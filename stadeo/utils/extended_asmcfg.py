# -*- encoding: utf8 -*-
#
# Copyright (c) 2020 ESET spol. s r.o.
# Author: Vladislav Hrčka <vladislav.hrcka@eset.com>
# See LICENSE file for redistribution.

from binascii import hexlify

from miasm.analysis.binary import Container
from miasm.analysis.depgraph import *
from miasm.analysis.disasm_cb import get_ira
from miasm.analysis.machine import Machine
from miasm.arch.x86.arch import instruction_x86, additional_info, mn_x86, conditional_branch, unconditional_branch
from miasm.core.asmblock import AsmBlock, AsmConstraint, AsmConstraintNext, AsmConstraintTo, bbl_simplifier, \
    asm_resolve_final, AsmCFG
from miasm.core.bin_stream import bin_stream_pe
from miasm.core.utils import pck32, pck64, upck64, upck32
from miasm.expression.expression import *
from miasm.ir.ir import IRBlock, IntermediateRepresentation, IRCFG
from miasm.ir.symbexec import SymbolicExecutionEngine
from miasm.loader import pe_init
from miasm.core.interval import interval
from pprint import pformat
import logging

logger = logging.getLogger('ExtendedAsmCFG')
logger.setLevel(logging.WARNING)


def is_bad_expr(expr):
    return expr.is_id() and expr.name in ["RIP", "EIP", "zf", "nf", "pf", "of", "cf", "af", "df", "IRDst"]


def custom_get(self, loc_key, elements, line_nb, heads):
    """Compute the dependencies of @elements at line number @line_nb in
    the block named @loc_key in the current IRCFG, before the execution of
    this line. Dependency check stop if one of @heads is reached
    @loc_key: LocKey instance
    @element: set of Expr instances
    @line_nb: int
    @heads: set of LocKey instances
    Return an iterator on DiGraph(DependencyNode)
    """
    # Init the algorithm
    inputs = {element: set() for element in elements}
    initial_state = DependencyState(loc_key, inputs, line_nb)
    todo = {initial_state}
    done = set()
    dpResultcls = DependencyResultImplicit if self._implicit else DependencyResult

    while todo:
        state = todo.pop()
        self._compute_intrablock(state)
        done_state = state.get_done_state()
        if done_state in done:
            continue
        done.add(done_state)
        if state.loc_key in heads or not state.pending:
            yield dpResultcls(self._ircfg, initial_state, state, elements)
            continue

        if self._implicit:
            # Force IRDst to be tracked, except in the input block
            state.pending[self._ircfg.IRDst] = set()

        # Propagate state to parents
        for pred in self._ircfg.predecessors_iter(state.loc_key):
            todo.add(state.extend(pred))


def custom_get_range(self):
    """Returns the offset hull of an AsmBlock"""
    try:
        rng = (self.lines[0].offset,
               self.lines[-1].offset + self.lines[-1].l)
        if None in rng:
            rng = 0, 0
    except (IndexError, TypeError):
        rng = 0, 0
    return rng


# support for premature termination of tracking depending on heads
DependencyGraph.get = custom_get
AsmBlock.get_range = custom_get_range


def custom_break_flow(self):
    if self.name in conditional_branch + unconditional_branch:
        return True
    if self.name.startswith('LOOP'):
        return True
    if self.name.startswith('RET'):
        return True
    if self.name.startswith('INT'):
        return True
    if self.name.startswith('SYS'):
        return True
    if self.name.startswith('CMOV'):
        return True
    if self.name.startswith('SBB'):
        return True
    return self.name in ['CALL', 'HLT', 'IRET', 'IRETD', 'IRETQ', 'ICEBP', 'UD2']


def custom_split_flow(self):
    if self.name in conditional_branch:
        return True
    if self.name in unconditional_branch:
        return False
    if self.name.startswith('LOOP'):
        return True
    if self.name.startswith('INT'):
        return True
    if self.name.startswith('SYS'):
        return True
    if self.name.startswith('CMOV'):
        return True
    if self.name.startswith('SBB'):
        return True
    if self.name in ['CALL']:
        return True
    return False


instruction_x86.breakflow = custom_break_flow
instruction_x86.splitflow = custom_split_flow


def custom_get_next_loc_key(self, instr):
    if not instr.offset or not instr.l and self.asm_block.lines[-1] == instr:
        return [i for i in self.asm_block.bto if i.c_t == "c_next"][0].loc_key
    loc_key = self.loc_db.get_or_create_offset_location(instr.offset + instr.l)
    self.split_offset = instr.offset + instr.l
    return loc_key


def custom_new_ircfg_from_asmcfg(self, asmcfg, *args, **kwargs):
    """
    Return a new instance of IRCFG from an @asmcfg
    @asmcfg: AsmCFG instance
    """

    ircfg = IRCFG(self.IRDst, self.loc_db, *args, **kwargs)
    self.new_blocks = []
    for block in asmcfg.blocks:
        self.add_asmblock_to_ircfg(block, ircfg, False, asmcfg)
    while self.new_blocks:
        block = self.new_blocks.pop()
        asmcfg.add_block(block)
        asmcfg.rebuild_edges()
        self.add_asmblock_to_ircfg(block, ircfg, False, asmcfg)
    return ircfg


def custom_add_asmblock_to_ircfg(self, block, ircfg, gen_pc_updt=False, asmcfg=None):
    """
    Add a native block to the current IR
    @block: native assembly block
    @ircfg: IRCFG instance
    @gen_pc_updt: insert PC update effects between instructions
    """

    loc_key = block.loc_key
    ir_blocks_all = []

    assignments = []
    self.asm_block = block
    for instr in block.lines:
        if loc_key is None:
            assignments = []
            loc_key = self.get_loc_key_for_instr(instr)
        split = self.add_instr_to_current_state(
            instr, block, assignments,
            ir_blocks_all, gen_pc_updt
        )
        if split:
            ir_blocks_all.append(IRBlock(loc_key, assignments))
            loc_key = None
            if len(assignments) != len(block.lines) and asmcfg:
                new_block = block.split(asmcfg.loc_db, self.split_offset)
                self.new_blocks.append(new_block)
                break
            assignments = []
    if loc_key is not None:
        ir_blocks_all.append(IRBlock(loc_key, assignments))

    new_ir_blocks_all = self.post_add_asmblock_to_ircfg(block, ircfg, ir_blocks_all)
    for irblock in new_ir_blocks_all:
        ircfg.add_irblock(irblock)
    return new_ir_blocks_all


# support for manually added assembly without offset and size
IntermediateRepresentation.add_asmblock_to_ircfg = custom_add_asmblock_to_ircfg
IntermediateRepresentation.get_next_loc_key = custom_get_next_loc_key
IntermediateRepresentation.new_ircfg_from_asmcfg = custom_new_ircfg_from_asmcfg


def create_jump_instruction(mode, target):
    """
    :param mode: 32 or 64, depends on architecture
    :param target: Expr to jump to
    :return: created instruction
    """
    tmp_ln = instruction_x86("JMP", mode, [target])
    tmp_ln.additional_info = additional_info()
    tmp_ln.additional_info.g1.value = 0
    return tmp_ln


def create_mov_instruction(mode, dst, src):
    tmp_ln = instruction_x86("MOV", mode, [dst, src])
    tmp_ln.additional_info = additional_info()
    tmp_ln.additional_info.g1.value = 0
    return tmp_ln


def create_cond_branch_instruction(mode, name, target):
    tmp_ln = instruction_x86(name, mode, [target])
    tmp_ln.additional_info = additional_info()
    tmp_ln.additional_info.g1.value = 0
    return tmp_ln


def create_cmp_j_instructions(mode, expr, val, target, kind):
    cmp_inst = instruction_x86("CMP", mode, [expr, val])
    cmp_inst.additional_info = additional_info()
    cmp_inst.additional_info.g1.value = 0

    jz_inst = instruction_x86(kind, mode, [target])
    jz_inst.additional_info = additional_info()
    jz_inst.additional_info.g1.value = 0
    return [cmp_inst, jz_inst]


def create_nop(mode):
    nop_inst = instruction_x86("NOP", mode, [])
    nop_inst.additional_info = additional_info()
    nop_inst.additional_info.g1.value = 0
    return nop_inst


def remove_redundant_and_unpin_blocks(asmcfg, head, mode, unpin=True):
    """
    To unpin a block means to unset associated address. New one can be calculated then.
    :return:
    """
    reachable_loc_keys = list(asmcfg.reachable_sons(head))
    blocks_to_be_removed = []
    rip = ExprId("RIP", 64)
    new_next_addr_card = ExprLoc(asmcfg.loc_db.get_or_create_name_location('_'), 64)
    for block in asmcfg.blocks:
        if block.loc_key not in reachable_loc_keys:
            blocks_to_be_removed.append(block)
        elif unpin:
            for instr in block.lines:
                for ind in range(len(instr.args)):
                    if rip in instr.args[ind]:
                        next_addr = ExprInt(instr.offset + instr.l, 64)
                        fix_dict = {rip: rip + next_addr - new_next_addr_card}
                        instr.args[ind] = instr.args[ind].replace_expr(fix_dict)

        if not block.lines:
            block.lines = [create_nop(mode)]
        if unpin and asmcfg.loc_db.get_location_offset(block.loc_key):
            asmcfg.loc_db.unset_location_offset(block.loc_key)

    for block in blocks_to_be_removed:
        asmcfg.del_block(block)


def fix_multiple_next_constraints(asmcfg, mode):
    """
    When there are multiple blocks proceeding another block with no jump, add one.
    :return:
    """
    blocks_to_be_added = []
    for loc_key in asmcfg.nodes():
        next_edges = {edge: constraint for edge, constraint in asmcfg.edges2constraint.items() if
                      constraint == AsmConstraint.c_next}
        pred_next = list(ploc_key for (ploc_key, dloc_key) in next_edges if dloc_key == loc_key)
        if len(pred_next) > 1:
            for index in range(1, len(pred_next)):
                inst = create_jump_instruction(mode, ExprLoc(loc_key, mode))

                new_block_loc_key = asmcfg.loc_db.add_location()
                new_block = AsmBlock(new_block_loc_key)
                new_block.addline(inst)
                new_block.bto = {AsmConstraintTo(loc_key)}

                asmcfg.loc_key_to_block(pred_next[index]).bto = {AsmConstraintNext(new_block_loc_key)}
                blocks_to_be_added.append(new_block)
    # one while might be sufficient, depends on type of _nodes
    for block in blocks_to_be_added:
        asmcfg.add_block(block)


def write_patches_to_file(asmcfg, exectbl, out_addr, out_file_name, mode, max_addr=2 ** 64 - 1, head=None):
    if head is None:
        head = asmcfg.heads()[0]

    asmcfg = bbl_simplifier.apply_simp(asmcfg)
    asmcfg.rebuild_edges()
    remove_redundant_and_unpin_blocks(asmcfg, head, mode)
    fix_multiple_next_constraints(asmcfg, mode)
    # careless block reordering might have damaged edges of the graph and introduced dead blocks
    asmcfg.rebuild_edges()

    asmcfg.loc_db.set_location_offset(head, out_addr)
    patches = asm_resolve_final(mn_x86, asmcfg, asmcfg.loc_db, dst_interval=interval([(out_addr, max_addr)]))

    last_empty_address = 0
    for offset, raw in patches.items():
        logger.debug(
            "patch addr rva is 0x%x; raw is 0x%x; the patch: %s" % (exectbl.virt2rva(offset), offset, raw.hex()))
        exectbl.img_rva[exectbl.virt2rva(offset)] = raw
        next_empty_address = offset + len(raw)
        if last_empty_address < next_empty_address:
            last_empty_address = next_empty_address

    with open(out_file_name + ".bak", 'wb') as bak:
        with open(out_file_name, 'rb') as fl:
            bak.write(fl.read())
    with open(out_file_name, 'wb') as fl:
        fl.write(bytes(exectbl))
    return last_empty_address


class MySymbolicExecutionEngine(SymbolicExecutionEngine):
    def __init__(self, pool_bin, jtc_var, *args, **kwargs):
        super(MySymbolicExecutionEngine, self).__init__(*args, **kwargs)
        self.pool_bin = pool_bin
        self.jtc_var = jtc_var

    def mem_read(self, expr_mem):
        """Memory read wrapper for symbolic execution
        @expr_mem: ExprMem"""
        if not expr_mem.ptr.is_int() or self.jtc_var == expr_mem:
            return super(MySymbolicExecutionEngine, self).mem_read(expr_mem)
        addr = expr_mem.ptr.arg.arg
        size = expr_mem.size // 8
        value = self.pool_bin.getbytes(addr, size)
        final = ExprInt(int(hexlify(value[::-1]), 16), expr_mem.size)
        return final


class JTCVariableDependencyGraph(DependencyGraph):
    def __init__(self, loc_key, *args, **kwargs):
        super(JTCVariableDependencyGraph, self).__init__(*args, **kwargs)
        self.jtc_var = None
        self.done = False
        self.loc_key = loc_key

    def _track_exprs(self, state, assignblk, line_nb):
        """Track pending expression in an assignblock"""
        if self.done:
            return
        future_pending = {}
        node_resolved = set()
        for dst, src in assignblk.items():
            # Only track pending
            if dst not in state.pending:
                continue
            # Track IRDst in implicit mode only
            if dst == self._ircfg.IRDst and not self._implicit:
                continue
            assert dst not in node_resolved
            node_resolved.add(dst)
            dependencies = self._follow_apply_cb(src)

            state.link_element(dst, line_nb)
            state.link_dependencies(dst, line_nb,
                                    dependencies, future_pending)

        # Update pending nodes
        if not self.jtc_var and state.loc_key == self.loc_key:
            for expr in future_pending:
                if expr.is_mem() or (expr.is_id() and
                                     expr.name not in ["RIP", "EIP", "zf", "nf", "pf", "of", "cf", "af", "df",
                                                       self._ircfg.IRDst.name]):
                    self.jtc_var = expr
                    state.pending = {}
                    # break
                    return

        state.remove_pendings(node_resolved)
        state.add_pendings(future_pending)


class ExtendedAsmCFG(AsmCFG):
    def __init__(self, file_name, conn=None, cont=None, exectbl=None, *args, **kwargs):
        super(ExtendedAsmCFG, self).__init__(loc_db=LocationDB(), *args, **kwargs)
        self.file_name = file_name
        if not cont:
            if conn:
                stream = conn.builtins.open(file_name, 'rb')
            else:
                stream = open(file_name, 'rb')
            cont = Container.from_stream(stream)
        self.cont = cont
        self.mode = int(cont.arch[-2:])
        self.address_size = self.mode // 8
        self.pck = pck32
        self.upck = upck32
        self.machine = Machine(cont.arch)
        self.disassembler = self.machine.dis_engine
        if self.mode == 64:
            self.pck = pck64
            self.upck = upck64
        self._exectbl = exectbl
        if not exectbl:
            self._exectbl = pe_init.PE(cont.executable)
        self._dis_engine = None
        self.func_addr = None
        self.jmp_table_loc_keys = set()

    def _process_cmov(self, cur_bloc, last_instruction):
        assignment_block = AsmBlock(self.loc_db.add_location())
        cond_block = AsmBlock(self.loc_db.add_location())
        dst = last_instruction.args[0]
        src = last_instruction.args[1]
        assignment_block.lines.append(create_mov_instruction(self.mode, dst, src))
        branch_target = next(iter(cur_bloc.bto)).loc_key
        assignment_block.lines.append(create_jump_instruction(self.mode, ExprLoc(branch_target, self.mode)))
        branch_name = "J" + last_instruction.name[len("CMOV"):]
        cur_bloc.lines.pop()
        if not cur_bloc.lines:
            cur_bloc.lines = [create_nop(self.mode)]
        cond_block.lines.append(create_cond_branch_instruction(self.mode, branch_name,
                                                               ExprLoc(assignment_block.loc_key, self.mode)))
        assignment_block.bto = {AsmConstraintTo(branch_target)}
        cond_block.bto = {AsmConstraintNext(branch_target), AsmConstraintTo(assignment_block.loc_key)}
        cur_bloc.bto = {AsmConstraintNext(cond_block.loc_key)}
        self.add_block(assignment_block)
        self.add_block(cond_block)

    def _process_sbb(self, cur_bloc, last_instruction):
        assignment_block = AsmBlock(self.loc_db.add_location())
        cond_block = AsmBlock(self.loc_db.add_location())
        reg = last_instruction.args[0]
        assignment_block.lines.append(create_mov_instruction(self.mode, reg, ExprInt(-1, reg.size)))
        branch_target = next(iter(cur_bloc.bto)).loc_key
        assignment_block.lines.append(create_jump_instruction(self.mode, ExprLoc(branch_target, self.mode)))
        branch_name = "JB"  # JC is not implemented in miasm, using alias
        cur_bloc.lines.pop()
        pre_branch_block = AsmBlock(self.loc_db.add_location())
        pre_branch_block.lines = [create_mov_instruction(self.mode, reg, ExprInt(0, reg.size))]
        cond_block.lines.append(create_cond_branch_instruction(self.mode, branch_name,
                                                               ExprLoc(assignment_block.loc_key, self.mode)))
        if not cur_bloc.lines:
            cur_bloc.lines = [create_nop(self.mode)]
        assignment_block.bto = {AsmConstraintTo(branch_target)}
        cur_bloc.bto = {AsmConstraintNext(cond_block.loc_key)}
        cond_block.bto = {AsmConstraintNext(pre_branch_block.loc_key), AsmConstraintTo(assignment_block.loc_key)}
        pre_branch_block.bto = {AsmConstraintNext(branch_target)}
        self.add_block(assignment_block)
        self.add_block(cond_block)
        self.add_block(pre_branch_block)

    def _process_adc(self, cur_bloc, last_instruction):
        assignment_block = AsmBlock(self.loc_db.add_location())
        reg = last_instruction.args[0]
        assignment_block.lines.append(create_mov_instruction(self.mode, reg, ExprInt(-1, reg.size)))
        branch_target = next(iter(cur_bloc.bto)).loc_key
        assignment_block.lines.append(create_jump_instruction(self.mode, ExprLoc(branch_target, self.mode)))
        branch_name = "JB"  # JC is not implemented in miasm, using alias
        cur_bloc.lines.pop()
        cur_bloc.lines.append(create_mov_instruction(self.mode, reg, ExprInt(0, reg.size)))
        cur_bloc.lines.append(create_cond_branch_instruction(self.mode, branch_name,
                                                             ExprLoc(assignment_block.loc_key, self.mode)))
        self.add_block(assignment_block)
        assignment_block.bto = {AsmConstraintTo(branch_target)}
        cur_bloc.bto.add(AsmConstraintTo(assignment_block.loc_key))

    @staticmethod
    def _eliminate_jtc_var_slice_cb(expr, sizes, target):
        if expr.is_compose():
            if expr.args[0].is_slice() and expr.args[0].arg.is_id() and expr.args[0].arg == target:
                size = expr.args[0].size
                sizes.add(size)
            if expr.args[0].is_id() and expr.args[0] == target:
                size = expr.size
                sizes.add(size)
        elif expr.is_slice() and expr.arg.is_id() and expr.arg == target:
            size = expr.size
            sizes.add(size)

    def _process_jmp_table(self, cur_bloc, mn, attrib, loc_db, pool_bin, offsets_to_dis):
        # TODO add support for jump tables with "AND cntrl_var, range" boundary check; such jmp tables were present only
        #   in library functions in Stantinko samples
        # add current block to the asmcfg to make it accessible in the ircfg edges, add_block is called anyway right
        # after this callback, it will notice that the block has been already added
        self.add_block(cur_bloc)
        dst_address = loc_db.get_location_offset(cur_bloc.loc_key)

        logger.info("Possible jump table addr: 0x%x" % dst_address)

        ira = get_ira(mn, attrib)

        ir_arch = ira(loc_db)

        ircfg = ir_arch.new_ircfg_from_asmcfg(self)

        # the previous blocks should have exactly 1 predecessor dictating range
        predecessors = self.predecessors(cur_bloc.loc_key)
        if len(predecessors) != 1:
            logger.info("Expected exactly one predecessor")
            return
        predecessor = ircfg.blocks[predecessors.pop()]

        irdst_block = ircfg.blocks[cur_bloc.loc_key]
        if len(irdst_block.assignblks) != len(cur_bloc.lines):
            processed = set()
            todo = {irdst_block.loc_key}
            while not irdst_block.dst.is_mem():
                loc_key = todo.pop()
                if loc_key in processed:
                    continue
                processed.add(loc_key)
                irdst_block = ircfg.blocks[loc_key]
                todo.update(ircfg.successors(loc_key))

        # we shouldn't stumble upon crashing segm and call operators even thought implicit is required to process
        # initial IRDst(mentioned operators cause crashes of the engine behind implicit) since we operate only on the
        # 2 crucial basic blocks. The predecessor contains range of the jump table, we use it to determine constructs
        # of the jump table and track back base code segment address assignment to target the msvc compiler and x64
        # architecture, other compilers use directly RIP related addressing to get the address.

        # get real predecessor
        asm_block = self.loc_key_to_block(predecessor.loc_key)
        if len(predecessor.assignblks) != len(asm_block.lines):
            processed = set()
            todo = {predecessor.loc_key}
            while cur_bloc.loc_key not in ircfg.successors(predecessor.loc_key):
                loc_key = todo.pop()
                if loc_key in processed:
                    continue
                processed.add(loc_key)
                predecessor = ircfg.blocks[loc_key]
                todo.update(ircfg.successors(loc_key))

        # get jump_table_control_variable from predecessor
        dg = DependencyGraph(ircfg, implicit=True, apply_simp=True, follow_mem=True, follow_call=False)
        jtcdg = JTCVariableDependencyGraph(predecessor.loc_key,
                                           ircfg, implicit=True, apply_simp=True, follow_mem=False, follow_call=False)

        dependency_result_iter = iter(jtcdg.get(irdst_block.loc_key, {ircfg.IRDst}, len(predecessor.assignblks),
                                                {predecessor.loc_key}))
        solution_predecessor = next(dependency_result_iter)
        # jump table control variable
        jtc_var = jtcdg.jtc_var
        if not jtc_var:
            logger.info("couldn't determine single jump table control variable")
            return
        # get symbolic execution engine to be used in both predecessor and jmp table block
        symb_exec_both = MySymbolicExecutionEngine(pool_bin, jtc_var, ir_arch)
        try:
            # symbolically evaluate lines influencing IRDst of the predecessor leading to jtc_var
            for line_nb in sorted({node.line_nb for node in solution_predecessor.relevant_nodes
                                   if node.loc_key == predecessor.loc_key}):
                assign_blk = predecessor.assignblks[line_nb]
                symb_exec_both.eval_updt_assignblk(assign_blk)
        except (KeyError, TypeError):
            logger.error(
                "Couldn't symbolically eval predecessor of 0x%x" % loc_db.get_location_offset(cur_bloc.loc_key))
            # stantinko contains illegal unreachable dereferences prior jmp tables, such as
            # xor     eax, eax; movsx   eax, byte ptr [eax]
            return
        # get symbolic execution engine supporting binary memory dereference
        symb_exec_minimal = MySymbolicExecutionEngine(pool_bin, ir_arch, symb_exec_both.symbols.copy())
        predecessor_irdst_equation = symb_exec_both.symbols[ircfg.IRDst]

        # get equation whose solutions solve the indirect jump
        irdst_block = ircfg.blocks[cur_bloc.loc_key]
        if len(irdst_block.assignblks) != len(cur_bloc.lines):
            processed = set()
            todo = {irdst_block.loc_key}
            while not irdst_block.dst.is_mem():
                symb_exec_both.eval_updt_irblock(irdst_block)
                loc_key = todo.pop()
                if loc_key in processed:
                    continue
                processed.add(loc_key)
                irdst_block = ircfg.blocks[loc_key]
                todo.update(ircfg.successors(loc_key))

        irdst_equation = symb_exec_both.eval_updt_irblock(irdst_block)
        sizes = set()
        # prevent mem processing via raw arrays by using var ID instead
        # we also want to set a maximum boundary so slices don't cause the sat solver generate a huge number of results
        visitor = ExprVisitorCallbackTopToBottom(lambda x: self._eliminate_jtc_var_slice_cb(x, sizes, jtc_var))
        irdst_equation = visitor.visit(irdst_equation)
        predecessor_irdst_equation = visitor.visit(predecessor_irdst_equation)
        size_boundary = jtc_var.size
        sizes = sorted(filter(lambda x: x > 1, sizes))
        if sizes:
            size_boundary = sizes[0]
        jtc_var_id = ExprId("jtc_var", jtc_var.size)
        irdst_equation = irdst_equation.replace_expr({jtc_var: jtc_var_id})
        predecessor_irdst_equation = predecessor_irdst_equation.replace_expr({jtc_var: jtc_var_id})
        # track possible CS base address dependency, ignore control variable from predecessor
        eliminated_jtc_var_equation = irdst_equation.replace_expr({jtc_var_id: ExprInt(0, jtc_var_id.size)})
        evaluated_ejtc_var_equation = symb_exec_both.eval_expr(eliminated_jtc_var_equation)
        if not evaluated_ejtc_var_equation.is_int():
            # we need to determine code base
            dependencies = dg._follow_apply_cb(evaluated_ejtc_var_equation)
            expr_deps = {fexpr.element for fexpr in dependencies if fexpr.follow}
            dg_base = DependencyGraph(ircfg, implicit=False, apply_simp=True, follow_mem=True, follow_call=False)
            dependency_result_iter = iter(dg_base.get(cur_bloc.loc_key, expr_deps, len(cur_bloc.lines),
                                                      {self.heads()[0]}))
            solution = next(dependency_result_iter)
            code_base_dict = {expr: solution.emul(ir_arch)[expr] for expr in expr_deps}
            irdst_equation = irdst_equation.replace_expr(code_base_dict)
            predecessor_irdst_equation = predecessor_irdst_equation.replace_expr(code_base_dict)

        # we need backward slice of the jump table destination dependencies to retain the other independent assignments
        # during cmp chain assembling
        dependency_result = dg.get(cur_bloc.loc_key, {ircfg.IRDst}, len(cur_bloc.lines), {cur_bloc.loc_key})
        dependent_line_nbs = {}
        for solution in dependency_result:
            dependent_line_nbs.setdefault(solution.loc_key, set()).update(
                {dn.line_nb for dn in solution.relevant_nodes})
        cur_bloc_new_lines = []
        for loc_key, lines in dependent_line_nbs.items():
            for line_nb, assignblk in enumerate(ircfg.blocks[loc_key].assignblks):
                if line_nb not in lines:
                    symb_exec_minimal.eval_assignblk(assignblk)
                    cur_bloc_new_lines.append(assignblk.instr)
        comparison_reg_id = None
        comparison_reg_value = None
        if jtc_var not in symb_exec_minimal.symbols.symbols_id:
            comparison_reg_id = jtc_var
            comparison_reg_value = jtc_var
        else:
            for symbol, comparison_reg_value in symb_exec_minimal.symbols.symbols_id.items():
                if jtc_var in comparison_reg_value and (symbol.is_mem() or
                                                        (symbol.is_id() and symbol.name not in
                                                         ["RIP", "EIP", "zf", "nf", "pf", "of", "cf", "af", "df",
                                                          ircfg.IRDst.name])):
                    replaced_jtcv = comparison_reg_value.replace_expr({jtc_var: ExprInt(0, jtc_var.size)})
                    if isinstance(symb_exec_minimal.eval_expr(replaced_jtcv), ExprInt):
                        comparison_reg_id = symbol
                        break
        if not comparison_reg_id or not comparison_reg_value:
            logger.debug("Couldn't find any candidate for comparison register at 0x%x" %
                         loc_db.get_location_offset(cur_bloc.loc_key))
            return

        from miasm.ir.translators import Translator
        import z3
        translator = Translator.to_language("z3")
        solver = z3.Solver()

        logger.debug("predecessor_irdst_equation: %s" % str(predecessor_irdst_equation))
        logger.debug(("dst_address: 0x%x" % dst_address))
        logger.debug(("jump_table_control_variable: %s" % str(jtc_var)))
        solver.add(translator.from_expr(predecessor_irdst_equation) == dst_address)
        translated_jtc_var = translator.from_expr(jtc_var_id)
        solver.add(translated_jtc_var >= 0)
        solver.add(translated_jtc_var < 2 ** (size_boundary - 1) - 1)

        if solver.check() != z3.sat:
            logger.debug("Couldn't find at least one jump table control variable")
            return

        dbg_destinations = set()
        next_loc_key = new_block_loc_key = loc_db.add_location()

        logger.debug("comparison_reg_id: %s" % str(comparison_reg_id))
        dst_ranges = {}
        counter = 0
        while counter < 500:
            val = solver.model()[translated_jtc_var].as_long()
            final_irdst_equation = irdst_equation.replace_expr({jtc_var_id: ExprInt(val, jtc_var_id.size)})
            final_dst = int(symb_exec_both.eval_expr(final_irdst_equation))
            cmp_reg_val = comparison_reg_value.replace_expr({jtc_var: ExprInt(val, jtc_var.size)})
            cmp_reg_val = int(symb_exec_minimal.eval_expr(cmp_reg_val))

            dst_ranges[final_dst] = dst_ranges.get(final_dst, interval()).union([(cmp_reg_val, cmp_reg_val)])
            dbg_destinations.add(final_dst)
            offsets_to_dis.add(final_dst)

            solver.add(translated_jtc_var != translator.from_expr(ExprInt(val, jtc_var_id.size)))
            if solver.check() != z3.sat:
                break
            counter += 1

        if counter == 500:
            raise RuntimeError("Interrupted; there might be a broken slice")

        for dst, interv in dst_ranges.items():
            cond_target_loc_key = loc_db.get_or_create_offset_location(dst)
            for lower, upper in interv:
                lower = ExprInt(lower, self.mode)
                upper = ExprInt(upper, self.mode)
                new_asm_block = AsmBlock(new_block_loc_key)
                new_block_loc_key = loc_db.add_location()
                if lower == upper:
                    new_asm_block.lines = create_cmp_j_instructions(self.mode, comparison_reg_id, lower,
                                                                    ExprLoc(cond_target_loc_key, self.mode), "JZ")
                    new_asm_block.add_cst(cond_target_loc_key, "c_to")
                    new_asm_block.add_cst(new_block_loc_key, "c_next")
                else:
                    upper_check_loc_key = loc_db.add_location()
                    # lower boundary check
                    new_asm_block.lines = create_cmp_j_instructions(self.mode, comparison_reg_id, lower,
                                                                    ExprLoc(new_block_loc_key, self.mode), "JB")
                    new_asm_block.add_cst(new_block_loc_key, "c_to")
                    new_asm_block.add_cst(upper_check_loc_key, "c_next")
                    # upper boundary check
                    upper_check_block = AsmBlock(upper_check_loc_key)
                    upper_check_block.lines = create_cmp_j_instructions(self.mode, comparison_reg_id, upper,
                                                                        ExprLoc(cond_target_loc_key, self.mode), "JBE")
                    upper_check_block.add_cst(cond_target_loc_key, "c_to")
                    upper_check_block.add_cst(new_block_loc_key, "c_next")
                    self.add_block(upper_check_block)
                self.add_block(new_asm_block)
        # trigger last jump unconditionally
        new_asm_block.bto = {AsmConstraintTo(cond_target_loc_key)}
        new_asm_block.lines = [create_jump_instruction(self.mode, ExprLoc(cond_target_loc_key, self.mode))]

        cur_bloc.lines = cur_bloc_new_lines
        cur_bloc.add_cst(next_loc_key, "c_next")
        if not cur_bloc.lines:
            cur_bloc.lines = [create_nop(self.mode)]
        self.jmp_table_loc_keys.add(cur_bloc.loc_key)
        logger.debug("destinations: %s" % pformat([hex(i or 0) for i in dbg_destinations]))
        logger.debug("blocks: %d" % counter)

    # noinspection PyUnusedLocal
    def _extended_discovery(self, dism_eng, cur_bloc, offsets_to_dis):
        mn = self.machine.mn
        attrib = self.mode
        pool_bin = dism_eng.bin_stream
        loc_db = dism_eng.loc_db
        if not cur_bloc.lines:
            return
        last_instruction = cur_bloc.lines[-1]
        if last_instruction.name.startswith("CMOV"):
            self._process_cmov(cur_bloc, last_instruction)
        elif last_instruction.name.startswith("SBB") and last_instruction.args[0] == last_instruction.args[1]:
            self._process_sbb(cur_bloc, last_instruction)
        elif last_instruction.name == 'JMP' and type(last_instruction.args[0]) in [ExprMem, ExprId]:
            self._process_jmp_table(cur_bloc, mn, attrib, loc_db, pool_bin, offsets_to_dis)
        elif last_instruction.name.startswith("INT"):
            offsets_to_dis = set()
        elif last_instruction.name == 'JMP' and last_instruction.args[0].is_loc(cur_bloc.loc_key) \
                and len(cur_bloc.lines) == 1:
            # prevent Miasm eb fe bug https://github.com/cea-sec/miasm/issues/1257
            cur_bloc.lines.insert(0, create_nop(self.mode))

    def disassemble(self, function_address, conn=None):
        unreachable = []
        if conn:
            ea = conn.modules.idaapi.get_func(function_address)
            try:
                unreachable = [i.end_ea for i in ea.tails] + [ea.end_ea]
            except AttributeError:
                pass
        self.func_addr = function_address
        self.jmp_table_loc_keys = set()
        binary_stream = bin_stream_pe(self._exectbl)
        self._dis_engine = self.disassembler(binary_stream, loc_db=self.loc_db, dont_dis=unreachable)
        self._dis_engine.dis_block_callback = self._extended_discovery
        self._dis_engine.dis_multiblock(function_address, self)

    @property
    def exectbl(self):
        return self._exectbl
