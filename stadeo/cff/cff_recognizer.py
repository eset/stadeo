# -*- encoding: utf8 -*-
#
# Copyright (c) 2020 ESET spol. s r.o.
# Author: Vladislav Hrčka <vladislav.hrcka@eset.com>
# See LICENSE file for redistribution.

from collections import namedtuple
from hashlib import md5
from miasm.analysis.data_flow import ReachingDefinitions, DiGraphDefUse, AssignblkNode
import miasm.analysis.depgraph as depgraph
from miasm.arch.x86 import regs
from miasm.arch.x86.arch import expr_simp
from miasm.core.locationdb import LocationDB
from miasm.expression.expression import *
from miasm.ir.ir import AssignBlock, IRBlock
import logging

from miasm.ir.symbexec import SymbolicExecutionEngine
from sortedcontainers import SortedSet

from stadeo.cff.arcg_cache_depgraph import ArgCacheDependencyGraph, contains_local_variable
from stadeo.utils.extended_asmcfg import ExtendedAsmCFG, is_bad_expr, remove_redundant_and_unpin_blocks

logger = logging.getLogger('CFFrecognizer')
logger.setLevel(logging.WARNING)


# logger.basicConfig(stream=sys.stderr, level=logger.DEBUG)
# logger.basicConfig(filename="solver.log", level=logger.DEBUG)


class FlatteningLoop(object):
    def __init__(self, head_vars: list, primary_loc_keys: set, affected_lines: dict, affected_exprs: dict
                 , loc_key: LocKey):
        # TODO replace loc_key with seq IDs
        self.affected_exprs = affected_exprs
        self.loc_key = loc_key
        self.head_vars = head_vars
        self.affected_lines = affected_lines
        self.primary_loc_keys = primary_loc_keys
        self.is_default = False
        self._seq = 0

    def get_affected_hash(self, symb_exec, block_loc_key, flat_loop, source_hash_value):
        hash_list = [block_loc_key, source_hash_value]
        for head_var in self.head_vars:
            hash_list.append((head_var, symb_exec.eval_expr(head_var)))
        for affected_expr in flat_loop.affected_exprs[block_loc_key]:
            hash_list.append((affected_expr, symb_exec.eval_expr(affected_expr)))
        seq = False
        if not flat_loop.affected_exprs[block_loc_key]:
            hash_list.append(self._seq)
            self._seq += 1
            seq = True
        new_hash = int(md5(bytes(str(hash_list), 'ascii')).hexdigest(), 16)
        return new_hash, seq


class FlatteningLoops(object):
    def __init__(self):
        self._loc_key_to_loop = {}
        self.loc_db = LocationDB()
        self.loops = []
        # for blocks outside of any loop
        self._outside_of_scope = FlatteningLoop([], set(), {}, {}, self.loc_db.add_location())
        self._outside_of_scope.is_default = True
        self._address = None

    def get_block(self, block_loc_key, symb_exec, source_flat_block=None):
        flat_loop = self[block_loc_key]
        flat_hash = source_hash_value = source_loop_loc_key = None
        if flat_loop.is_default:
            if source_flat_block:
                source_loop_loc_key = source_flat_block.source_loop_loc_key or source_flat_block.block_loc_key
                source_flat_loop = self[source_loop_loc_key]
                source_hash_value = source_flat_block.source_hash_value or source_flat_block.control_hash_value
                if block_loc_key in source_flat_loop.affected_lines:
                    flat_hash, no_affected_expr = \
                        flat_loop.get_affected_hash(symb_exec, block_loc_key, source_flat_loop, None)
                    source_hash_value = None
        else:
            flat_hash, _ = flat_loop.get_affected_hash(symb_exec, block_loc_key, flat_loop, None)
        # TODO check init block too to prevent initial duplicity in case of loops(eliminated by the decompiler)
        flat_block = FlatteningBlock(flat_loop.loc_key, source_loop_loc_key, block_loc_key, flat_hash,
                                     source_hash_value)
        return flat_block

    def create(self, head_vars, affected_lines, primary_loc_keys, ircfg, address):
        self._address = hex(address) if address else "None"
        affected_exprs = {}
        dp = depgraph.DependencyGraph(ircfg, True)
        for block_loc_key in affected_lines:
            block = ircfg.blocks[block_loc_key]
            cur_affected_exprs = SortedSet(key=lambda x: str(x))
            for line_nb in affected_lines[block_loc_key]:
                affected_assignments = block.assignblks[line_nb]
                for ind, (dst, src) in enumerate(affected_assignments.items()):
                    if type(src) not in [ExprInt, ExprMem]:
                        res = next(dp.get(block_loc_key, {dst}, ind, {block_loc_key}))
                        cur_affected_exprs.update(filter(lambda x: not is_bad_expr(x), res.pending.keys()))
            affected_exprs[block_loc_key] = cur_affected_exprs
        loop = FlatteningLoop(list(head_vars), primary_loc_keys, affected_lines, affected_exprs,
                              self.loc_db.add_location())
        upd = {}
        for i in loop.primary_loc_keys:
            if i in self._loc_key_to_loop:
                raise RuntimeError("Overlap of primary blocks of the flattening loops")
            upd[i] = loop
        self._loc_key_to_loop.update(upd)
        self.loops.append(loop)
        return loop

    def __getitem__(self, loc_key):
        """
        Retrieves particular flattening loop by ID of the block
        :param loc_key:
        :return:
        """
        return self._loc_key_to_loop.get(loc_key, self._outside_of_scope)

    def __contains__(self, loc_key):
        return loc_key in self._loc_key_to_loop

    def __len__(self):
        return len(self.loops)


FlattenState = namedtuple('FlattenState', 'flat_block, symbols')


class ConfirmedMergeFunc(object):
    def __init__(self, recognizer, vals):
        self.recognizer = recognizer
        self.vals = vals


class FlatteningBlock(object):
    """
    We don't need any what flattening loop the block belongs to since they are all disjunct.
    """

    def __init__(self, loop_loc_key: LocKey, source_loop_loc_key: LocKey, block_loc_key: LocKey, control_hash_value,
                 source_hash_value):
        self.block_loc_key = block_loc_key
        self.control_hash_value = control_hash_value
        self.loop_loc_key = loop_loc_key
        self.source_hash_value = source_hash_value
        self.source_loop_loc_key = source_loop_loc_key

    def __hash__(self):
        hash_list = [self.loop_loc_key, self.block_loc_key, self.control_hash_value, self.source_hash_value]
        new_hash = int(md5(bytes(str(hash_list), "ascii")).hexdigest(), 16)
        return new_hash

    def __eq__(self, other):
        return self.loop_loc_key == other.loop_loc_key and \
               self.block_loc_key == other.block_loc_key and \
               self.control_hash_value == other.control_hash_value and \
               self.source_hash_value == other.source_hash_value


class Analyses(object):
    def __init__(self, ircfg, asmcfg):
        self.defuse_edges = {}
        self.reaching_defs = ReachingDefinitions(ircfg)
        defuse = DiGraphDefUse(self.reaching_defs, deref_mem=False, apply_simp=True)
        heads = asmcfg.heads()
        self.dominators = asmcfg.compute_dominators(heads[0])
        self.immediate_dominators = asmcfg.compute_immediate_dominators(heads[0])

        self.back_edges = []
        self.rev_back_edges = {}
        for node in asmcfg.walk_depth_first_forward(heads[0]):
            for successor in asmcfg.successors_iter(node):
                # check for a back edge to a dominator
                if successor in self.dominators[node]:
                    edge = (node, successor)
                    self.rev_back_edges.setdefault(successor, set()).add(node)
                    self.back_edges.append(edge)

        for src, dst in defuse.edges():
            self.defuse_edges.setdefault(src, []).append(dst)


class CFFRecognizer(object):
    def __init__(self, file_path, func_address, machine, conn):
        self.ir_arch = None
        self.func_address = func_address
        self.asmcfg = None
        self.file_path = file_path
        self.all_affected_lines = {}
        self.flat_loops = FlatteningLoops()
        self.machine = machine
        self.mn = machine.mn
        self._merging_var_candidates = None
        self.merging_var = None
        self.possible_merge_funcs = set()
        self.conn = conn
        self.func_addresses = set(conn.modules.idautils.Functions())
        self.ircfg = None
        self.pad = False
        self.analyses = None

    @staticmethod
    def _resize_top_expr(expr, size):
        cls, state = expr.__reduce__()
        if expr.is_slice():
            return ExprSlice(expr.arg, 0, size)
        elif isinstance(state[-1], int):
            # int must be since since all the other args are Expr instance
            return cls(*state[:-1], size)
        elif expr.is_op() and expr.op.startswith("zeroExt"):
            return ExprOp("zeroExt_" + str(size), *expr.args)
        return None

    def _normalize_ircfg(self, conn):
        # unalias stack miasm.re/blog/2017/02/03/data_flow_analysis_depgraph.html , but involve base pointer too
        # TODO remove manual *BP propagation in normalize_ircfg and use standrad Miasm propagation when it is fixed
        # remove composes from bigger to smaller, they are not important for us
        bp = {}
        prev_offset = None
        for irb_loc_key in self.ircfg.walk_breadth_first_forward(LocKey(0)):
            irs = []
            if irb_loc_key not in self.ircfg.blocks:
                continue
            irb = self.ircfg.blocks[irb_loc_key]
            if irb.dst.is_cond() and irb.dst.cond.is_op() and irb.dst.cond.op == 'CC_EQ':
                # TODO propagate cmp ..., arb_int too
                # propagate known zeroes to process test    eax, eax; jnz ...; lea     edi, [eax+4]
                symb_exec = SymbolicExecutionEngine(self.ir_arch)
                dst = symb_exec.eval_updt_irblock(irb)
                if dst.is_cond() and dst.cond.is_id():
                    # add explicit mov ID, 0 to given irb
                    target_loc = dst.src2
                    if target_loc.is_int():
                        target_loc = self.asmcfg.loc_db.get_offset_location(int(target_loc))
                    elif target_loc.is_loc():
                        target_loc = target_loc.loc_key
                    else:
                        continue
                    target_irb = self.ircfg.blocks[target_loc]
                    asign_blk = AssignBlock([ExprAssign(dst.cond, ExprInt(0, dst.cond.size))])
                    assignblks = tuple([asign_blk, *target_irb.assignblks])
                    new_irb = IRBlock(target_loc, assignblks)
                    self.ircfg.blocks[target_loc] = new_irb
            fix_dct = {}
            for assignblk in irb:
                offset = prev_offset
                if assignblk.instr and assignblk.instr.offset:
                    offset = assignblk.instr.offset
                prev_offset = offset
                spd = conn.modules.idc.get_spd(offset)
                if spd is not None:
                    stk_high = ExprInt(spd, self.ir_arch.sp.size)
                    fix_dct = {self.ir_arch.sp: self.mn.regs.regs_init[self.ir_arch.sp] + stk_high}
                    fix_dct.update(bp)
                else:
                    logger.warning("Couldn't acquire stack depth at 0x%x" % (offset or 0x0BADF00D))

                new_assignblk = {}
                for dst, src in assignblk.items():
                    if src.is_compose():
                        slc_arg = None
                        arg = None
                        for tmp_arg in src.args:
                            if not tmp_arg.is_slice():
                                arg = tmp_arg
                            else:
                                # we're interested only in bigger to smaller
                                slc_arg = tmp_arg
                        if slc_arg and arg and len(arg.get_r()) == 1:
                            top_to_bottom_visitor = ExprVisitorCallbackTopToBottom(
                                lambda x: self._resize_top_expr(x, src.size))
                            src = top_to_bottom_visitor.visit(arg)
                    if dst == src:
                        # special compiler anomalies such as lea     esp, [esp+0]
                        continue
                    if src == self.ir_arch.sp:
                        src = expr_simp(src.replace_expr(fix_dct))
                        if bp and src not in bp.values() and irb_loc_key != LocKey(0):
                            raise RuntimeError("Ambiguous base pointer")
                        bp.update({dst: src})
                        fix_dct.update(bp)
                    else:
                        src = expr_simp(src.replace_expr(fix_dct))
                        if dst != self.ir_arch.sp and dst not in bp.keys():
                            dst = dst.replace_expr(fix_dct)

                    dst, src = expr_simp(dst), expr_simp(src)
                    new_assignblk[dst] = src
                irs.append(AssignBlock(new_assignblk, instr=assignblk.instr))
            self.ircfg.blocks[irb.loc_key] = IRBlock(irb.loc_key, irs)

    def _recog_init(self, merging_var_candidates):
        # recognize cff loops and initiate deobfuscation
        self._merging_var_candidates = merging_var_candidates
        self.ircfg = self.ir_arch.new_ircfg_from_asmcfg(self.asmcfg)
        self.asmcfg.rebuild_edges()

        # TODO put constant propagation here when fixed in Miasm
        # simp = IRCFGSimplifierSSA(self.ir_arch)
        # from datetime import datetime
        # startTime = datetime.now()
        # ssa = simp.ircfg_to_ssa(self.ircfg, LocKey(0))
        # simp.do_propagate_expressions(ssa, LocKey(0))
        # self.ircfg = simp.ssa_to_unssa(ssa, LocKey(0))
        # print(datetime.now() - startTime)

        # init_infos = self.ir_arch.arch.regs.regs_init
        # cst_propag_link = cst_prop.propagate_cst_expr(self.ir_arch, self.ircfg, self.asmcfg.func_addr, init_infos)

        # raise Exception("test")

        self._normalize_ircfg(self.conn)
        irb_bak = None
        if merging_var_candidates:
            self.pad = True
            new_line = AssignBlock([ExprAssign(k, k) for k in merging_var_candidates])
            irb_bak = self.ircfg.blocks[LocKey(0)]
            new_irb = IRBlock(LocKey(0), tuple([new_line, *self.ircfg.blocks[LocKey(0)].assignblks]))
            self.ircfg.blocks[LocKey(0)] = new_irb

        self.analyses = Analyses(self.ircfg, self.asmcfg)
        return irb_bak

    def clear_cache(self):
        # TODO save to disk and recover when needed
        self.asmcfg = None
        self.ircfg = None
        self.analyses = None
        self.ir_arch = None
        self.all_affected_lines = {}
        self.flat_loops = FlatteningLoops()
        self.possible_merge_funcs = set()
        self._merging_var_candidates = None

    def _recognize(self, max_loop_num):
        symb_engine = SymbolicExecutionEngine(self.ir_arch, regs.regs_init)
        todo = [(LocKey(0), symb_engine.get_state())]
        done_loc = set()
        if not max_loop_num:
            max_loop_num = float('inf')
        found_loops_num = 0
        while todo:
            loc_key, symb_state = todo.pop()
            if loc_key in done_loc or loc_key not in self.ircfg.blocks:
                continue
            done_loc.add(loc_key)
            ir_block = self.ircfg.blocks[loc_key]
            symb_engine.set_state(symb_state)
            for ind, assignblk in enumerate(ir_block.assignblks):
                for dst, src in assignblk.items():
                    if max_loop_num < found_loops_num:
                        return
                    if src.is_int() and int(src) in self.func_addresses:
                        assignblk_node = AssignblkNode(ir_block.loc_key, ind, dst)
                        # no uses
                        if assignblk_node not in self.analyses.defuse_edges or not \
                                self.analyses.defuse_edges[assignblk_node]:
                            # possible virtual table initialization
                            self.possible_merge_funcs.add((int(src), frozenset(), loc_key))
                    elif src.is_op("call_func_stack"):
                        self._process_call(src, dst, symb_engine, assignblk, loc_key)
                    elif (expr_simp(src).is_int() and not is_bad_expr(dst)) \
                            or (ir_block.loc_key == LocKey(0) and dst == src and
                                (not self._merging_var_candidates or dst in self._merging_var_candidates)):
                        if self._process_assignment(ir_block, ind, dst):
                            self._merging_var_candidates = None
                            found_loops_num += 1
                symb_engine.eval_updt_assignblk(assignblk)

            for succ in self.ircfg.successors(loc_key):
                todo.append((succ, symb_engine.get_state()))

    def recognize(self, max_loop_num=False, merging_var_candidates=None):
        if not merging_var_candidates:
            merging_var_candidates = None
        if not self.asmcfg:
            self.asmcfg = ExtendedAsmCFG(self.file_path, self.conn)
            self.asmcfg.disassemble(self.func_address, self.conn)
            remove_redundant_and_unpin_blocks(self.asmcfg, LocKey(0), self.asmcfg.mode, unpin=False)
            block_nb = len(self.asmcfg.blocks)
            if block_nb > 4250:
                self.clear_cache()
                logger.critical("Function is too big")
                raise RuntimeError("Function is too big")

            self.ir_arch = self.machine.ira(self.asmcfg.loc_db)
            if self.merging_var:
                merging_var_candidates = {self.merging_var}
        else:
            return
        # setting merging vars
        try:
            irb_bak = self._recog_init(merging_var_candidates)
        except RuntimeError:
            logger.warning("Exotic stack operations, skipping")
            return
        self._recognize(max_loop_num)
        if merging_var_candidates:
            self.ircfg.blocks[LocKey(0)] = irb_bak

    def _process_assignment(self, ir_block, ind, dst):
        assignblk_node = AssignblkNode(ir_block.loc_key, ind, dst)
        # loop id 0 is the default
        logger.debug("Processing %s" %
                     hex(self.asmcfg.loc_db.get_location_offset(ir_block.loc_key) or 0))
        local_affected_lines = {}
        affected_irdsts, possible_nodes = self._get_affected_ir_destinations(assignblk_node, local_affected_lines)
        result = False
        for node in self.asmcfg.walk_breadth_first_forward(LocKey(0)):
            if node in possible_nodes:
                filtered_irdsts = self._filter_sequential_loc_keys(node, affected_irdsts)
                affected_lines = {}
                result |= self._create_flattening_loop(node, filtered_irdsts, affected_lines)
        return result

    def _process_call(self, src, dst, symb_engine, assignblk, loc_key):
        # adds function to the to be processed list
        addr = src.args[0]
        if addr.is_mem():
            addr = addr.ptr
        if addr.is_loc():
            addr = self.asmcfg.loc_db.get_location_offset(addr.loc_key)
        if isinstance(addr, int) or addr.is_int():
            addr = int(addr)
            if addr in self.func_addresses:
                new_merging_var_candidates = self._get_merging_var_candidates(symb_engine, assignblk, dst)
                self.possible_merge_funcs.add((addr, frozenset(new_merging_var_candidates), loc_key))

    def _get_merging_var_candidates(self, symb_engine, assignblk, dst):
        stk_high = ExprInt(self.conn.modules.idc.get_spd(assignblk.instr.offset),
                           self.ir_arch.sp.size)
        init_sp = self.mn.regs.regs_init[self.ir_arch.sp]
        fix_dct = {init_sp: - stk_high + init_sp + ExprInt(dst.size // 8, dst.size)}
        new_merging_var_candidates = set()  # values are tuples key, val
        for key, val in symb_engine.modified(regs.regs_init):
            if not val.is_int() or not val.size > 1 or type(key) not in [ExprId, ExprMem] \
                    or key.is_id() and key.name in ["RIP", "EIP", self.ircfg.IRDst.name]:
                continue
            if not key.is_id():
                # get relative depth
                key = key.replace_expr(fix_dct)
                key = expr_simp(key)
            new_merging_var_candidates.add((key, val))
        return new_merging_var_candidates

    def _get_affected_ir_destinations(self, assignblk_node, local_affected_lines):
        todo = [assignblk_node]
        processed = set()  # {}
        result = {}
        possible_nodes = {assignblk_node.label}
        while todo:
            target = todo.pop()
            if not self.flat_loops[target.label].is_default:
                logger.debug("Overlap at %s skipping" % hex(
                    self.ircfg.loc_db.get_location_offset(target.label) or 0xbadf0d))
                return set(), set()

            if target in processed:
                continue
            local_affected_lines.setdefault(target.label, set()).add(target.index)
            processed.add(target)
            if target.var == self.ircfg.IRDst:
                result[target.label] = target
            possible_nodes.add(target.label)
            for use in self.analyses.defuse_edges.get(target, []):
                todo.append(use)
        return result, possible_nodes

    def _filter_sequential_loc_keys(self, node, affected):
        if node in self.all_affected_lines:
            return set()
        todo = [node]
        accessible = {}
        done = set()
        fst = False  # found the first comparison
        while todo:
            target = todo.pop()
            if target in accessible or target in done:
                continue
            done.add(target)
            succs = self.asmcfg.successors(target)
            irb = self.ircfg.blocks[target]
            if target in affected:
                fst = True
                accessible[target] = affected[target]
            elif len(succs) > 1 and fst:
                continue
            if irb.dst.is_cond() and irb.dst.cond.is_op("CC_EQ"):
                succs = [self.ircfg.get_loc_key(irb.dst.src2.loc_key)]
            todo += succs
        return set(accessible.values())

    def _add_2_control_vars(self, primary_loc_keys, affected_lines, merging_var, done, head_vars):
        # involve cff loops containing compiler "optimization" introducing 2 control variables(
        # range(0,x,1) and range(0,x,1*y)); there are multiple due to various compiler anomalies, but
        # only one from affected_irdsts
        found = False
        for disp_loc, last_cff_locs in self.analyses.rev_back_edges.items():
            if disp_loc not in primary_loc_keys:
                continue
            for last_cff_loc in last_cff_locs:
                preds = self.asmcfg.predecessors(last_cff_loc)
                succs = self.asmcfg.successors(last_cff_loc)
                if not len(succs) > 1 and len(preds) == 1 and last_cff_loc not in affected_lines:
                    last_cff_loc = preds[0]
                    succs = self.asmcfg.successors(last_cff_loc)
                if last_cff_loc not in primary_loc_keys:
                    if len(succs) > 1:
                        primary_loc_keys.add(last_cff_loc)
                        opti_node = AssignblkNode(last_cff_loc, len(self.ircfg.blocks[last_cff_loc].assignblks) - 1,
                                                  self.ir_arch.IRDst)
                        self._process_affected_irdsts({opti_node}, affected_lines, primary_loc_keys, merging_var, done,
                                                      head_vars)
                        if last_cff_loc in primary_loc_keys:
                            # otherwise last_cff_loc couldn't be determined and was removed from primaries
                            found = True
                    if last_cff_loc in affected_lines:
                        found = True
                else:
                    found = True
        if not found:
            raise RuntimeError("There must be a back-edge")

    def _cff_loop_sanity_check(self, primary_loc_keys, node, affected_lines):
        affected_immediate_nb = suitable_predecessors = 0
        try:
            wanted = affected_lines.keys() | self.asmcfg.jmp_table_loc_keys
            for i in primary_loc_keys:
                affected_immediate_nb += i not in self.asmcfg.heads() and \
                                         self.analyses.immediate_dominators[i] in wanted
                # suitable_predecessors += set(self.ircfg.predecessors(i)).issubset(wanted)
                # there can be 3 bad predecessors: the range check, the first block, the dispatch
                # TODO test suitable_predecessors before implementing, they weren't required before
        except KeyError:
            raise RuntimeError()

        if not (len(primary_loc_keys) > 1 and
                len(primary_loc_keys) - 1 - (self._merging_var_candidates is not None) <= affected_immediate_nb and
                # len(primary_loc_keys) - 2 - (self.merging_var_candidates is not None) <= suitable_predecessors and
                all(node in self.analyses.dominators[i] for i in primary_loc_keys)):
            # in this case AL is part of EAX which is tracked, FP affecting huge number of IRDsts therefore we require
            # that none of them are solved to skip it
            # MOV        AL, BYTE PTR [ECX]
            # CMP        AL, 0x30
            # the assignment has to dominate all the primary loc_keys and immediate dominators must contain affected
            # blocks, except the first one; jump table blocks and in case of merged function the initial range check;
            # all the primary blocks have to present in the dominator tree
            raise RuntimeError()

    def _create_flattening_loop(self, node, assign_blocks, affected_lines):
        # assign_blocks are all affected IRDsts
        if not len(assign_blocks) > 1:
            return False

        primary_loc_keys = {i.label for i in assign_blocks}
        done = set()
        head_vars = set()
        merging_var = self._process_affected_irdsts(assign_blocks, affected_lines, primary_loc_keys, self.merging_var,
                                                    done, head_vars)
        try:
            self._add_2_control_vars(primary_loc_keys, affected_lines, merging_var, done, head_vars)
            self._cff_loop_sanity_check(primary_loc_keys, node, affected_lines)
        except RuntimeError:
            return False
        if merging_var:
            self.merging_var = merging_var
            logger.debug("setting merging var %s" % merging_var)
        try:
            self.flat_loops.create(head_vars, affected_lines, primary_loc_keys, self.ircfg,
                                   self.ircfg.loc_db.get_location_offset(node))
        except RuntimeError:
            return False
        logger.debug("adding")
        for tmp_loc_key, lines in affected_lines.items():
            self.all_affected_lines.setdefault(tmp_loc_key, SortedSet()).update(lines)
        return True

    def _process_affected_irdsts(self, assign_blocks, affected_lines, primary_loc_keys, merging_var, done, head_vars):
        dg = ArgCacheDependencyGraph(self, self.ircfg, implicit=False, follow_mem=False, follow_call=False)
        possible_merging_var = merging_var
        incorrect_cache = set()
        for ind, assign_block in enumerate(assign_blocks):
            if self.asmcfg.loc_db.get_location_offset(assign_block.label):
                logger.debug("processing assign_block %d out of %d at %s" %
                             (ind + 1, len(assign_blocks),
                              hex(self.asmcfg.loc_db.get_location_offset(assign_block.label) or 0)))
            base_expr_ids = self.ircfg.blocks[assign_block.label][assign_block.index][assign_block.var].get_r()
            local_done = set(done)
            dr = dg.get(assign_block.label, base_expr_ids, assign_block.index, self.asmcfg.heads(), local_done,
                        incorrect_cache)
            local_affected_lines = {}
            local_head_vars = set()
            for sol in dr:
                if not dg.cached:
                    if not dg.incorrect:
                        possible_merging_vars = set()
                        for pnd in sol.pending:
                            if not contains_local_variable(pnd, self.ir_arch, self.mn):
                                if pnd != self.mn.regs.regs_init[self.ir_arch.sp]:
                                    possible_merging_vars.add(pnd)
                            elif sol.loc_key == LocKey(0):
                                local_head_vars.add(pnd)

                        pmv_len = len(possible_merging_vars)
                        if self._merging_var_candidates and possible_merging_vars:
                            possible_merging_var = possible_merging_vars.pop()
                    if dg.incorrect or pmv_len > (self._merging_var_candidates is not None) \
                            or possible_merging_var and self._merging_var_candidates and \
                            possible_merging_var not in self._merging_var_candidates or \
                            (merging_var and possible_merging_var != merging_var):
                        incorrect_cache.update(sol.pending_links)
                        primary_loc_keys.remove(assign_block.label)
                        if self.asmcfg.loc_db.get_location_offset(assign_block.label):
                            logger.debug("%s cannot be determined" %
                                         hex(self.asmcfg.loc_db.get_location_offset(assign_block.label) or 0))
                        break
                    else:
                        merging_var = possible_merging_var
                self._add_relevant_nodes(sol.relevant_nodes, local_affected_lines)
            else:
                done.update(local_done)
                head_vars.update(local_head_vars)
                affected_lines.setdefault(assign_block.label, SortedSet()).add(assign_block.index)
                for loc_key, lines in local_affected_lines.items():
                    affected_lines.setdefault(loc_key, SortedSet()).update(lines)
        return merging_var

    @staticmethod
    def _add_relevant_nodes(relevant_nodes, affected_lines):
        for node in relevant_nodes:
            affected_lines.setdefault(node.loc_key, SortedSet()).add(node.line_nb)
