# -*- encoding: utf8 -*-
#
# Copyright (c) 2020 ESET spol. s r.o.
# Author: Vladislav Hrčka <vladislav.hrcka@eset.com>
# See LICENSE file for redistribution.

import logging

from miasm.analysis.depgraph import DependencyGraph
from miasm.arch.x86.arch import instruction_x86, additional_info
from miasm.core.asmblock import AsmConstraintTo, AsmBlock, AsmConstraint, AsmCFG
from miasm.core.locationdb import LocationDB
from miasm.expression.expression import *
from miasm.ir.ir import AssignBlock, IRBlock
from miasm.ir.symbexec import SymbolicExecutionEngine

from stadeo.utils.extended_asmcfg import create_jump_instruction
from stadeo.cff.cff_recognizer import FlattenState

logger = logging.getLogger('CFFsolver')
logger.setLevel(logging.WARNING)


class CFFSolver(object):
    def __init__(self, recognizer):
        self.ircfg = recognizer.ircfg
        self.asmcfg = recognizer.asmcfg
        self.flat_loops = recognizer.flat_loops
        self.all_affected_lines = recognizer.all_affected_lines
        self.ir_arch = recognizer.ir_arch
        loc_db = LocationDB()
        loc_db.merge(recognizer.asmcfg.loc_db)
        self.out_asmcfg = AsmCFG(loc_db)
        self.merging_var = recognizer.merging_var
        self.pad = recognizer.pad
        self.possible_merge_funcs = recognizer.possible_merge_funcs
        self.relevant_nodes = set()

    def process(self, pending, merging_val, reached_funcs):
        if len(self.flat_loops) == 0:
            # add all reached functions
            for func_addr, possible_merge_vars, loc_key in self.possible_merge_funcs:
                reached_funcs.add(func_addr)
                for expr, val in possible_merge_vars:
                    pending.setdefault(func_addr, {}).setdefault(expr, set()).add(val)
            return None

        assert len(self.asmcfg.heads()) == 1

        # add merging var to the ircfg
        if self.pad:
            initial_block_bak = self.ircfg.blocks[LocKey(0)]
            if merging_val and self.merging_var:
                asgn_blk = AssignBlock([ExprAssign(self.merging_var, merging_val)])
            else:
                asgn_blk = AssignBlock()
            assignblks = tuple([asgn_blk, *self.ircfg.blocks[LocKey(0)].assignblks])
            self.ircfg.blocks[LocKey(0)] = IRBlock(LocKey(0), assignblks)

        head = self.asmcfg.heads()[0]
        head_block = self.asmcfg.loc_key_to_block(head)
        new_head = self._deobfuscate_cff_loops(head_block, self.asmcfg.machine.mn.regs.regs_init)

        if self.pad:
            self.ircfg.blocks[LocKey(0)] = initial_block_bak
            if merging_val and self.merging_var:
                mode = self.asmcfg.mode
                fix_dct = {self.asmcfg.machine.mn.regs.regs_init[self.ir_arch.sp]: self.ir_arch.sp}
                mov = instruction_x86("MOV", mode, [self.merging_var.replace_expr(fix_dct), merging_val])
                mov.additional_info = additional_info()
                mov.additional_info.g1.value = 0
                self.out_asmcfg.loc_key_to_block(LocKey(0)).lines.insert(0, mov)

        loc_keys = self.relevant_nodes
        for func_addr, possible_merge_vars, loc_key in self.possible_merge_funcs:
            if loc_key in loc_keys:
                reached_funcs.add(func_addr)
                for expr, val in possible_merge_vars:
                    pending.setdefault(func_addr, {}).setdefault(expr, set()).add(val)

        return new_head

    def _insert_flat_block(self, source_flat_block, symb_exec, flat_block_to_loc_key):
        """
        Copies source_flat_block and sets its successors according to flat_block_to_loc_key
        :param flat_block_to_loc_key: dictionary mapping flat_blocks to respective loc_keys
        :param symb_exec: instance of current symbolic execution engine
        :param source_flat_block: flat_block to be inserted
        :return: dictionary mapping old successor loc_keys to the new ones
        """
        # we're not using redirect_successors after copying to avoid executing the same loops multiple times
        source_block = self.asmcfg.loc_key_to_block(source_flat_block.block_loc_key)
        tobe_processed = {}
        new_flat_blocks = set()
        new_block_loc_key = flat_block_to_loc_key[source_flat_block]
        if self.out_asmcfg.loc_key_to_block(new_block_loc_key) is not None:
            raise Exception("Target loc_key is already associated to a block")
        new_block = AsmBlock(new_block_loc_key)

        # copy instructions
        for ln in source_block.lines:
            tmp_ln = instruction_x86(ln.name, ln.mode, [i.copy() for i in ln.args], ln.additional_info)
            tmp_ln.b = ln.b
            tmp_ln.l = ln.l
            tmp_ln.offset = ln.offset
            new_block.addline(tmp_ln)

        constraints = source_block.bto
        # try to simplify the destination if it's a primary flattening block
        if not self.flat_loops[source_block.loc_key].is_default:
            logger.debug("current block is a part of primary loc_keys")
            simplified_target = symb_exec.eval_expr(self.ircfg.IRDst)
            if isinstance(simplified_target, ExprInt):
                simplified_target = self.asmcfg.loc_db.get_offset_location(int(simplified_target))
            elif isinstance(simplified_target, ExprLoc):
                simplified_target = simplified_target.loc_key
            else:
                # there's probably a(n) (series of) unknown instruction(s) causing an implicit conditional assignment
                # such as CMOV or SBB->AND->ADD, prepend comparison + cond jump if it happens to be common, or add it to
                # ExtendedAsmCFG.extended_discovery and split flow on the final instruction

                # it's also possible that it's not related to any cff loop at all
                addr = self.asmcfg.loc_db.get_location_offset(source_flat_block.block_loc_key)
                addr = hex(addr) if addr else addr
                logger.warning("Couldn't simplify loc_key %s at %s, continuing" %
                               (str(source_flat_block.block_loc_key), addr))
                logger.warning("the simplified target is %s of instance %s" %
                               (simplified_target, type(simplified_target)))
                simplified_target = None
            if simplified_target:
                constraints = {AsmConstraintTo(simplified_target)}
                mode = self.asmcfg.mode

                # remove redundant comparison
                dp = DependencyGraph(self.ircfg, True)
                block_loc_key = source_block.loc_key
                res = next(dp.get(block_loc_key, {self.ircfg.IRDst}, None, {block_loc_key}))
                for depnode in res.relevant_nodes:
                    ind = depnode.line_nb
                    ind -= (len(self.ircfg.blocks[block_loc_key]) - len(new_block.lines))
                    if new_block.lines[ind].name == "CMP":
                        new_block.lines.pop(ind)

                new_block.lines[-1] = create_jump_instruction(mode, ExprLoc(simplified_target, mode))

        # copy constraints
        new_bto = set()
        for constraint in constraints:
            if not self.asmcfg.loc_key_to_block(constraint.loc_key):
                logger.debug("Skipping bad constraint %s" % constraint.loc_key)
                continue
            flat_block = self.flat_loops.get_block(constraint.loc_key, symb_exec, source_flat_block)
            if flat_block not in flat_block_to_loc_key:
                new_flat_blocks.add(flat_block)
                new_loc_key = self.out_asmcfg.loc_db.add_location()
                tobe_processed[constraint.loc_key] = (new_loc_key, flat_block)
                flat_block_to_loc_key[flat_block] = new_loc_key
            else:
                new_loc_key = flat_block_to_loc_key[flat_block]
            new_bto.add(AsmConstraint(new_loc_key, constraint.c_t))
        new_block.bto = new_bto
        new_block.alignment = source_block.alignment

        # change jmp targets
        if new_block.lines:
            for ind, arg in enumerate(list(new_block.lines[-1].args)):
                if isinstance(arg, ExprLoc):
                    if not self.asmcfg.loc_key_to_block(arg.loc_key):
                        logger.debug("Skipping bad constraint %s" % arg.loc_key)
                        continue
                    new_target, flat_block = tobe_processed.get(arg.loc_key, (None, None))
                    if not new_target:
                        flat_block = self.flat_loops.get_block(arg.loc_key, symb_exec, source_flat_block)
                        new_target = flat_block_to_loc_key.get(flat_block)
                    # None in case of irrelevant calls
                    logger.debug("new target: %s" % new_target)
                    if new_target:
                        new_block.lines[-1].args[ind] = ExprLoc(new_target, arg.size)

        self.out_asmcfg.add_block(new_block)
        return new_flat_blocks

    def _deobfuscate_cff_loops(self, source_block, symbols):
        """

        :param symbols: initial symbols of symbolic execution engine to be created
        :param source_block: head of the graph to be deobfuscated
        :return:
        """
        symb_exec = SymbolicExecutionEngine(self.ir_arch)
        flat_block = self.flat_loops.get_block(source_block.loc_key, symb_exec, None)
        # maps flattening blocks to their respective loc_keys
        new_head = LocKey(0)
        flat_block_to_loc_key = {flat_block: new_head}
        todo = [FlattenState(flat_block, symbols)]
        counter = {}
        while todo:
            state = todo.pop()
            block_loc_key = state.flat_block.block_loc_key
            self.relevant_nodes.add(block_loc_key)
            counter[block_loc_key] = counter.get(block_loc_key, 0) + 1
            logger.debug("Processing block at 0x%x as %s; in all affected: %d; loops_id: %s; the jtc_vars are:" %
                         (self.asmcfg.loc_db.get_location_offset(block_loc_key) or 0xBAD, str(block_loc_key),
                          block_loc_key in self.all_affected_lines,
                          self.flat_loops[block_loc_key].loc_key))
            if counter[block_loc_key] > 500:
                raise Exception("Couldn't deobfuscate cff loop, either fell into an infinite loop or processing very "
                                "big function")
            symb_exec.set_state(state.symbols)
            # evaluate all affected lines
            self._eval_updt_lines(symb_exec, block_loc_key)
            for flat_block in self._insert_flat_block(state.flat_block, symb_exec, flat_block_to_loc_key):
                todo.append(FlattenState(flat_block, symb_exec.get_state()))
        return new_head

    def _eval_updt_lines(self, symb_exec, loc_key):
        logger.debug("[DBG} block to eval: %s" % self.ircfg.blocks[loc_key])
        if loc_key not in self.all_affected_lines:
            return
        logger.debug("[DBG} lines to eval: %s" % str(self.all_affected_lines[loc_key]))
        for line_nb in self.all_affected_lines[loc_key]:
            assign_blk = self.ircfg.blocks[loc_key].assignblks[line_nb]
            symb_exec.eval_updt_assignblk(assign_blk)
