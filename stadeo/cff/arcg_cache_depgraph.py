# -*- encoding: utf8 -*-
#
# Copyright (c) 2020 ESET spol. s r.o.
# Author: Vladislav Hrčka <vladislav.hrcka@eset.com>
# See LICENSE file for redistribution.

from miasm.analysis import depgraph
from miasm.analysis.data_flow import AssignblkNode
from miasm.expression.expression import *
from miasm.expression.simplifications import expr_simp


def is_local_variable(expr, ir_arch_a, mn):
    if not expr.is_mem():
        return None
    ptr = expr.ptr
    diff = expr_simp(ptr - mn.regs.regs_init[ir_arch_a.sp])
    if diff.is_int() and int(expr_simp(expr_is_signed_lower(diff, ExprInt(0, diff.size)))):
        return True
    return None


def contains_local_variable(expr, ir_arch_a, mn):
    visitor = ExprWalk(lambda x: is_local_variable(x, ir_arch_a, mn))
    return visitor.visit(expr)


def custom_init(self, ircfg, initial_state, state, inputs):
    super(depgraph.DependencyResult, self).__init__(state.loc_key, state.pending)
    self.initial_state = initial_state
    self.history = state.history
    self.pending = state.pending
    self.line_nb = state.line_nb
    self.inputs = inputs
    self.links = state.links
    self._ircfg = ircfg

    # Init lazy elements
    self._has_loop = None
    if hasattr(state, 'pending_links'):
        self.pending_links = state.pending_links


class MyDependencyState(depgraph.DependencyState):
    def __init__(self, *args, **kwargs):
        super(depgraph.DependencyState, self).__init__(*args, **kwargs)
        self.pending_links = set()

    # state consisting of the pendings suits much better our needs
    def get_done_state(self):
        """Returns immutable object representing current state"""
        return self.loc_key, frozenset(self.pending)

    def extend(self, loc_key):
        """Return a copy of itself, with itself in history
        @loc_key: LocKey instance for the new DependencyState's loc_key
        """
        new_state = self.__class__(loc_key, self.pending)
        new_state.links = set(self.links)
        new_state.history = self.history + [loc_key]
        new_state.pending_links = set(self.pending_links)
        return new_state


def custom_visit_inner(self, expr, *args, **kwargs):
    if expr.is_id():
        self.follow.add(expr)
    elif expr.is_int():
        self.nofollow.add(expr)
    elif expr.is_loc():
        self.nofollow.add(expr)
    elif expr.is_mem():
        self.follow.add(expr)
        if not self.follow_mem:
            return None
    elif expr.is_function_call():
        self.follow.add(expr)
        if not self.follow_call:
            return None

    ret = super(depgraph.FilterExprSources, self).visit(expr, *args, **kwargs)
    return ret


def is_push_param(recognizer, loc_key, index):
    initial_irb = recognizer.ircfg.blocks[loc_key]
    initial_assignblk = initial_irb[index]
    target_stack_ptr = recognizer.conn.modules.idc.get_spd(initial_assignblk.instr.offset)
    todo = [(loc_key, index + 1)]
    done = set()
    while todo:
        loc_key, index = todo.pop()
        if loc_key in done:
            continue
        done.add(loc_key)
        irb = recognizer.ircfg.blocks[loc_key]
        for assignblk in irb[index:]:
            if assignblk.instr and assignblk.instr.offset:
                stack_ptr = recognizer.conn.modules.idc.get_spd(assignblk.instr.offset)
                if stack_ptr and stack_ptr >= target_stack_ptr:
                    break
                for dst, src in assignblk.items():
                    if src.is_function_call():
                        arg_addresses = recognizer.conn.modules.idaapi.get_arg_addrs(assignblk.instr.offset)
                        if arg_addresses and initial_assignblk.instr.offset in arg_addresses:
                            return True
                        break
        else:
            for succ in recognizer.ircfg.successors(loc_key):
                todo.append((succ, 0))
    return False


depgraph.FilterExprSources.visit_inner = custom_visit_inner
depgraph.DependencyState = MyDependencyState
depgraph.DependencyResult.__init__ = custom_init


class ArgCacheDependencyGraph(depgraph.DependencyGraph):
    """
    Since there's typically a number of sequential comparisons in cff loops, we take advantage of the fact and, memoize
    already processed states. We can do this because the graph doesn't change. We also halt on mem stack arguments, they
    cannot be part of cff loops.
    """
    def __init__(self, recognizer, *args, **kwargs):
        super(ArgCacheDependencyGraph, self).__init__(*args, **kwargs)
        self.incorrect = False
        self.ir = recognizer.ir_arch
        self.mn = recognizer.mn
        self.recognizer = recognizer
        self.defuse_edges = recognizer.analyses.defuse_edges
        self.cached = False
        self.new_cache_states = set()

    def _track_exprs(self, state, assignblk, line_nb):
        """Track pending expression in an assignblock"""
        if self.incorrect:
            return
        future_pending = {}
        node_resolved = set()
        for dst, src in assignblk.items():
            assignblk_node = AssignblkNode(state.loc_key, line_nb, dst)
            # Only track pending
            if dst not in state.pending:
                if type(src) in [ExprId, ExprOp, ExprCompose] and any(src in i for i in state.pending):
                    if assignblk_node in self.defuse_edges:
                        # targets function arguments such as lea eax, var; push eax since constant propagation doesn't
                        # work correctly in miasm; https://github.com/cea-sec/miasm/issues/1197;
                        # https://github.com/cea-sec/miasm/issues/1218; https://github.com/cea-sec/miasm/issues/1259;
                        # TODO when constant propagation is fixed, rework this; elaborate on 1259
                        for assignblk_node in self.defuse_edges[assignblk_node]:
                            if is_local_variable(assignblk_node.var, self.ir, self.mn) \
                                    and assignblk_node not in self.defuse_edges:
                                break
                        else:
                            continue
                    elif not is_local_variable(dst, self.ir, self.mn):
                        continue

                    if is_push_param(self.recognizer, assignblk_node.label, assignblk_node.index):
                        # prevents FPs in weird code such as push    [ebp+var_18]; call ...; add     esp, 4
                        # where [ebp+var_18] is not param and it's just pushed
                        self.incorrect = True
                        return
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
        state.remove_pendings(node_resolved)
        state.add_pendings(future_pending)

    def get(self, loc_key, elements, line_nb, heads, done_cache_states=None, incorrect_cache_states=None):
        """Compute the dependencies of @elements at line number @line_nb in
        the block named @loc_key in the current IRCFG, before the execution of
        this line. Dependency check stop if one of @heads is reached. The difference
        with the Miasm implementation is that we just want to know whether there's a
        non-integer dependency and optimize the computation that way.
        @loc_key: LocKey instance
        @element: set of Expr instances
        @line_nb: int
        @heads: set of LocKey instances
        Return an iterator on DiGraph(DependencyNode)
        """
        # Init the algorithm
        if done_cache_states is None:
            done_cache_states = set()
        if incorrect_cache_states is None:
            incorrect_cache_states = set()
        inputs = {element: set() for element in elements}
        initial_state = depgraph.DependencyState(loc_key, inputs, line_nb)
        todo = {initial_state}
        dpResultcls = depgraph.DependencyResultImplicit if self._implicit else depgraph.DependencyResult
        self.incorrect = False
        new_cache_states = set()
        self.new_cache_states = new_cache_states

        while todo:
            state = todo.pop()
            self._compute_intrablock(state)
            if self.incorrect:
                yield dpResultcls(self._ircfg, initial_state, state, elements)
                self.incorrect = False
                continue
            done_state = state.get_done_state()
            if done_state in incorrect_cache_states:
                self.incorrect = True
                yield dpResultcls(self._ircfg, initial_state, state, elements)
                self.incorrect = False
                continue
            if done_state in done_cache_states | new_cache_states:
                self.cached = True
                yield dpResultcls(self._ircfg, initial_state, state, elements)
                self.cached = False
                continue
            new_cache_states.add(done_state)
            if state.loc_key in heads or not state.pending:
                yield dpResultcls(self._ircfg, initial_state, state, elements)
                continue

            if self._implicit:
                # Force IRDst to be tracked, except in the input block
                state.pending[self._ircfg.IRDst] = set()

            state.pending_links.add(done_state)
            # Propagate state to parents
            for pred in self._ircfg.predecessors_iter(state.loc_key):
                todo.add(state.extend(pred))
        done_cache_states.update(new_cache_states)
