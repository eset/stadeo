# -*- encoding: utf8 -*-
#
# Copyright (c) 2020 ESET spol. s r.o.
# Author: Vladislav Hrčka <vladislav.hrcka@eset.com>
# See LICENSE file for redistribution.

from binascii import hexlify

from miasm.expression.expression import *


# TODO add stubs for other string manipulation functions - current stantinko versions has been seen to only use strcat
#  and strcpy via win api


def get_win_str_data_a(jitter, ad_str, max_char=None):
    l = 0
    tmp = ad_str
    while ((max_char is None or l < max_char) and
           jitter.vm.get_mem(tmp, 1) != b"\x00"):
        tmp += 1
        l += 1
    data = jitter.vm.get_mem(ad_str, l)
    return data


def get_win_str_data_w(jitter, ad_str, max_char=None):
    l = 0
    tmp = ad_str
    while ((max_char is None or l < max_char) and
           jitter.vm.get_mem(tmp, 2) != b"\x00\x00"):
        tmp += 2
        l += 2
    s = jitter.vm.get_mem(ad_str, l)
    return s


def kernel32_lstrcat(dse, get_win_str_data, zero_pad):
    arg_ptr2 = dse.jitter.get_arg_n_stdcall(2)
    arg_ptr1 = dse.jitter.get_arg_n_stdcall(1)
    s2 = get_win_str_data(dse.jitter, arg_ptr2)
    s1 = get_win_str_data(dse.jitter, arg_ptr1)
    real_len = len(s2) * 8 + zero_pad * 8
    value = int(hexlify(s2[::-1]), 16)
    rhs = ExprCompose(ExprInt(value, len(s2) * 8), ExprInt(0, zero_pad * 8))
    if dse.jitter.ir_arch.attrib == 32:
        stack_ptr = ExprMem(dse.jitter.ir_arch.sp + ExprInt(4, 32), dse.jitter.ir_arch.attrib)
        shifted_evaluated_stack_ptr = dse.eval_expr(stack_ptr + ExprInt(len(s1), 32))
        lhs = ExprMem(shifted_evaluated_stack_ptr, real_len)
        upd = {lhs: rhs,
               ExprId("EAX", 32): dse.eval_expr(stack_ptr)}
    else:
        lhs = ExprMem(ExprId("RCX", 64) + ExprInt(len(s1), 64), real_len)
        upd = {lhs: rhs,
               ExprId("RAX", 64): dse.eval_expr(ExprId("RCX", 64))}
    dse.update_state(upd)
    # apply ret effects
    rhs = dse.eval_expr(dse.jitter.ir_arch.sp + ExprInt(12, dse.jitter.ir_arch.sp.size))
    dse.update_state({dse.jitter.ir_arch.sp: rhs})


def kernel32_lstrcatW_symb(dse):
    kernel32_lstrcat(dse, get_win_str_data_w, 2)


def kernel32_lstrcatA_symb(dse):
    kernel32_lstrcat(dse, get_win_str_data_a, 1)


def kernel32_lstrcpy(dse, get_win_str_data, zero_pad):
    arg_ptr2 = dse.jitter.get_arg_n_stdcall(2)
    s2 = get_win_str_data(dse.jitter, arg_ptr2)
    real_len = len(s2) * 8 + zero_pad * 8
    value = int(hexlify(s2[::-1]), 16)
    rhs = ExprCompose(ExprInt(value, len(s2) * 8), ExprInt(0, zero_pad * 8))
    if dse.jitter.ir_arch.attrib == 32:
        stack_ptr = ExprMem(dse.jitter.ir_arch.sp + ExprInt(4, 32), dse.jitter.ir_arch.attrib)
        evaluated_stack_ptr = dse.eval_expr(stack_ptr)
        lhs = ExprMem(evaluated_stack_ptr, real_len)
        upd = {lhs: rhs,
               ExprId("EAX", 32): lhs.ptr}
    else:
        lhs = ExprMem(ExprId("RCX", 64), real_len)
        upd = {lhs: rhs,
               ExprId("RAX", 64): lhs.ptr}
    dse.update_state(upd)
    # apply ret effects
    rhs = dse.eval_expr(dse.jitter.ir_arch.sp + ExprInt(12, dse.jitter.ir_arch.sp.size))
    dse.update_state({dse.jitter.ir_arch.sp: rhs})


def kernel32_lstrcpyA_symb(dse):
    kernel32_lstrcpy(dse, get_win_str_data_a, 1)


def kernel32_lstrcpyW_symb(dse):
    kernel32_lstrcpy(dse, get_win_str_data_w, 2)
