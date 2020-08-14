# -*- encoding: utf8 -*-
#
# Copyright (c) 2020 ESET spol. s r.o.
# Contains regexes which are Copyright (C) 2017 FireEye, Inc.
# Author: Vladislav Hrčka <vladislav.hrcka@eset.com>
# See LICENSE file for redistribution.

import logging
import re
from unittest import mock

import rpyc
from miasm.analysis.dse import DSEEngine
from miasm.expression.simplifications import expr_simp
from miasm.analysis.sandbox import Sandbox_Win_x86_32, Sandbox_Win_x86_64
from sortedcontainers import SortedList

from stadeo.string.string_symb_stubs import *
from stadeo.utils.extended_asmcfg import ExtendedAsmCFG

logger = logging.getLogger('StringRevealer')
logger.setLevel(logging.WARNING)


class StringRevealer(object):
    # patterns borrowed from https://github.com/fireeye/flare-floss/blob/master/floss/strings.py
    ASCII_BYTE = br"!\"#\$%&\'\(\)\*\+,-\./0123456789:;<=>\?@ABCDEFGHIJKLMNOPQRSTUVWXYZ\[" \
                 br"\]\^_`abcdefghijklmnopqrstuvwxyz\{\|\}\\\~\t "
    ASCII_RE = re.compile(b"([%s]{%d,})" % (ASCII_BYTE, 3))
    UNICODE_RE = re.compile(b"((?:[%s]\x00){%d,})" % (ASCII_BYTE, 3))

    def __init__(self, attrib):
        self.sandbox = Sandbox_Win_x86_32
        if attrib == 64:
            raise Exception("Not supported")
            # 64 bit string revealer doesn't work due to https://github.com/cea-sec/miasm/issues/647
            self.sandbox = Sandbox_Win_x86_64
        parser = self.sandbox.parser()
        self.options = parser.parse_args()
        self.options.use_windows_structs = True
        self.options.usesegm = True
        self.options.mimic_env = True
        self.options.jitter = "llvm"
        self.sb = None

    @staticmethod
    def _exec_callback(dse, func, occurances, jitter, strings, get_strings_from_dse):
        occurances[jitter.pc] = occurances.get(jitter.pc, 0) + 1
        if occurances[jitter.pc] > 500:
            return False
        # extracts strings more often, but is naturally slower, not needed for Stantinko, one could use it elsewhere:
        # if func.loc_db.get_offset_location(jitter.pc):
        #     # snap = dse.take_snapshot()
        #     # dse.update_state_from_concrete()
        #     strings.update(get_strings_from_dse(dse))
        #     # dse.restore_snapshot(snap)
        dse.callback(jitter)
        return True

    def process_all(self, ip='localhost', port=4455, conn=None):
        """
        Reveals strings in all functions recognized by IDA
        :param ip: optional, IP of the computer running rpyc server in IDA
        :param port: optional, port of the computer running rpyc server in IDA
        :param conn: optional, already estabilished connection to running rpyc server in IDA
        :return: dictionary mapping each processed function address to the respective revealed strings
        """
        close_conn = False
        if not conn:
            close_conn = True
            conn = rpyc.classic.connect(ip, port)

        strings = {}
        file_path = conn.modules.idaapi.get_input_file_path()
        with mock.patch("builtins.open", conn.builtins.open):
            self.sb = self.sandbox(file_path, self.options, globals())
            # put some mem above initial SP
            sp = self.sb.jitter.arch.getsp(self.sb.jitter.attrib)
            setattr(self.sb.jitter.cpu, sp.name, self.sb.jitter.stack_base + self.sb.jitter.stack_size - 0x8 * 80)
            for func_addr in conn.modules.idautils.Functions():
                func = ExtendedAsmCFG(file_path)
                func.disassemble(func_addr, conn)
                strings[func_addr] = self._process_func(func)

        if close_conn:
            conn.close()

        return strings

    def process_funcs(self, func_addresses, ip='localhost', port=4455, conn=None):
        """
        Reveals strings in all supplied function addresses
        :param func_addresses: function addresses to process
        :param ip: optional, IP of the computer running rpyc server in IDA
        :param port: optional, port of the computer running rpyc server in IDA
        :param conn: optional, already estabilished connection to running rpyc server in IDA
        :return: dictionary mapping each processed function address to the respective revealed strings
        """
        close_conn = False
        if not conn:
            close_conn = True
            conn = rpyc.classic.connect(ip, port)

        strings = {}
        file_path = conn.modules.idaapi.get_input_file_path()
        with mock.patch("builtins.open", conn.builtins.open):
            self.sb = self.sandbox(file_path, self.options, globals())
        # put some mem above initial SP
        sp = self.sb.jitter.arch.getsp(self.sb.jitter.attrib)
        setattr(self.sb.jitter.cpu, sp.name, self.sb.jitter.stack_base + self.sb.jitter.stack_size - 0x8 * 80)

        # self.sb.jitter.jit.log_regs = True
        # self.sb.jitter.jit.log_mn = True
        for func_address in func_addresses:
            with mock.patch("builtins.open", conn.builtins.open):
                func = ExtendedAsmCFG(file_path)
                func.disassemble(func_address, conn)
            strings[func_address] = self._process_func(func)

        if close_conn:
            conn.close()

        return strings

    @staticmethod
    def _wipe_dse_errors(dse):
        dse.symb.reset_modified()
        dse.jitter.vm.set_exception(0)
        dse.jitter.cpu.set_exception(0)
        dse.jitter.bs._atomic_mode = False

    def _process_func(self, func):
        dse = DSEEngine(self.sb.machine)
        dse.attach(self.sb.jitter)  # needs to be attached before setting exec_cb to overwrite it with ours
        bak_snap = dse.take_snapshot()
        dse.add_lib_handler(self.sb.libs, globals())
        occurances = {}
        addr = func.loc_db.get_location_offset(LocKey(0))
        asmb = func.loc_key_to_block(LocKey(0))
        strings = set()
        self.sb.jitter.exec_cb = lambda x: self._exec_callback(dse, func, occurances, x, strings,
                                                               self._get_strings_from_dse)
        self.sb.jitter.init_run(addr)
        try:
            self.sb.jitter.run_until(asmb.lines[-1].offset)
        except:
            pass
        dse.update_state_from_concrete()
        initial_snap = dse.take_snapshot()  # prepared initial context
        strings.update(self._get_strings_from_dse(dse))
        dse.restore_snapshot(initial_snap)
        for loc_key in func.walk_breadth_first_forward(LocKey(0)):
            addr = func.loc_db.get_location_offset(loc_key)
            if not addr:
                continue
            occurances.clear()
            self._emul_address(dse, addr)
            dse.update_state_from_concrete()
            strings.update(self._get_strings_from_dse(dse))
            dse.restore_snapshot(initial_snap)

        dse.restore_snapshot(bak_snap)
        strings = self._get_top_level_strings(strings)
        return strings

    def _emul_address(self, dse, addr):
        self.sb.jitter.init_run(addr)
        crashed = set()
        while 1:
            self._wipe_dse_errors(dse)
            try:
                self.sb.jitter.continue_run()
            except Exception as e:
                if isinstance(e, RuntimeError) and \
                        e.args and e.args[0] == "Cannot find address" and \
                        self.sb.jitter.pc not in crashed:
                    instr = self.sb.jitter.jit.mdis.dis_instr(self.sb.jitter.pc)
                    crashed.add(self.sb.jitter.pc)
                    if instr:
                        next_addr = self.sb.jitter.pc + instr.l
                        self.sb.jitter.init_run(next_addr)
                        continue
            break

    @staticmethod
    def _get_top_level_strings(strings):
        new_strings = set()
        while strings:
            string = strings.pop()
            for tmp_string in strings | new_strings:
                if string in tmp_string:
                    break
            else:
                new_strings.add(string)
        return new_strings

    def _get_strings_from_dse(self, dse):
        modified_mem = SortedList(key=lambda x: int(x[0]))
        for key, val in dse.symb.modified(ids=False, mems=True):
            try:
                val = dse.eval_expr(key)
                key = dse.eval_expr(key.ptr)
            except RuntimeError:
                continue
            if not key.is_int() or not val.is_int():
                continue
            modified_mem.add((key, val))
        following_address = None
        current_sequence = b""
        strings = set()
        for address, value in modified_mem:
            if following_address == address:
                current_sequence += int(value).to_bytes(value.size // 8, "little")
            else:
                self._update_strings_from_sequence(current_sequence, strings)
                current_sequence = int(value).to_bytes(value.size // 8, "little")
            following_address = expr_simp(address + ExprInt(value.size // 8, address.size))
        self._update_strings_from_sequence(current_sequence, strings)
        return strings

    def _update_strings_from_sequence(self, sequence, strings):
        strings.update([i.decode() for i in self.ASCII_RE.findall(sequence)])
        strings.update([i.decode("utf-16le") for i in self.UNICODE_RE.findall(sequence)])
