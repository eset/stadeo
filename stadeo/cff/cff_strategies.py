# -*- encoding: utf8 -*-
#
# Copyright (c) 2020 ESET spol. s r.o.
# Author: Vladislav Hrčka <vladislav.hrcka@eset.com>
# See LICENSE file for redistribution.

import logging
from pprint import pformat
from unittest import mock

import rpyc
from miasm.analysis.machine import Machine
from miasm.expression.expression import LocKey

from stadeo.cff.cff_recognizer import CFFRecognizer, ConfirmedMergeFunc
from stadeo.cff.cff_solver import CFFSolver
from stadeo.utils.extended_asmcfg import write_patches_to_file
from collections.abc import Iterable


logger = logging.getLogger('CFFstrategies')
logger.setLevel(logging.WARNING)


class CFFStrategies(object):
    def __init__(self, arch):
        """

        :param arch: Either 32 or 64 bit architecture
        """
        self._pending = {}
        self._reached_funcs = set()
        if arch not in [32, 64]:
            raise ValueError
        self._machine = Machine("x86_" + str(arch))

    def solve_loop(self, func_address, empty_address, context=None, ip='localhost', port=4455, conn=None,
                   only_one=False):
        """
        Deobfuscates single loop
        :param func_address: address of the function to be deobfuscated
        :param empty_address: address of the resulting deobfuscated function
        :param context: optional, dictionary assigning merging variable to its value using Miasm expressions
        :param ip: optional, IP of the computer running rpyc server in IDA
        :param port: optional, port of the computer running rpyc server in IDA
        :param conn: optional, already estabilished connection to running rpyc server in IDA
        :param only_one: do not attempt to reveal more than 1 CFF loop
        :return: True on successful deobfuscation, otherwise False
        """
        close_conn = False
        if not conn:
            close_conn = True
            conn = rpyc.classic.connect(ip, port)

        with mock.patch("builtins.open", conn.builtins.open):
            if context is None:
                context = {}

            file_path = conn.modules.idaapi.get_input_file_path()
            recognizer = CFFRecognizer(file_path, func_address, self._machine, conn)
            try:
                recognizer.recognize(only_one, context)
            except:
                return False
            val = None
            if context:
                val = set(context.values()).pop()
            new_empty_address = self._solve_loop(empty_address, recognizer, file_path, conn, val)

        if close_conn:
            conn.close()

        return new_empty_address == empty_address

    def _solve_loop(self, empty_address, recognizer, file_path, conn=None, val=None):
        func = recognizer.asmcfg
        deflattener = CFFSolver(recognizer)
        new_head = deflattener.process(self._pending, val, self._reached_funcs)
        if val:
            val = int(val)
        if not new_head:
            local_mapping = "skipping 0x%08x with val %s: %s\n" % (func.func_addr, recognizer.merging_var,
                                                                   hex(val or 0x0BADF00D))
            print("%s" % local_mapping, end="")
            return empty_address
        local_mapping = "0x%08x -> 0x%08x with val %s: %s\n" % (func.func_addr, empty_address, recognizer.merging_var,
                                                                hex(val or 0x0BADF00D))
        print("mapping: %s" % local_mapping, end="")
        deflattener.out_asmcfg.loc_db.set_location_offset(LocKey(0), empty_address, True)
        new_addr = write_patches_to_file(deflattener.out_asmcfg, func.exectbl, empty_address, file_path, func.mode,
                                         2 ** 64 - 1, new_head)
        if conn:
            conn.modules.idaapi.reload_file(conn.modules.idaapi.get_input_file_path(), 0)
            conn.modules.ida_funcs.add_func(new_addr)
        return new_addr

    def process_all(self, empty_address, ip='localhost', port=4455, conn=None):
        """
        Tries to deobfuscate all functions recognized by IDA
        :param empty_address: address where to put all the deobfuscated functions
        :param ip: optional, IP of the computer running rpyc server in IDA
        :param port: optional, port of the computer running rpyc server in IDA
        :param conn: optional, already estabilished connection to running rpyc server in IDA
        :return: dictionary assigning each processed function address either to None in case of failure or to the
        respective @ConfirmedMergeFunc instance
        """
        close_conn = False
        if not conn:
            close_conn = True
            conn = rpyc.classic.connect(ip, port)

        recognized_funcs = {}
        with mock.patch("builtins.open", conn.builtins.open):
            file_path = conn.modules.idaapi.get_input_file_path()
            for func_addr in conn.modules.idautils.Functions():
                recognizer = CFFRecognizer(file_path, func_addr, self._machine, conn)
                try:
                    recognizer.recognize(True)
                except:
                    recognized_funcs[func_addr] = None
                    continue
                recognized_funcs[func_addr] = ConfirmedMergeFunc(recognizer, empty_address)
                empty_address = self._solve_loop(empty_address, recognizer, file_path, conn)
                if recognized_funcs[func_addr].vals == empty_address:
                    recognized_funcs[func_addr] = None
                recognizer.clear_cache()

        if close_conn:
            conn.close()

        return recognized_funcs

    @staticmethod
    def _clear_cache(recognized_funcs):
        for merge_func in recognized_funcs.values():
            if not merge_func:
                continue
            merge_func.recognizer.clear_cache()

    def process_merging(self, func_addresses, empty_address, ip='localhost', port=4455, conn=None,
                        recognized_funcs=None):
        """
        Tries to discover and deobfuscate reachable functions
        :param func_addresses: initial function address or addresses
        :param empty_address: address where to put all the deobfuscated functions
        :param ip: optional, IP of the computer running rpyc server in IDA
        :param port: optional, port of the computer running rpyc server in IDA
        :param conn: optional, already estabilished connection to running rpyc server in IDA
        :param recognized_funcs: optional, dictionary assigning each already processed function address either to None
        in case of failure or to the respective @ConfirmedMergeFunc instance; used after repeated execution with
        different initial address
        :return: dictionary assigning each processed function address either to None in case of failure or to the
        respective @ConfirmedMergeFunc instance
        """
        if recognized_funcs is None:
            recognized_funcs = {}  # ConfirmedMergeFunc
        if not isinstance(func_addresses, Iterable):
            # in case of only one function
            func_addresses = {func_addresses}
        self._reached_funcs.update(func_addresses)

        processed_blocks = 0
        close_conn = False
        if not conn:
            close_conn = True
            conn = rpyc.classic.connect(ip, port)

        with mock.patch("builtins.open", conn.builtins.open):
            file_path = conn.modules.idaapi.get_input_file_path()
            while self._reached_funcs:
                func_addr = self._reached_funcs.pop()
                logger.debug("Processing func at 0x%x" % func_addr)
                logger.debug("Reached funcs: %s" % {hex(i) for i in self._reached_funcs})
                logger.debug("Pending func_addr: %s" % (pformat(self._pending[func_addr]) if func_addr in self._pending
                             else "None"))

                if processed_blocks > 800:
                    # clear cached recognizers to avoid running out of memory
                    processed_blocks = 0
                    self._clear_cache(recognized_funcs)

                if func_addr not in recognized_funcs:
                    # recognize a new func for the first time
                    ida_func = conn.modules.idaapi.get_func(func_addr)
                    if ida_func and ida_func.flags & conn.modules.idaapi.FUNC_LIB:
                        local_mapping = "skipping 0x%08x (library func)\n" % func_addr
                        print("%s" % local_mapping, end="")
                        recognized_funcs[func_addr] = None
                        if func_addr in self._pending:
                            del self._pending[func_addr]
                        continue
                    recognizer = CFFRecognizer(file_path, func_addr, self._machine, conn)
                    merging_var_candidates = self._pending.get(func_addr, {})
                    try:
                        recognizer.recognize(False, merging_var_candidates)
                        recognized_funcs[func_addr] = ConfirmedMergeFunc(recognizer, {})
                        processed_blocks += len(recognizer.asmcfg.blocks)
                    except (TypeError, OSError, RuntimeError):
                        recognized_funcs[func_addr] = None
                        logger.warning("Skipping exotic func at 0x%x" % func_addr)
                        if func_addr in self._pending:
                            del self._pending[func_addr]
                        continue
                elif not self._pending.get(func_addr, None) or \
                        not (recognized_funcs[func_addr] and recognized_funcs[func_addr].recognizer.merging_var):
                    if func_addr in self._pending:
                        del self._pending[func_addr]
                    continue

                recognizer = recognized_funcs[func_addr].recognizer
                merging_var = recognizer.merging_var

                if not recognizer.asmcfg:
                    # cache has been cleared
                    recognizer.recognize()
                    processed_blocks += len(recognizer.asmcfg.blocks)

                if not merging_var:
                    # just added non merging; even non-cff funcs can reach this point since they don't have any merging
                    # var, they are to be considered as processed from now on
                    recognized_funcs[func_addr].vals = empty_address
                    empty_address = self._solve_loop(empty_address, recognizer, file_path, conn)
                    if recognized_funcs[func_addr].vals == empty_address:
                        recognized_funcs[func_addr].vals = None
                    continue
                if merging_var not in self._pending[func_addr]:
                    logger.warning("Function 0x%x isn't merging, ignore its previous results" % func_addr)
                    recognizer.flat_loops.loops.pop(0)  # the first loop is merging
                    recognizer.merging_var = None
                    empty_address = self._solve_loop(empty_address, recognizer, file_path, conn)
                    del self._pending[func_addr]
                    continue
                current_vals = self._pending[func_addr][merging_var]
                del self._pending[func_addr]
                for val in current_vals:
                    if val in recognized_funcs[func_addr].vals:
                        continue
                    recognized_funcs[func_addr].vals[val] = empty_address
                    empty_address = self._solve_loop(empty_address, recognizer, file_path, conn, val)
                    if recognized_funcs[func_addr].vals[val] == empty_address:
                        # failed
                        recognized_funcs[func_addr] = None

        if close_conn:
            conn.close()

        return recognized_funcs
