# Copyright (C) 2013-2017 The python-bitcoinlib developers
# Copyright (C) 2018 The python-bitcointx developers
#
# This file is part of python-bitcointx.
#
# It is subject to the license terms in the LICENSE file found in the top-level
# directory of this distribution.
#
# No part of python-bitcointx, including this file, may be copied, modified,
# propagated, or distributed except according to the terms contained in the
# LICENSE file.

# pylama:ignore=E501

import json
import os
import unittest
import warnings
import ctypes

from typing import List, Iterator, Tuple, Set, Optional

from binascii import unhexlify

from bitcointx.core import (
    x, ValidationError,
    CTxOut, CTxIn, CTransaction, COutPoint, CTxWitness, CTxInWitness
)
from bitcointx.core.key import CKey
from bitcointx.core.script import (
    OPCODES_BY_NAME, CScript, CScriptWitness,
    OP_0, SIGHASH_ALL, SIGVERSION_BASE, SIGVERSION_WITNESS_V0,
    standard_multisig_redeem_script, standard_multisig_witness_stack,
)
from bitcointx.core.scripteval import (
    VerifyScript, SCRIPT_VERIFY_FLAGS_BY_NAME, SCRIPT_VERIFY_P2SH,
    SCRIPT_VERIFY_WITNESS, ScriptVerifyFlag_Type
)
from bitcointx.core.bitcoinconsensus import (
    ConsensusVerifyScript, BITCOINCONSENSUS_ACCEPTED_FLAGS,
    load_bitcoinconsensus_library
)


def parse_script(s: str) -> CScript:
    def ishex(s: str) -> bool:
        return set(s).issubset(set('0123456789abcdefABCDEF'))

    r: List[bytes] = []

    # Create an opcodes_by_name table with both OP_ prefixed names and
    # shortened ones with the OP_ dropped.
    opcodes_by_name = {}
    for name, code in OPCODES_BY_NAME.items():
        opcodes_by_name[name] = code
        opcodes_by_name[name[3:]] = code

    for word in s.split():
        if word.isdigit() or (word[0] == '-' and word[1:].isdigit()):
            r.append(CScript([int(word)]))
        elif word.startswith('0x') and ishex(word[2:]):
            # Raw ex data, inserted NOT pushed onto stack:
            r.append(unhexlify(word[2:].encode('utf8')))
        elif len(word) >= 2 and word[0] == "'" and word[-1] == "'":
            r.append(CScript([bytes(word[1:-1].encode('utf8'))]))
        elif word in opcodes_by_name:
            r.append(CScript([opcodes_by_name[word]]))
        else:
            raise ValueError("Error parsing script: %r" % s)

    return CScript(b''.join(r))


def load_test_vectors(
    name: str, skip_fixme: bool = True
) -> Iterator[
    Tuple[CScript, CScript, CScriptWitness, int, Set[ScriptVerifyFlag_Type],
          str, str, str]
]:
    with open(os.path.dirname(__file__) + '/data/' + name, 'r') as fd:
        fixme_comment = None
        num_skipped = 0
        for test_case in json.load(fd):
            if len(test_case) == 1:
                continue  # comment

            if len(test_case) == 2:
                if not skip_fixme:
                    assert test_case[0].startswith('FIXME'),\
                        "we do not expect anything other than FIXME* here"
                    continue
                if test_case[0] == 'FIXME':
                    fixme_comment = test_case[1]
                    continue
                if test_case[0] == 'FIXME_END':
                    warnings.warn("SKIPPED {} tests: {}"
                                  .format(num_skipped, fixme_comment))
                    fixme_comment = None
                    num_skipped = 0
                    continue

            if fixme_comment:
                num_skipped += 1
                continue

            to_unpack = test_case.copy()

            witness = CScriptWitness()
            nValue = 0
            if isinstance(to_unpack[0], list):
                wdata = to_unpack.pop(0)
                stack = [CScript(x(d)) for d in wdata[:-1]]
                witness = CScriptWitness(stack)
                nValue = int(round(wdata[-1] * 1e8))

            if len(to_unpack) == 4:
                to_unpack.append('')  # add missing comment

            assert len(to_unpack) == 5, "unexpected test data format: {}".format(to_unpack)

            scriptSig_str, scriptPubKey_str, flags, expected_result, comment = to_unpack

            scriptSig = parse_script(scriptSig_str)
            scriptPubKey = parse_script(scriptPubKey_str)

            flag_set = set()
            for flag in flags.split(','):
                if flag == '' or flag == 'NONE':
                    pass

                else:
                    try:
                        flag = SCRIPT_VERIFY_FLAGS_BY_NAME[flag]
                    except IndexError:
                        raise Exception('Unknown script verify flag %r' % flag)

                    flag_set.add(flag)

            yield (scriptSig, scriptPubKey, witness, nValue,
                   flag_set, expected_result, comment, test_case)

        if fixme_comment is not None:
            raise Exception('Unbalanced FIXME blocks in test data')


class Test_EvalScript(unittest.TestCase):
    def create_test_txs(
        self, scriptSig: CScript, scriptPubKey: CScript,
        witness: CScriptWitness, nValue: int
    ) -> Tuple[CTransaction, CTransaction]:
        txCredit = CTransaction([CTxIn(COutPoint(), CScript([OP_0, OP_0]), nSequence=0xFFFFFFFF)],
                                [CTxOut(nValue, scriptPubKey)],
                                witness=CTxWitness(),
                                nLockTime=0, nVersion=1)
        txSpend = CTransaction([CTxIn(COutPoint(txCredit.GetTxid(), 0), scriptSig, nSequence=0xFFFFFFFF)],
                               [CTxOut(nValue, CScript())],
                               nLockTime=0, nVersion=1,
                               witness=CTxWitness([CTxInWitness(witness)]))
        return (txCredit, txSpend)

    def test_script(self) -> None:
        for t in load_test_vectors('script_tests.json'):
            (scriptSig, scriptPubKey, witness, nValue,
             flags, expected_result, comment, test_case) = t
            (txCredit, txSpend) = self.create_test_txs(scriptSig, scriptPubKey, witness, nValue)

            try:
                VerifyScript(scriptSig, scriptPubKey, txSpend, 0, flags, amount=nValue, witness=witness)
            except ValidationError as err:
                if expected_result == 'OK':
                    self.fail('Script FAILED: %r %r %r with exception %r\n\nTest data: %r' % (scriptSig, scriptPubKey, comment, err, test_case))
                continue

            if expected_result != 'OK':
                self.fail('Expected %r to fail (%s)' % (test_case, expected_result))

    def test_script_bitcoinconsensus(self) -> None:
        try:
            handle = load_bitcoinconsensus_library()
        except ImportError:
            warnings.warn("libbitcoinconsensus library is not avaliable, not testing bitcoinconsensus module")
            return

        def do_test_bicoinconsensus(handle: Optional[ctypes.CDLL]) -> None:
            for t in load_test_vectors('script_tests.json', skip_fixme=False):
                (scriptSig, scriptPubKey, witness, nValue,
                 flags, expected_result, comment, test_case) = t
                (txCredit, txSpend) = self.create_test_txs(scriptSig, scriptPubKey, witness, nValue)

                libconsensus_flags = (flags & BITCOINCONSENSUS_ACCEPTED_FLAGS)
                if flags != libconsensus_flags:
                    continue

                try:
                    ConsensusVerifyScript(scriptSig, scriptPubKey, txSpend, 0,
                                          libconsensus_flags, amount=nValue,
                                          witness=witness,
                                          consensus_library_hanlde=handle)
                except ValidationError as err:
                    if expected_result == 'OK':
                        self.fail('Script FAILED: %r %r %r with exception %r\n\nTest data: %r' % (scriptSig, scriptPubKey, comment, err, test_case))
                    continue

                if expected_result != 'OK':
                    self.fail('Expected %r to fail (%s)' % (test_case, expected_result))

        do_test_bicoinconsensus(handle)  # test with supplied handle
        do_test_bicoinconsensus(None)  # test with default-loaded handle

    def test_p2sh_redeemscript(self) -> None:
        def T(required: int, total: int, alt_total: Optional[int] = None) -> None:
            amount = 10000
            keys = [CKey.from_secret_bytes(os.urandom(32))
                    for _ in range(total)]
            pubkeys = [k.pub for k in keys]

            if alt_total is not None:
                total = alt_total  # for assertRaises checks

            redeem_script = standard_multisig_redeem_script(
                total=total, required=required, pubkeys=pubkeys)

            # Test with P2SH

            scriptPubKey = redeem_script.to_p2sh_scriptPubKey()

            (_, tx) = self.create_test_txs(CScript(), scriptPubKey,
                                           CScriptWitness([]), amount)

            tx = tx.to_mutable()

            sighash = redeem_script.sighash(tx, 0, SIGHASH_ALL,
                                            amount=amount,
                                            sigversion=SIGVERSION_BASE)

            sigs = [k.sign(sighash) + bytes([SIGHASH_ALL])
                    for k in keys[:required]]

            tx.vin[0].scriptSig = CScript(
                standard_multisig_witness_stack(sigs, redeem_script))

            VerifyScript(tx.vin[0].scriptSig, scriptPubKey, tx, 0,
                         (SCRIPT_VERIFY_P2SH,))

            # Test with P2WSH

            scriptPubKey = redeem_script.to_p2wsh_scriptPubKey()

            (_, tx) = self.create_test_txs(CScript(), scriptPubKey,
                                           CScriptWitness([]), amount)

            tx = tx.to_mutable()

            sighash = redeem_script.sighash(tx, 0, SIGHASH_ALL,
                                            amount=amount,
                                            sigversion=SIGVERSION_WITNESS_V0)

            sigs = [k.sign(sighash) + bytes([SIGHASH_ALL])
                    for k in keys[:required]]

            witness_stack = standard_multisig_witness_stack(sigs, redeem_script)
            tx.vin[0].scriptSig = CScript([])
            tx.wit.vtxinwit[0] = CTxInWitness(CScriptWitness(witness_stack)).to_mutable()

            VerifyScript(tx.vin[0].scriptSig, scriptPubKey, tx, 0,
                         flags=(SCRIPT_VERIFY_WITNESS, SCRIPT_VERIFY_P2SH),
                         amount=amount,
                         witness=tx.wit.vtxinwit[0].scriptWitness)

            # Test with P2SH_P2WSH

            scriptPubKey = redeem_script.to_p2wsh_scriptPubKey()

            (_, tx) = self.create_test_txs(CScript(), scriptPubKey,
                                           CScriptWitness([]), amount)

            tx = tx.to_mutable()

            sighash = redeem_script.sighash(tx, 0, SIGHASH_ALL,
                                            amount=amount,
                                            sigversion=SIGVERSION_WITNESS_V0)

            sigs = [k.sign(sighash) + bytes([SIGHASH_ALL])
                    for k in keys[:required]]

            witness_stack = standard_multisig_witness_stack(sigs, redeem_script)
            tx.vin[0].scriptSig = CScript([scriptPubKey])
            tx.wit.vtxinwit[0] = CTxInWitness(CScriptWitness(witness_stack)).to_mutable()

            VerifyScript(tx.vin[0].scriptSig,
                         scriptPubKey.to_p2sh_scriptPubKey(), tx, 0,
                         flags=(SCRIPT_VERIFY_WITNESS, SCRIPT_VERIFY_P2SH),
                         amount=amount,
                         witness=tx.wit.vtxinwit[0].scriptWitness)

        T(1, 3)
        T(2, 12)
        T(10, 13)
        T(11, 15)
        T(15, 15)

        with self.assertRaises(ValueError):
            T(1, 1)
            T(2, 1)
            T(1, 16)
            T(11, 11, alt_total=12)
            T(1, 3, alt_total=2)
