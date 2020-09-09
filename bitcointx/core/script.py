# Copyright (C) 2012-2015 The python-bitcoinlib developers
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

# pylama:ignore=E501,E261,E231,E221,C901

"""Scripts

Functionality to build scripts, as well as SignatureHash(). Script evaluation
is in bitcointx.core.scripteval
"""

import struct
import hashlib
from io import BytesIO
from abc import abstractmethod
from typing import (
    List, Tuple, Dict, Union, Iterable, Sequence, Optional, TypeVar, Type,
    Generator, Iterator, Any, Callable, cast
)

import bitcointx.core
import bitcointx.core.key
import bitcointx.core._bignum

from .serialize import (
    VarIntSerializer, BytesSerializer, ImmutableSerializable, ByteStream_Type
)

from ..util import (
    no_bool_use_as_property, ClassMappingDispatcher, activate_class_dispatcher,
    ensure_isinstance
)

MAX_SCRIPT_SIZE = 10000
MAX_SCRIPT_ELEMENT_SIZE = 520
MAX_STANDARD_P2WSH_SCRIPT_SIZE = 3600
MAX_SCRIPT_OPCODES = 201

# CScriptOp is a subclass of int, and CPubKey is a subclass of bytes,
# but is incuded here for documentaion purposes - what we expect in a script.
ScriptElement_Type = Union['CScriptOp', 'bitcointx.core.key.CPubKey',
                           int, bytes, bytearray]


T_CScript = TypeVar('T_CScript', bound='CScript')
T_CScriptWitness = TypeVar('T_CScriptWitness', bound='CScriptWitness')


# By using an int-derived class for SIGVERSION_*
# instead of enum, we allow the code that define their own sighash
# functions for to extend the list of accepted SIGVERSION_* values,
# without the need to redefine the enum (subclassing enum cannot add members)
class SIGVERSION_Type(int):
    ...


SIGVERSION_BASE: SIGVERSION_Type = SIGVERSION_Type(0)
SIGVERSION_WITNESS_V0: SIGVERSION_Type = SIGVERSION_Type(1)


T_int = TypeVar('T_int', bound=int)


class SIGHASH_Bitflag_Type(int):
    def __or__(self, other: T_int) -> T_int:
        return cast(T_int, super().__or__(other))


SIGHASH_ANYONECANPAY: SIGHASH_Bitflag_Type = SIGHASH_Bitflag_Type(0x80)

T_SIGHASH_Type = TypeVar('T_SIGHASH_Type', bound='SIGHASH_Type')


class SIGHASH_Type(int):

    _known_values: Tuple[int, ...] = ()
    _known_bitflags: SIGHASH_Bitflag_Type = SIGHASH_ANYONECANPAY

    def __init__(self, _value: int) -> None:
        super().__init__()
        if not (self & ~self._known_bitflags) in self._known_values:
            raise ValueError(
                f'a supported SIGHASH type value must be supplied, but '
                f'{self} is not a supported SIGHASH type')

    @classmethod
    def register_type(cls: Type[T_SIGHASH_Type], value: int) -> T_SIGHASH_Type:
        ensure_isinstance(value, int, 'sighash type to register')
        if value in cls._known_values:
            raise ValueError(f'value {value} is already registered')
        cls._known_values = tuple(list(cls._known_values) + [value])
        return cls(value)

    # The type of 'other' is intentionally incompatible wit supertype 'int'
    # because we do not want that or-ing with anything but bitflag type
    # to produce SIGHASH_Type result.
    def __or__(self,  # type: ignore
               other: 'SIGHASH_Bitflag_Type'
               ) -> 'SIGHASH_Type':
        if self != int(SIGHASH_ANYONECANPAY) and other != SIGHASH_ANYONECANPAY:
            raise ValueError(
                'combining SIGHASH_* values only make sense with '
                'SIGHASH_ANYONECANPAY, other values are not a bit flags')
        return SIGHASH_Type(super().__or__(other))


SIGHASH_ALL: SIGHASH_Type = SIGHASH_Type.register_type(1)
SIGHASH_NONE: SIGHASH_Type = SIGHASH_Type.register_type(2)
SIGHASH_SINGLE: SIGHASH_Type = SIGHASH_Type.register_type(3)

# (partial) comment from Bitcoin Core IsStandardTx() function:
# Biggest 'standard' txin is a 15-of-15 P2SH multisig with compressed
# keys (remember the 520 byte limit on redeemScript size). That works
# out to a (15*(33+1))+3=513 byte redeemScript
MAX_P2SH_MULTISIG_PUBKEYS = 15

OPCODE_NAMES: Dict['CScriptOp', str] = {}

_opcode_instances: List['CScriptOp'] = []


class ScriptCoinClassDispatcher(ClassMappingDispatcher, identity='script'):
    ...


class ScriptCoinClass(metaclass=ScriptCoinClassDispatcher):
    ...


class ScriptBitcoinClassDispatcher(ScriptCoinClassDispatcher):
    ...


class ScriptBitcoinClass(ScriptCoinClass, metaclass=ScriptBitcoinClassDispatcher):
    ...


class CScriptOp(int):
    """A single script opcode"""
    __slots__: List[str] = []

    @staticmethod
    def encode_op_pushdata(d: Union[bytes, bytearray]) -> bytes:
        """Encode a PUSHDATA op, returning bytes"""
        if len(d) < 0x4c:
            return b'' + bytes([len(d)]) + d # OP_PUSHDATA
        elif len(d) <= 0xff:
            return b'\x4c' + bytes([len(d)]) + d # OP_PUSHDATA1
        elif len(d) <= 0xffff:
            return b'\x4d' + struct.pack(b'<H', len(d)) + d # OP_PUSHDATA2
        elif len(d) <= 0xffffffff:
            return b'\x4e' + struct.pack(b'<I', len(d)) + d # OP_PUSHDATA4
        else:
            raise ValueError("Data too long to encode in a PUSHDATA op")

    @staticmethod
    def encode_op_n(n: int) -> 'CScriptOp':
        """Encode a small integer op, returning an opcode"""
        if not (0 <= n <= 16):
            raise ValueError('Integer must be in range 0 <= n <= 16, got %d' % n)

        if n == 0:
            return OP_0
        else:
            return CScriptOp(OP_1 + n-1)

    def decode_op_n(self) -> int:
        """Decode a small integer opcode, returning an integer"""
        if self == OP_0:
            return 0

        if not (self == OP_0 or OP_1 <= self <= OP_16):
            raise ValueError('op %r is not an OP_N' % self)

        return int(self - OP_1+1)

    @no_bool_use_as_property
    def is_small_int(self) -> bool:
        """Return true if the op pushes a small integer to the stack"""
        if 0x51 <= self <= 0x60 or self == 0:
            return True
        else:
            return False

    def __str__(self) -> str:
        return repr(self)

    def __repr__(self) -> str:
        if self in OPCODE_NAMES:
            return OPCODE_NAMES[self]
        else:
            return 'CScriptOp(0x%x)' % self

    def __new__(cls, n: int) -> 'CScriptOp':
        try:
            return _opcode_instances[n]
        except IndexError:
            assert len(_opcode_instances) == n
            # mypy cannot handle arguments to `bytes.__new__()` at the moment,
            # issue: https://github.com/python/typeshed/issues/2630
            # apparently it can't handle args to `int.__new__()`, too.
            _opcode_instances.append(super().__new__(cls, n))  # type: ignore
            return _opcode_instances[n]


# Populate opcode instance table
for n in range(0xff+1):
    CScriptOp(n)


# push value
OP_0 = CScriptOp(0x00)
OP_FALSE = OP_0
OP_PUSHDATA1 = CScriptOp(0x4c)
OP_PUSHDATA2 = CScriptOp(0x4d)
OP_PUSHDATA4 = CScriptOp(0x4e)
OP_1NEGATE = CScriptOp(0x4f)
OP_RESERVED = CScriptOp(0x50)
OP_1 = CScriptOp(0x51)
OP_TRUE = OP_1
OP_2 = CScriptOp(0x52)
OP_3 = CScriptOp(0x53)
OP_4 = CScriptOp(0x54)
OP_5 = CScriptOp(0x55)
OP_6 = CScriptOp(0x56)
OP_7 = CScriptOp(0x57)
OP_8 = CScriptOp(0x58)
OP_9 = CScriptOp(0x59)
OP_10 = CScriptOp(0x5a)
OP_11 = CScriptOp(0x5b)
OP_12 = CScriptOp(0x5c)
OP_13 = CScriptOp(0x5d)
OP_14 = CScriptOp(0x5e)
OP_15 = CScriptOp(0x5f)
OP_16 = CScriptOp(0x60)

# control
OP_NOP = CScriptOp(0x61)
OP_VER = CScriptOp(0x62)
OP_IF = CScriptOp(0x63)
OP_NOTIF = CScriptOp(0x64)
OP_VERIF = CScriptOp(0x65)
OP_VERNOTIF = CScriptOp(0x66)
OP_ELSE = CScriptOp(0x67)
OP_ENDIF = CScriptOp(0x68)
OP_VERIFY = CScriptOp(0x69)
OP_RETURN = CScriptOp(0x6a)

# stack ops
OP_TOALTSTACK = CScriptOp(0x6b)
OP_FROMALTSTACK = CScriptOp(0x6c)
OP_2DROP = CScriptOp(0x6d)
OP_2DUP = CScriptOp(0x6e)
OP_3DUP = CScriptOp(0x6f)
OP_2OVER = CScriptOp(0x70)
OP_2ROT = CScriptOp(0x71)
OP_2SWAP = CScriptOp(0x72)
OP_IFDUP = CScriptOp(0x73)
OP_DEPTH = CScriptOp(0x74)
OP_DROP = CScriptOp(0x75)
OP_DUP = CScriptOp(0x76)
OP_NIP = CScriptOp(0x77)
OP_OVER = CScriptOp(0x78)
OP_PICK = CScriptOp(0x79)
OP_ROLL = CScriptOp(0x7a)
OP_ROT = CScriptOp(0x7b)
OP_SWAP = CScriptOp(0x7c)
OP_TUCK = CScriptOp(0x7d)

# splice ops
OP_CAT = CScriptOp(0x7e)
OP_SUBSTR = CScriptOp(0x7f)
OP_LEFT = CScriptOp(0x80)
OP_RIGHT = CScriptOp(0x81)
OP_SIZE = CScriptOp(0x82)

# bit logic
OP_INVERT = CScriptOp(0x83)
OP_AND = CScriptOp(0x84)
OP_OR = CScriptOp(0x85)
OP_XOR = CScriptOp(0x86)
OP_EQUAL = CScriptOp(0x87)
OP_EQUALVERIFY = CScriptOp(0x88)
OP_RESERVED1 = CScriptOp(0x89)
OP_RESERVED2 = CScriptOp(0x8a)

# numeric
OP_1ADD = CScriptOp(0x8b)
OP_1SUB = CScriptOp(0x8c)
OP_2MUL = CScriptOp(0x8d)
OP_2DIV = CScriptOp(0x8e)
OP_NEGATE = CScriptOp(0x8f)
OP_ABS = CScriptOp(0x90)
OP_NOT = CScriptOp(0x91)
OP_0NOTEQUAL = CScriptOp(0x92)

OP_ADD = CScriptOp(0x93)
OP_SUB = CScriptOp(0x94)
OP_MUL = CScriptOp(0x95)
OP_DIV = CScriptOp(0x96)
OP_MOD = CScriptOp(0x97)
OP_LSHIFT = CScriptOp(0x98)
OP_RSHIFT = CScriptOp(0x99)

OP_BOOLAND = CScriptOp(0x9a)
OP_BOOLOR = CScriptOp(0x9b)
OP_NUMEQUAL = CScriptOp(0x9c)
OP_NUMEQUALVERIFY = CScriptOp(0x9d)
OP_NUMNOTEQUAL = CScriptOp(0x9e)
OP_LESSTHAN = CScriptOp(0x9f)
OP_GREATERTHAN = CScriptOp(0xa0)
OP_LESSTHANOREQUAL = CScriptOp(0xa1)
OP_GREATERTHANOREQUAL = CScriptOp(0xa2)
OP_MIN = CScriptOp(0xa3)
OP_MAX = CScriptOp(0xa4)

OP_WITHIN = CScriptOp(0xa5)

# crypto
OP_RIPEMD160 = CScriptOp(0xa6)
OP_SHA1 = CScriptOp(0xa7)
OP_SHA256 = CScriptOp(0xa8)
OP_HASH160 = CScriptOp(0xa9)
OP_HASH256 = CScriptOp(0xaa)
OP_CODESEPARATOR = CScriptOp(0xab)
OP_CHECKSIG = CScriptOp(0xac)
OP_CHECKSIGVERIFY = CScriptOp(0xad)
OP_CHECKMULTISIG = CScriptOp(0xae)
OP_CHECKMULTISIGVERIFY = CScriptOp(0xaf)

# expansion
OP_NOP1 = CScriptOp(0xb0)
OP_NOP2 = CScriptOp(0xb1)
OP_CHECKLOCKTIMEVERIFY = OP_NOP2
OP_NOP3 = CScriptOp(0xb2)
OP_CHECKSEQUENCEVERIFY = OP_NOP3
OP_NOP4 = CScriptOp(0xb3)
OP_NOP5 = CScriptOp(0xb4)
OP_NOP6 = CScriptOp(0xb5)
OP_NOP7 = CScriptOp(0xb6)
OP_NOP8 = CScriptOp(0xb7)
OP_NOP9 = CScriptOp(0xb8)
OP_NOP10 = CScriptOp(0xb9)

# template matching params
OP_SMALLINTEGER = CScriptOp(0xfa)
OP_PUBKEYS = CScriptOp(0xfb)
OP_PUBKEYHASH = CScriptOp(0xfd)
OP_PUBKEY = CScriptOp(0xfe)

OP_INVALIDOPCODE = CScriptOp(0xff)

OPCODE_NAMES.update({
    OP_0: 'OP_0',
    OP_PUSHDATA1: 'OP_PUSHDATA1',
    OP_PUSHDATA2: 'OP_PUSHDATA2',
    OP_PUSHDATA4: 'OP_PUSHDATA4',
    OP_1NEGATE: 'OP_1NEGATE',
    OP_RESERVED: 'OP_RESERVED',
    OP_1: 'OP_1',
    OP_2: 'OP_2',
    OP_3: 'OP_3',
    OP_4: 'OP_4',
    OP_5: 'OP_5',
    OP_6: 'OP_6',
    OP_7: 'OP_7',
    OP_8: 'OP_8',
    OP_9: 'OP_9',
    OP_10: 'OP_10',
    OP_11: 'OP_11',
    OP_12: 'OP_12',
    OP_13: 'OP_13',
    OP_14: 'OP_14',
    OP_15: 'OP_15',
    OP_16: 'OP_16',
    OP_NOP: 'OP_NOP',
    OP_VER: 'OP_VER',
    OP_IF: 'OP_IF',
    OP_NOTIF: 'OP_NOTIF',
    OP_VERIF: 'OP_VERIF',
    OP_VERNOTIF: 'OP_VERNOTIF',
    OP_ELSE: 'OP_ELSE',
    OP_ENDIF: 'OP_ENDIF',
    OP_VERIFY: 'OP_VERIFY',
    OP_RETURN: 'OP_RETURN',
    OP_TOALTSTACK: 'OP_TOALTSTACK',
    OP_FROMALTSTACK: 'OP_FROMALTSTACK',
    OP_2DROP: 'OP_2DROP',
    OP_2DUP: 'OP_2DUP',
    OP_3DUP: 'OP_3DUP',
    OP_2OVER: 'OP_2OVER',
    OP_2ROT: 'OP_2ROT',
    OP_2SWAP: 'OP_2SWAP',
    OP_IFDUP: 'OP_IFDUP',
    OP_DEPTH: 'OP_DEPTH',
    OP_DROP: 'OP_DROP',
    OP_DUP: 'OP_DUP',
    OP_NIP: 'OP_NIP',
    OP_OVER: 'OP_OVER',
    OP_PICK: 'OP_PICK',
    OP_ROLL: 'OP_ROLL',
    OP_ROT: 'OP_ROT',
    OP_SWAP: 'OP_SWAP',
    OP_TUCK: 'OP_TUCK',
    OP_CAT: 'OP_CAT',
    OP_SUBSTR: 'OP_SUBSTR',
    OP_LEFT: 'OP_LEFT',
    OP_RIGHT: 'OP_RIGHT',
    OP_SIZE: 'OP_SIZE',
    OP_INVERT: 'OP_INVERT',
    OP_AND: 'OP_AND',
    OP_OR: 'OP_OR',
    OP_XOR: 'OP_XOR',
    OP_EQUAL: 'OP_EQUAL',
    OP_EQUALVERIFY: 'OP_EQUALVERIFY',
    OP_RESERVED1: 'OP_RESERVED1',
    OP_RESERVED2: 'OP_RESERVED2',
    OP_1ADD: 'OP_1ADD',
    OP_1SUB: 'OP_1SUB',
    OP_2MUL: 'OP_2MUL',
    OP_2DIV: 'OP_2DIV',
    OP_NEGATE: 'OP_NEGATE',
    OP_ABS: 'OP_ABS',
    OP_NOT: 'OP_NOT',
    OP_0NOTEQUAL: 'OP_0NOTEQUAL',
    OP_ADD: 'OP_ADD',
    OP_SUB: 'OP_SUB',
    OP_MUL: 'OP_MUL',
    OP_DIV: 'OP_DIV',
    OP_MOD: 'OP_MOD',
    OP_LSHIFT: 'OP_LSHIFT',
    OP_RSHIFT: 'OP_RSHIFT',
    OP_BOOLAND: 'OP_BOOLAND',
    OP_BOOLOR: 'OP_BOOLOR',
    OP_NUMEQUAL: 'OP_NUMEQUAL',
    OP_NUMEQUALVERIFY: 'OP_NUMEQUALVERIFY',
    OP_NUMNOTEQUAL: 'OP_NUMNOTEQUAL',
    OP_LESSTHAN: 'OP_LESSTHAN',
    OP_GREATERTHAN: 'OP_GREATERTHAN',
    OP_LESSTHANOREQUAL: 'OP_LESSTHANOREQUAL',
    OP_GREATERTHANOREQUAL: 'OP_GREATERTHANOREQUAL',
    OP_MIN: 'OP_MIN',
    OP_MAX: 'OP_MAX',
    OP_WITHIN: 'OP_WITHIN',
    OP_RIPEMD160: 'OP_RIPEMD160',
    OP_SHA1: 'OP_SHA1',
    OP_SHA256: 'OP_SHA256',
    OP_HASH160: 'OP_HASH160',
    OP_HASH256: 'OP_HASH256',
    OP_CODESEPARATOR: 'OP_CODESEPARATOR',
    OP_CHECKSIG: 'OP_CHECKSIG',
    OP_CHECKSIGVERIFY: 'OP_CHECKSIGVERIFY',
    OP_CHECKMULTISIG: 'OP_CHECKMULTISIG',
    OP_CHECKMULTISIGVERIFY: 'OP_CHECKMULTISIGVERIFY',
    OP_NOP1: 'OP_NOP1',
    # OP_NOP2: 'OP_NOP2', # replaced by OP_CHECKLOCKTIMEVERIFY
    OP_CHECKLOCKTIMEVERIFY: 'OP_CHECKLOCKTIMEVERIFY',
    # OP_NOP3: 'OP_NOP3', # replaced by OP_CHECKSEQUENCEVERIFY
    OP_CHECKSEQUENCEVERIFY: 'OP_CHECKSEQUENCEVERIFY',
    OP_NOP4: 'OP_NOP4',
    OP_NOP5: 'OP_NOP5',
    OP_NOP6: 'OP_NOP6',
    OP_NOP7: 'OP_NOP7',
    OP_NOP8: 'OP_NOP8',
    OP_NOP9: 'OP_NOP9',
    OP_NOP10: 'OP_NOP10',
    OP_SMALLINTEGER: 'OP_SMALLINTEGER',
    OP_PUBKEYS: 'OP_PUBKEYS',
    OP_PUBKEYHASH: 'OP_PUBKEYHASH',
    OP_PUBKEY: 'OP_PUBKEY',
    OP_INVALIDOPCODE: 'OP_INVALIDOPCODE',
})

OPCODES_BY_NAME = {
    'OP_0': OP_0,
    'OP_FALSE': OP_0,
    'OP_PUSHDATA1': OP_PUSHDATA1,
    'OP_PUSHDATA2': OP_PUSHDATA2,
    'OP_PUSHDATA4': OP_PUSHDATA4,
    'OP_1NEGATE': OP_1NEGATE,
    'OP_RESERVED': OP_RESERVED,
    'OP_1': OP_1,
    'OP_TRUE': OP_1,
    'OP_2': OP_2,
    'OP_3': OP_3,
    'OP_4': OP_4,
    'OP_5': OP_5,
    'OP_6': OP_6,
    'OP_7': OP_7,
    'OP_8': OP_8,
    'OP_9': OP_9,
    'OP_10': OP_10,
    'OP_11': OP_11,
    'OP_12': OP_12,
    'OP_13': OP_13,
    'OP_14': OP_14,
    'OP_15': OP_15,
    'OP_16': OP_16,
    'OP_NOP': OP_NOP,
    'OP_VER': OP_VER,
    'OP_IF': OP_IF,
    'OP_NOTIF': OP_NOTIF,
    'OP_VERIF': OP_VERIF,
    'OP_VERNOTIF': OP_VERNOTIF,
    'OP_ELSE': OP_ELSE,
    'OP_ENDIF': OP_ENDIF,
    'OP_VERIFY': OP_VERIFY,
    'OP_RETURN': OP_RETURN,
    'OP_TOALTSTACK': OP_TOALTSTACK,
    'OP_FROMALTSTACK': OP_FROMALTSTACK,
    'OP_2DROP': OP_2DROP,
    'OP_2DUP': OP_2DUP,
    'OP_3DUP': OP_3DUP,
    'OP_2OVER': OP_2OVER,
    'OP_2ROT': OP_2ROT,
    'OP_2SWAP': OP_2SWAP,
    'OP_IFDUP': OP_IFDUP,
    'OP_DEPTH': OP_DEPTH,
    'OP_DROP': OP_DROP,
    'OP_DUP': OP_DUP,
    'OP_NIP': OP_NIP,
    'OP_OVER': OP_OVER,
    'OP_PICK': OP_PICK,
    'OP_ROLL': OP_ROLL,
    'OP_ROT': OP_ROT,
    'OP_SWAP': OP_SWAP,
    'OP_TUCK': OP_TUCK,
    'OP_CAT': OP_CAT,
    'OP_SUBSTR': OP_SUBSTR,
    'OP_LEFT': OP_LEFT,
    'OP_RIGHT': OP_RIGHT,
    'OP_SIZE': OP_SIZE,
    'OP_INVERT': OP_INVERT,
    'OP_AND': OP_AND,
    'OP_OR': OP_OR,
    'OP_XOR': OP_XOR,
    'OP_EQUAL': OP_EQUAL,
    'OP_EQUALVERIFY': OP_EQUALVERIFY,
    'OP_RESERVED1': OP_RESERVED1,
    'OP_RESERVED2': OP_RESERVED2,
    'OP_1ADD': OP_1ADD,
    'OP_1SUB': OP_1SUB,
    'OP_2MUL': OP_2MUL,
    'OP_2DIV': OP_2DIV,
    'OP_NEGATE': OP_NEGATE,
    'OP_ABS': OP_ABS,
    'OP_NOT': OP_NOT,
    'OP_0NOTEQUAL': OP_0NOTEQUAL,
    'OP_ADD': OP_ADD,
    'OP_SUB': OP_SUB,
    'OP_MUL': OP_MUL,
    'OP_DIV': OP_DIV,
    'OP_MOD': OP_MOD,
    'OP_LSHIFT': OP_LSHIFT,
    'OP_RSHIFT': OP_RSHIFT,
    'OP_BOOLAND': OP_BOOLAND,
    'OP_BOOLOR': OP_BOOLOR,
    'OP_NUMEQUAL': OP_NUMEQUAL,
    'OP_NUMEQUALVERIFY': OP_NUMEQUALVERIFY,
    'OP_NUMNOTEQUAL': OP_NUMNOTEQUAL,
    'OP_LESSTHAN': OP_LESSTHAN,
    'OP_GREATERTHAN': OP_GREATERTHAN,
    'OP_LESSTHANOREQUAL': OP_LESSTHANOREQUAL,
    'OP_GREATERTHANOREQUAL': OP_GREATERTHANOREQUAL,
    'OP_MIN': OP_MIN,
    'OP_MAX': OP_MAX,
    'OP_WITHIN': OP_WITHIN,
    'OP_RIPEMD160': OP_RIPEMD160,
    'OP_SHA1': OP_SHA1,
    'OP_SHA256': OP_SHA256,
    'OP_HASH160': OP_HASH160,
    'OP_HASH256': OP_HASH256,
    'OP_CODESEPARATOR': OP_CODESEPARATOR,
    'OP_CHECKSIG': OP_CHECKSIG,
    'OP_CHECKSIGVERIFY': OP_CHECKSIGVERIFY,
    'OP_CHECKMULTISIG': OP_CHECKMULTISIG,
    'OP_CHECKMULTISIGVERIFY': OP_CHECKMULTISIGVERIFY,
    'OP_NOP1': OP_NOP1,
    'OP_NOP2': OP_NOP2,
    'OP_CHECKLOCKTIMEVERIFY': OP_CHECKLOCKTIMEVERIFY,
    'OP_NOP3': OP_NOP3,
    'OP_CHECKSEQUENCEVERIFY': OP_CHECKSEQUENCEVERIFY,
    'OP_NOP4': OP_NOP4,
    'OP_NOP5': OP_NOP5,
    'OP_NOP6': OP_NOP6,
    'OP_NOP7': OP_NOP7,
    'OP_NOP8': OP_NOP8,
    'OP_NOP9': OP_NOP9,
    'OP_NOP10': OP_NOP10,
    'OP_SMALLINTEGER': OP_SMALLINTEGER,
    'OP_PUBKEYS': OP_PUBKEYS,
    'OP_PUBKEYHASH': OP_PUBKEYHASH,
    'OP_PUBKEY': OP_PUBKEY,
}

# Invalid even when occuring in an unexecuted OP_IF branch due to either being
# disabled, or never having been implemented.
DISABLED_OPCODES = frozenset((OP_VERIF, OP_VERNOTIF,
                              OP_CAT, OP_SUBSTR, OP_LEFT, OP_RIGHT, OP_INVERT, OP_AND,
                              OP_OR, OP_XOR, OP_2MUL, OP_2DIV, OP_MUL, OP_DIV, OP_MOD,
                              OP_LSHIFT, OP_RSHIFT))


class DATA(bytes):
    """A class that can be used to prevent accidental use of non-data
    elements in the script where data elemets were expected. For example,
    the code `CScript([var])` does not communicate to the reader if `var`
    is expected to be just data, or a number, or an opcode.
    with CScript([DATA(var)]), this is communicated clearly, and will
    raise TypeError if var is not bytes or bytearray instance."""

    def __new__(cls, data: Union[bytes, bytearray]) -> 'DATA':
        if not isinstance(data, (bytes, bytearray)):
            raise TypeError(
                'DATA can only accept bytes or bytearray instance')

        # mypy cannot handle arguments to `bytes.__new__()` at the moment,
        # issue: https://github.com/python/typeshed/issues/2630
        return super().__new__(cls, data)  # type: ignore


class NUMBER(int):
    """A class that can be used to prevent accidental use of non-numeric
    elements in the script where nmeric elemets were expected. For example,
    the code `CScript([var])` does not communicate to the reader if `var`
    is expected to be just data, or a number, or an opcode.
    with CScript([NUMBER(var)]), this is communicated clearly, and will
    raise TypeError if var is not an instance of int class, and not
    and instance of CScriptOp (special case needed because CScriptOp is
    a subclas of int, but there are special OPCODE guard for it"""

    def __new__(cls, num: int) -> 'NUMBER':
        if not isinstance(num, int):
            raise TypeError(
                'NUMBER can only accept values that are instance of '
                'int class (except CScriptOp)')

        if isinstance(num, CScriptOp):
            raise TypeError('NUMBER can not accept CScriptOp instance')

        # mypy cannot handle arguments to `bytes.__new__()` at the moment,
        # issue: https://github.com/python/typeshed/issues/2630
        # apparently it can't handle args to `int.__new__()`, too.
        return super().__new__(cls, num)  # type: ignore


def OPCODE(op: CScriptOp) -> CScriptOp:
    """A function that can be used to prevent accidental use of non-opcode
    elements in the script where opcode elemets were expected. For example,
    the code `CScript([var])` does not communicate to the reader if `var`
    is expected to be just data, or a number, or an opcode.
    with CScript([OPCODE(var)]), this is communicated clearly, and will
    raise TypeError if var is not an instance of CScriptOp
    Note that while DATA and NUMBER are classes, OPCODE cannot be a class,
    because if the op is some subclass of the CScriptOp, result of
    OPCODE(op) will not be the same, whereas with a function the same
    instance is just returned."""
    if not isinstance(op, CScriptOp):
        raise TypeError(
            'OPCODE can only accept instances of CScriptOp')
    return op


class CScriptInvalidError(Exception):
    """Base class for CScript exceptions"""
    pass


class CScriptTruncatedPushDataError(CScriptInvalidError):
    """Invalid pushdata due to truncation"""
    def __init__(self, msg: str, data: bytes):
        self.data = data
        super().__init__(msg)


class CScript(bytes, ScriptCoinClass, next_dispatch_final=True):
    """Serialized script

    A bytes subclass, so you can use this directly whenever bytes are accepted.
    Note that this means that indexing does *not* work - you'll get an index by
    byte rather than opcode. This format was chosen for efficiency so that the
    general case would not require creating a lot of little CScriptOp objects.

    iter(script) however does iterate by opcode.
    """
    @classmethod
    def __coerce_instance(cls, other: ScriptElement_Type) -> bytes:
        # Coerce other into bytes
        if isinstance(other, CScriptOp):
            other = bytes([other])
        elif isinstance(other, int):
            if 0 <= other <= 16:
                other = bytes([CScriptOp.encode_op_n(other)])
            elif other == -1:
                other = bytes([OP_1NEGATE])
            else:
                other = CScriptOp.encode_op_pushdata(
                    bitcointx.core._bignum.bn2vch(other))
        elif isinstance(other, (bytes, bytearray)):
            other = CScriptOp.encode_op_pushdata(other)
        else:
            raise TypeError("type '{}' cannot be represented in the script"
                            .format(type(other).__name__))
        return other

    def __add__(self: T_CScript, other: ScriptElement_Type) -> T_CScript:
        # Do the coercion outside of the try block so that errors in it are
        # noticed.
        other = self.__coerce_instance(other)

        try:
            # bytes.__add__ always returns bytes instances unfortunately
            return self.__class__(super().__add__(other))
        except TypeError:
            raise TypeError('Can not add a %r instance to a CScript' % other.__class__)

    # return type is deliberately None (incompatible with bytes),
    # because join makes no sense for a CScript()
    def join(self, iterable: Any) -> None:  # type: ignore
        # join makes no sense for a CScript()
        raise NotImplementedError

    def __new__(cls: Type[T_CScript],
                value: Iterable[ScriptElement_Type] = b''
                ) -> T_CScript:

        if isinstance(value, (bytes, bytearray)):
            # mypy cannot handle arguments to `bytes.__new__()` at the moment,
            # issue: https://github.com/python/typeshed/issues/2630
            return super().__new__(cls, value)  # type: ignore
        else:
            def coerce_iterable(iterable: Iterable[ScriptElement_Type]
                                ) -> Generator[bytes, None, None]:
                for instance in iterable:
                    yield cls.__coerce_instance(instance)

            # Annoyingly bytes.join() always
            # returns a bytes instance even when subclassed.

            # mypy cannot handle arguments to `bytes.__new__()` at the moment,
            # issue: https://github.com/python/typeshed/issues/2630
            return super().__new__(  # type: ignore
                cls, b''.join(coerce_iterable(value)))

    def raw_iter(self) -> Generator[Tuple[CScriptOp, Optional[bytes], int],
                                    None, None]:
        """Raw iteration

        Yields tuples of (opcode, data, sop_idx) so that the different possible
        PUSHDATA encodings can be accurately distinguished, as well as
        determining the exact opcode byte indexes. (sop_idx)
        """
        i = 0
        while i < len(self):
            sop_idx = i
            opcode = self[i]
            i += 1

            if opcode > OP_PUSHDATA4:
                yield (CScriptOp(opcode), None, sop_idx)
            else:
                datasize = None
                pushdata_type = None
                if opcode < OP_PUSHDATA1:
                    pushdata_type = 'PUSHDATA(%d)' % opcode
                    datasize = opcode

                elif opcode == OP_PUSHDATA1:
                    pushdata_type = 'PUSHDATA1'
                    if i >= len(self):
                        raise CScriptInvalidError('PUSHDATA1: missing data length')
                    datasize = self[i]
                    i += 1

                elif opcode == OP_PUSHDATA2:
                    pushdata_type = 'PUSHDATA2'
                    if i + 1 >= len(self):
                        raise CScriptInvalidError('PUSHDATA2: missing data length')
                    datasize = self[i] + (self[i+1] << 8)
                    i += 2

                elif opcode == OP_PUSHDATA4:
                    pushdata_type = 'PUSHDATA4'
                    if i + 3 >= len(self):
                        raise CScriptInvalidError('PUSHDATA4: missing data length')
                    datasize = self[i] + (self[i+1] << 8) + (self[i+2] << 16) + (self[i+3] << 24)
                    i += 4

                else:
                    assert False # shouldn't happen

                data = bytes(self[i:i+datasize])

                # Check for truncation
                if len(data) < datasize:
                    raise CScriptTruncatedPushDataError('%s: truncated data' % pushdata_type, data)

                i += datasize

                yield (CScriptOp(opcode), data, sop_idx)

    # This 'cooked' iteration is not compatible with supertype 'bytes',
    # thus we need this typing: ignore
    def __iter__(self) -> Generator[Union[CScriptOp, int, bytes],  # type: ignore
                                    None, None]:
        """'Cooked' iteration

        Returns either a CScriptOp instance, an integer, or bytes, as
        appropriate.

        See raw_iter() if you need to distinguish the different possible
        PUSHDATA encodings.
        """
        for (opcode, data, sop_idx) in self.raw_iter():
            if opcode == 0:
                yield 0
            elif data is not None:
                yield data
            else:
                opcode = CScriptOp(opcode)

                if opcode.is_small_int():
                    yield opcode.decode_op_n()
                else:
                    yield CScriptOp(opcode)

    def __repr__(self) -> str:
        # For Python3 compatibility add b before strings so testcases don't
        # need to change
        def _repr(o: Any) -> str:
            if isinstance(o, (bytes, bytearray)):
                return "x('%s')" % bitcointx.core.b2x(o)
            else:
                return repr(o)

        ops = []
        i = iter(self)
        while True:
            op = None
            try:
                op = _repr(next(i))
            except CScriptTruncatedPushDataError as err:
                op = '%s...<ERROR: %s>' % (_repr(err.data), err)
                break
            except CScriptInvalidError as err:
                op = '<ERROR: %s>' % err
                break
            except StopIteration:
                break
            finally:
                if op is not None:
                    ops.append(op)

        return "%s([%s])" % (self.__class__.__name__, ', '.join(ops))

    @no_bool_use_as_property
    def is_p2sh(self) -> bool:
        """Test if the script is a p2sh scriptPubKey

        Note that this test is consensus-critical.

        Note also that python-bitcointx does not aim to be
        fully consensus-compatible with current Bitcoin Core codebase
        """
        return (len(self) == 23 and
                self[0] == OP_HASH160 and
                self[1] == 0x14 and
                self[22] == OP_EQUAL)

    @no_bool_use_as_property
    def is_p2pkh(self) -> bool:
        """Test if the script is a p2pkh scriptPubKey"""
        return (len(self) == 25
                and self[0]  == OP_DUP
                and self[1]  == OP_HASH160
                and self[2]  == 0x14
                and self[23] == OP_EQUALVERIFY
                and self[24] == OP_CHECKSIG)

    def pubkey_hash(self) -> bytes:
        """get pubkey hash from p2pkh/p2wpkh scriptPubKey"""

        if self.is_witness_v0_keyhash():
            return self.witness_program()

        if self.is_p2pkh():
            return self[3:23]

        raise ValueError('not a p2pkh/p2wpkh scriptPubKey')

    @no_bool_use_as_property
    def is_witness_scriptpubkey(self) -> bool:
        """Returns true if this is a scriptpubkey signaling segregated witness data.

        A witness program is any valid CScript that consists of a 1-byte push opcode
        followed by a data push between 2 and 40 bytes.
        """
        size = len(self)
        if size < 4 or size > 42:
            return False

        if not CScriptOp(self[0]).is_small_int():
            return False

        if self[1] + 2 != size:
            return False

        return True

    def witness_version(self) -> int:
        """Returns the witness version on [0,16]. """
        if not self.is_witness_scriptpubkey():
            raise ValueError('not a witness scriptPubKey')
        return next(iter(self))

    def witness_program(self) -> bytes:
        """Returns the witness program"""
        if not self.is_witness_scriptpubkey():
            raise ValueError('not a witness scriptPubKey')
        return self[2:]

    @no_bool_use_as_property
    def is_witness_v0_keyhash(self) -> bool:
        """Returns true if this is a scriptpubkey for V0 P2WPKH. """
        return len(self) == 22 and self[0:2] == b'\x00\x14'

    @no_bool_use_as_property
    def is_witness_v0_nested_keyhash(self) -> bool:
        """Returns true if this is a scriptSig for V0 P2WPKH embedded in P2SH. """
        return len(self) == 23 and self[0:3] == b'\x16\x00\x14'

    @no_bool_use_as_property
    def is_witness_v0_scripthash(self) -> bool:
        """Returns true if this is a scriptpubkey for V0 P2WSH. """
        return len(self) == 34 and self[0:2] == b'\x00\x20'

    @no_bool_use_as_property
    def is_witness_v0_nested_scripthash(self) -> bool:
        """Returns true if this is a scriptSig for V0 P2WSH embedded in P2SH. """
        return len(self) == 35 and self[0:3] == b'\x22\x00\x20'

    @no_bool_use_as_property
    def is_push_only(self) -> bool:
        """Test if the script only contains pushdata ops

        Note that this test is consensus-critical.

        Scripts that contain invalid pushdata ops return False, matching the
        behavior in Bitcoin Core.
        """
        try:
            for (op, op_data, idx) in self.raw_iter():
                # Note how OP_RESERVED is considered a pushdata op.
                if op > OP_16:
                    return False

        except CScriptInvalidError:
            return False
        return True

    def has_canonical_pushes(self) -> bool:
        """Test if script only uses canonical pushes

        Not yet consensus critical; may be in the future.
        """
        try:
            for (op, data, idx) in self.raw_iter():
                if op > OP_16 or data is None:
                    continue

                elif op < OP_PUSHDATA1 and op > OP_0 and len(data) == 1 and data[0] <= 16:
                    # Could have used an OP_n code, rather than a 1-byte push.
                    return False

                elif op == OP_PUSHDATA1 and len(data) < OP_PUSHDATA1:
                    # Could have used a normal n-byte push, rather than OP_PUSHDATA1.
                    return False

                elif op == OP_PUSHDATA2 and len(data) <= 0xFF:
                    # Could have used a OP_PUSHDATA1.
                    return False

                elif op == OP_PUSHDATA4 and len(data) <= 0xFFFF:
                    # Could have used a OP_PUSHDATA2.
                    return False

        except CScriptInvalidError: # Invalid pushdata
            return False
        return True

    @no_bool_use_as_property
    def is_unspendable(self) -> bool:
        """Test if the script is provably unspendable"""
        return (len(self) > 0 and self[0] == OP_RETURN) or len(self) > MAX_SCRIPT_SIZE

    @no_bool_use_as_property
    def is_valid(self) -> bool:
        """Return True if the script is valid, False otherwise

        The script is valid if all PUSHDATA's are valid; invalid opcodes do not
        make is_valid() return False.
        """
        try:
            list(self)
        except CScriptInvalidError:
            return False
        return True

    def to_p2sh_scriptPubKey(self: T_CScript, checksize: bool = True
                             ) -> T_CScript:
        """Create P2SH scriptPubKey from this redeemScript

        That is, create the P2SH scriptPubKey that requires this script as a
        redeemScript to spend.

        checksize - Check if the redeemScript is larger than the 520-byte max
        pushdata limit; raise ValueError if limit exceeded.

        Since a >520-byte PUSHDATA makes EvalScript() fail, it's not actually
        possible to redeem P2SH outputs with redeem scripts >520 bytes.
        """
        if checksize and len(self) > MAX_SCRIPT_ELEMENT_SIZE:
            raise ValueError("redeemScript exceeds max allowed size; P2SH output would be unspendable")
        return self.__class__([OP_HASH160, bitcointx.core.Hash160(self), OP_EQUAL])

    def to_p2wsh_scriptPubKey(self: T_CScript, checksize: bool = True
                              ) -> T_CScript:
        """Create P2WSH scriptPubKey from this witnessScript

        That is, create the P2WSH scriptPubKey that requires this script as a
        witnessScript to spend.

        checksize - Check if the witnessScript is larger than the 3600-byte max
        script standardness limit; raise ValueError if limit exceeded.

        It is possible to have witnessScript up to 10000 bytes in size, if
        you are able to bypass transaction standardness checks (for example
        if you can supply your transaction directly to the miner and the miner
        would accept it), but generally you would not want to create
        non-standard transaction witnesses, as the nodes will not relay
        non-standard transactions.

        """
        if checksize and len(self) > MAX_STANDARD_P2WSH_SCRIPT_SIZE:
            raise ValueError(
                "witnessScript exceeds max size allowes for standard witness scripts; "
                "nodes will deny relaying the transaction containing this witnessScript in the txin witness")
        return self.__class__([0, hashlib.sha256(self).digest()])

    def GetSigOpCount(self, fAccurate: bool) -> int:
        """Get the SigOp count.

        fAccurate - Accurately count CHECKMULTISIG, see BIP16 for details.

        Note that this is consensus-critical.
        """
        n = 0
        lastOpcode = OP_INVALIDOPCODE
        for (opcode, data, sop_idx) in self.raw_iter():
            if opcode in (OP_CHECKSIG, OP_CHECKSIGVERIFY):
                n += 1
            elif opcode in (OP_CHECKMULTISIG, OP_CHECKMULTISIGVERIFY):
                if fAccurate and (OP_1 <= lastOpcode <= OP_16):
                    n += opcode.decode_op_n()
                else:
                    n += 20
            lastOpcode = opcode
        return n

    def sighash(self, txTo: 'bitcointx.core.CTransaction', inIdx: int,
                hashtype: SIGHASH_Type, amount: Optional[int] = None,
                sigversion: SIGVERSION_Type = SIGVERSION_BASE) -> bytes:
        """Calculate a signature hash

        'Cooked' version that checks if inIdx is out of bounds, and always
        checks that hashtype is a known hashtype value - this is *not*
        consensus-correct behavior, but is what you probably want for general
        wallet use.
        """

        # ensure this is supported type in case we got a simple int supplied
        # (when the caller do not check optional types)
        hashtype = SIGHASH_Type(hashtype)

        (h, err) = self.raw_sighash(txTo, inIdx, hashtype, amount=amount, sigversion=sigversion)
        if err is not None:
            raise ValueError(err)
        return h

    def raw_sighash(self, txTo: 'bitcointx.core.CTransaction', inIdx: int,
                    hashtype: int, amount: Optional[int] = None,
                    sigversion: SIGVERSION_Type = SIGVERSION_BASE
                    ) -> Tuple[bytes, Optional[str]]:
        """Consensus-correct SignatureHash

        Returns (hash, err) to precisely match the consensus-critical behavior of
        the SIGHASH_SINGLE bug. (inIdx is *not* checked for validity)

        Default implementation calls bitcoin-specific sighash function.

        If you're just writing wallet software you probably want sighash() method instead."""
        return RawBitcoinSignatureHash(self, txTo, inIdx, hashtype,
                                       amount=amount, sigversion=sigversion)


class CScriptWitness(ImmutableSerializable):
    """An encoding of the data elements on the initial stack for (segregated
        witness)
    """
    __slots__ = ['stack']

    stack: Tuple[bytes, ...]

    def __init__(self, stack: Iterable[ScriptElement_Type] = ()):
        stack_int_adjusted = (
            bitcointx.core._bignum.bn2vch(item)
            if (isinstance(item, int) and not isinstance(item, CScriptOp))
            else item
            for item in stack
        )
        coerced_stack = []
        for (opcode, data, sop_idx) in CScript(stack_int_adjusted).raw_iter():
            if data is not None:
                coerced_stack.append(data)
            else:
                coerced_stack.append(bytes([opcode]))
        object.__setattr__(self, 'stack', tuple(coerced_stack))

    def __len__(self) -> int:
        return len(self.stack)

    def __iter__(self) -> Iterator[bytes]:
        return iter(self.stack)

    def __repr__(self) -> str:
        return 'CScriptWitness([' + ','.join("x('%s')" % bitcointx.core.b2x(s) for s in self.stack) + '])'

    @no_bool_use_as_property
    def is_null(self) -> bool:
        return len(self.stack) == 0

    def __bool__(self) -> bool:
        return not self.is_null()

    @classmethod
    def stream_deserialize(cls: Type[T_CScriptWitness], f: ByteStream_Type,
                           **kwargs: Any) -> T_CScriptWitness:
        n = VarIntSerializer.stream_deserialize(f, **kwargs)
        stack = tuple(BytesSerializer.stream_deserialize(f, **kwargs)
                      for i in range(n))
        return cls(stack)

    def stream_serialize(self, f: ByteStream_Type, **kwargs: Any) -> None:
        VarIntSerializer.stream_serialize(len(self.stack), f, **kwargs)
        for s in self.stack:
            BytesSerializer.stream_serialize(s, f, **kwargs)


def FindAndDelete(script: T_CScript, sig: bytes) -> T_CScript:
    """Consensus critical, see FindAndDelete() in Satoshi codebase"""
    r = b''
    last_sop_idx = sop_idx = 0
    skip = True
    for (opcode, data, sop_idx) in script.raw_iter():
        if not skip:
            r += script[last_sop_idx:sop_idx]
        last_sop_idx = sop_idx
        if script[sop_idx:sop_idx + len(sig)] == sig:
            skip = True
        else:
            skip = False
    if not skip:
        r += script[last_sop_idx:]
    return script.__class__(r)


def IsLowDERSignature(sig: bytes) -> bool:
    """
    Loosely correlates with IsLowDERSignature() from script/interpreter.cpp
    Verifies that the S value in a DER signature is the lowest possible value.
    Used by BIP62 malleability fixes.
    """
    ensure_isinstance(sig, (bytes, bytearray), 'signature')
    length_r = sig[3]
    length_s = sig[5 + length_r]
    s_val = list(struct.unpack(str(length_s) + 'B', sig[6 + length_r:6 + length_r + length_s]))

    # If the S value is above the order of the curve divided by two, its
    # complement modulo the order could have been used instead, which is
    # one byte shorter when encoded correctly.
    max_mod_half_order = [
        0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0x5d,0x57,0x6e,0x73,0x57,0xa4,0x50,0x1d,
        0xdf,0xe9,0x2f,0x46,0x68,0x1b,0x20,0xa0]

    return CompareBigEndian(s_val, [0]) > 0 and \
        CompareBigEndian(s_val, max_mod_half_order) <= 0


def CompareBigEndian(c1: List[int], c2: List[int]) -> int:
    """
    Loosely matches CompareBigEndian() from eccryptoverify.cpp
    Compares two arrays of bytes, and returns a negative value if the first is
    less than the second, 0 if they're equal, and a positive value if the
    first is greater than the second.
    """
    c1 = list(c1)
    c2 = list(c2)

    # Adjust starting positions until remaining lengths of the two arrays match
    while len(c1) > len(c2):
        if c1.pop(0) > 0:
            return 1
    while len(c2) > len(c1):
        if c2.pop(0) > 0:
            return -1

    while len(c1) > 0:
        diff = c1.pop(0) - c2.pop(0)
        if diff != 0:
            return diff

    return 0


def RawBitcoinSignatureHash(script: CScript, txTo: 'bitcointx.core.CTransaction', inIdx: int,
                            hashtype: int, amount: Optional[int] = None,
                            sigversion: SIGVERSION_Type = SIGVERSION_BASE
                            ) -> Tuple[bytes, Optional[str]]:
    """Consensus-correct SignatureHash

    Returns (hash, err) to precisely match the consensus-critical behavior of
    the SIGHASH_SINGLE bug. (inIdx is *not* checked for validity)

    If you're just writing wallet software you probably want SignatureHash()
    instead.
    """
    if sigversion not in (SIGVERSION_BASE, SIGVERSION_WITNESS_V0):
        raise ValueError('unsupported sigversion')

    HASH_ONE = b'\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'

    if sigversion == SIGVERSION_WITNESS_V0:
        ensure_isinstance(amount, int, 'amount')
        hashPrevouts = b'\x00'*32
        hashSequence = b'\x00'*32
        hashOutputs  = b'\x00'*32

        if not (hashtype & SIGHASH_ANYONECANPAY):
            serialize_prevouts = bytes()
            for vin in txTo.vin:
                serialize_prevouts += vin.prevout.serialize()
            hashPrevouts = bitcointx.core.Hash(serialize_prevouts)

        if (not (hashtype & SIGHASH_ANYONECANPAY) and (hashtype & 0x1f) != SIGHASH_SINGLE and (hashtype & 0x1f) != SIGHASH_NONE):
            serialize_sequence = bytes()
            for vin in txTo.vin:
                serialize_sequence += struct.pack("<I", vin.nSequence)
            hashSequence = bitcointx.core.Hash(serialize_sequence)

        if ((hashtype & 0x1f) != SIGHASH_SINGLE and (hashtype & 0x1f) != SIGHASH_NONE):
            serialize_outputs = bytes()
            for vout in txTo.vout:
                serialize_outputs += vout.serialize()
            hashOutputs = bitcointx.core.Hash(serialize_outputs)
        elif ((hashtype & 0x1f) == SIGHASH_SINGLE and inIdx < len(txTo.vout)):
            serialize_outputs = txTo.vout[inIdx].serialize()
            hashOutputs = bitcointx.core.Hash(serialize_outputs)

        f = BytesIO()
        f.write(struct.pack("<i", txTo.nVersion))
        f.write(hashPrevouts)
        f.write(hashSequence)
        txTo.vin[inIdx].prevout.stream_serialize(f)
        BytesSerializer.stream_serialize(script, f)
        f.write(struct.pack("<q", amount))
        f.write(struct.pack("<I", txTo.vin[inIdx].nSequence))
        f.write(hashOutputs)
        f.write(struct.pack("<i", txTo.nLockTime))
        f.write(struct.pack("<i", hashtype))

        hash = bitcointx.core.Hash(f.getvalue())

        return (hash, None)

    assert sigversion == SIGVERSION_BASE

    if script.is_witness_scriptpubkey():
        raise ValueError(
            'segwit scriptpubkey supplied with sigversion=SIGVERION_BASE')

    if inIdx >= len(txTo.vin):
        return (HASH_ONE, "inIdx %d out of range (%d)" % (inIdx, len(txTo.vin)))

    txtmp = txTo.to_mutable()

    for txin in txtmp.vin:
        txin.scriptSig = CScript(b'')

    txtmp.vin[inIdx].scriptSig = FindAndDelete(
        script, script.__class__([OP_CODESEPARATOR]))

    if (hashtype & 0x1f) == SIGHASH_NONE:
        txtmp.vout = []

        for i in range(len(txtmp.vin)):
            if i != inIdx:
                txtmp.vin[i].nSequence = 0

    elif (hashtype & 0x1f) == SIGHASH_SINGLE:
        outIdx = inIdx
        if outIdx >= len(txtmp.vout):
            return (HASH_ONE, "outIdx %d out of range (%d)" % (outIdx, len(txtmp.vout)))

        tmp_vout = txtmp.vout[outIdx]
        txtmp.vout = []
        for i in range(outIdx):
            txtmp.vout.append(bitcointx.core.CMutableTxOut())
        txtmp.vout.append(tmp_vout)

        for i in range(len(txtmp.vin)):
            if i != inIdx:
                txtmp.vin[i].nSequence = 0

    if hashtype & SIGHASH_ANYONECANPAY:
        tmp_vin = txtmp.vin[inIdx]
        txtmp.vin = []
        txtmp.vin.append(tmp_vin)

    txtmp.wit = bitcointx.core.CMutableTxWitness()
    s = txtmp.serialize(for_sighash=True)
    s += struct.pack(b"<i", hashtype)

    hash = bitcointx.core.Hash(s)

    return (hash, None)


def RawSignatureHash(script: CScript, txTo: 'bitcointx.core.CTransaction', inIdx: int,
                     hashtype: int, amount: Optional[int] = None,
                     sigversion: SIGVERSION_Type = SIGVERSION_BASE
                     ) -> Tuple[bytes, Optional[str]]:
    """Consensus-correct SignatureHash

    Returns (hash, err) to precisely match the consensus-critical behavior of
    the SIGHASH_SINGLE bug. (inIdx is *not* checked for validity)

    If you're just writing wallet software you probably want SignatureHash()
    instead.
    """
    return script.raw_sighash(txTo, inIdx, hashtype, amount=amount, sigversion=sigversion)


def SignatureHash(script: CScript, txTo: 'bitcointx.core.CTransaction', inIdx: int,
                  hashtype: SIGHASH_Type, amount: Optional[int] = None,
                  sigversion: SIGVERSION_Type = SIGVERSION_BASE) -> bytes:
    """Calculate a signature hash

    'Cooked' version that checks if inIdx is out of bounds - this is *not*
    consensus-correct behavior, but is what you probably want for general
    wallet use.
    """
    (h, err) = RawSignatureHash(script, txTo, inIdx, hashtype, amount=amount, sigversion=sigversion)
    if err is not None:
        raise ValueError(err)
    return h


class CBitcoinScript(CScript, ScriptBitcoinClass):
    ...


class StandardMultisigScriptInfo:
    __slots__: List[str] = ['required', 'pubkeys']

    required: int
    pubkeys: Tuple['bitcointx.core.key.CPubKey', ...]

    def __init__(self, *, total: int, required:
                 int, pubkeys: Sequence['bitcointx.core.key.CPubKey']):
        if len(pubkeys) != total:
            raise ValueError('total must be equal to number of pubkeys')

        if required > total:
            raise ValueError('required must not be greater than total')

        self.required = required
        self.pubkeys = tuple(pubkeys)

    @property
    def total(self) -> int:
        return len(self.pubkeys)


def parse_standard_multisig_redeem_script(script: CScript
                                          ) -> StandardMultisigScriptInfo:
    """parse multisig script, raises ValueError if it does not match the
    format of the script produced by construct_multisig_redeem_script"""
    si = iter(script)
    try:
        required = next(si)
    except StopIteration:
        raise ValueError(
            'script is too short: stoped at required number of signatures')
    if not isinstance(required, int):
        raise ValueError('script is not a p2sh script, required number '
                         'of signatures is not a number')
    if required < 1:
        raise ValueError('required number of signatures are less than 1')
    if required > MAX_P2SH_MULTISIG_PUBKEYS:
        raise ValueError('required number of signatures are more than {}'
                         .format(MAX_P2SH_MULTISIG_PUBKEYS))
    total = None
    pubkeys: List[bitcointx.core.key.CPubKey] = []
    for i in range(MAX_P2SH_MULTISIG_PUBKEYS+1):  # +1 for `total`
        try:
            pub_data = next(si)
            if isinstance(pub_data, int):
                total = pub_data  # pubkeys ended
                break
            assert isinstance(pub_data, bytes)
            pub = bitcointx.core.key.CPubKey(pub_data)
            if not pub.is_fullyvalid():
                raise ValueError(
                    f'encountered an invalid pubkey at position {i}')
            pubkeys.append(pub)
        except StopIteration:
            raise ValueError(
                'script is too short for specified number of required '
                'signatures ({})'.format(required))

    if total is None:
        raise ValueError('script appears to contain more than {} pubkeys'
                         .format(MAX_P2SH_MULTISIG_PUBKEYS))

    if total != len(pubkeys):
        raise ValueError('number of pubkeys in the script is not the same '
                         'as the number of pubkeys required')
    if total < 2:
        raise ValueError('total number of pubkeys are less than 2')
    if total > MAX_P2SH_MULTISIG_PUBKEYS:
        raise ValueError('required number of pubkeys are more than {}'
                         .format(MAX_P2SH_MULTISIG_PUBKEYS))
    try:
        last_op = next(si)
    except StopIteration:
            raise ValueError('script is too short, ended before we could get '
                             'the last opcode')

    if last_op != OP_CHECKMULTISIG:
        raise ValueError('script is not a p2sh script, last opcode '
                         'is not OP_CHECKMULTISIG')
    try:
        next(si)
        raise ValueError('script has opcodes past OP_CHECKMULTISIG')
    except StopIteration:
        pass

    if len(set(pubkeys)) != len(pubkeys):
        raise ValueError('duplicate pubkeys in a script')

    # check that this is actually the last opcode
    return StandardMultisigScriptInfo(total=total, required=required,
                                      pubkeys=tuple(pubkeys))


def standard_multisig_witness_stack(sigs: List[Union[bytes, bytearray]],
                                    redeem_script: CScript
                                    ) -> List[ScriptElement_Type]:

    # check that standard multisig script is valid
    info = parse_standard_multisig_redeem_script(redeem_script)

    if not all(isinstance(s, (bytes, bytearray)) for s in sigs):
        raise ValueError('sigs must be an array of bytes (or bytearrays)')

    if len(sigs) > info.total:
        raise ValueError('number of signatures ({}) is greater than '
                         'total pubkeys ({}) in the redeem script'
                         .format(len(sigs), info.total))

    if len(sigs) != info.required:
        raise ValueError('number of signatures ({}) does not match '
                         'the number of required pubkeys ({}) '
                         'in the redeem script'
                         .format(len(sigs), info.required))

    stack: List[ScriptElement_Type]

    stack = [0]  # dummy 0 required for CHECKMULTISIG
    stack.extend(sigs)
    stack.append(redeem_script)
    return stack


def standard_multisig_redeem_script(
    *,
    total: int,
    required: int,
    pubkeys: List['bitcointx.core.key.CPubKey'],
) -> CScript:
    """Construct multisignature redeem script.
    We require to supply total number of pubkeys as separate argument
    to be able to catch bugs when pubkeys array is wrong for some reason.
    If the callers do not care about the possibility of such bug, they
    can just supply total=len(pubkeys).

    For '1-of-1' case the function raises ValueError exception,
    because this case is ambiguous - can be done via CHECKSIG or CHECKMULTISIG,
    and is not really a multisig.

    Arguments:

    total    - total number of pubkeys (must match the length of pubkeys array)
    required - the number of signatures required to satisfy the script,
               must be less than or equal to `total`
    pubkeys  - an array of pubkeys"""

    if total != len(pubkeys):
        raise ValueError("'total' argument must match length of pubkeys array")
    if required <= 0:
        raise ValueError("'required' argument must be >= 1")
    if required > total:
        raise ValueError(
            "'required' argument must be less than or equal to 'total'")
    if total > MAX_P2SH_MULTISIG_PUBKEYS:
        raise ValueError("%d pubkeys do not fit into standard p2sh multisig"
                         % total)
    if total == 1:
        # for 1-of-1, there is ambiguity in possible scripts:
        # using CHECKMULTISIG, or using just CHECKSIG.
        # scriptSig for these variants would differ, because CHECKMULTISIG
        # requires extra '0' on the stack, which CHECKSIG does not require.
        # therefore, if the callers want to support 1-of-1 in P2SH,
        # they need to handle it themselves.
        raise ValueError('1-of-1 multisig is not supported')

    result: List[ScriptElement_Type]

    result = [required]
    result.extend(pubkeys)
    result.append(total)
    result.append(OP_CHECKMULTISIG)

    return CScript(result)


def standard_keyhash_scriptpubkey(keyhash: bytes) -> CScript:
    ensure_isinstance(keyhash, bytes, 'keyhash')
    if len(keyhash) != 20:
        raise ValueError('keyhash len is not 20')
    return CScript([OP_DUP, OP_HASH160, keyhash, OP_EQUALVERIFY, OP_CHECKSIG])


def standard_witness_v0_scriptpubkey(keyhash_or_scripthash: bytes) -> CScript:
    ensure_isinstance(keyhash_or_scripthash, bytes, 'keyhash or scripthash')
    if len(keyhash_or_scripthash) not in (20, 32):
        raise ValueError('keyhash_or_scripthash len is not 20 nor 32')
    return CScript([0, keyhash_or_scripthash])


def standard_scripthash_scriptpubkey(scripthash: bytes) -> CScript:
    ensure_isinstance(scripthash, bytes, 'scripthash')
    if len(scripthash) != 20:
        raise ValueError('scripthash len is not 20')
    return CScript([OP_HASH160, scripthash, OP_EQUAL])


class ComplexScriptSignatureHelper:

    @abstractmethod
    def num_sigs_missing(self) -> int:
        """Return the minimum number of signatures that needs to be added
        for the script spending conditions to be satisfied"""

    @no_bool_use_as_property
    def is_enough_signatures(self) -> bool:
        return self.num_sigs_missing() == 0

    @abstractmethod
    def get_pubkeys_without_sig(self) -> Iterable['bitcointx.core.key.CPubKey']:
        """Return an iterable of pubkeys involved in the script spending
        condition, that have no signatures collected for them yet.
        The `sign()` method will use this iterable to try to get
        the signatures required."""

    @abstractmethod
    def construct_witness_stack(self) -> List[ScriptElement_Type]:
        """Construct a witness stack from spending script and
        the available signatures"""

    @abstractmethod
    def collect_sig(self, pub: 'bitcointx.core.key.CPubKey',
                    sig: Union[bytes, bytearray]) -> bool:
        """Collect a signature for the pubkey.
        return True if there is enough signatures to satisfy the script."""

    def sign(self, signer: Callable[['bitcointx.core.key.CPubKey'],
                                    Optional[bytes]],
             partial_sigs: Optional[
                 Dict['bitcointx.core.key.CPubKey', bytes]
             ] = None
             ) -> Tuple[Dict['bitcointx.core.key.CPubKey', bytes], bool]:
        """Create signatures for the pubkeys involved in spending conditions
        of the script, bu using provided `signer` callback. This callback
        should have access to all the information required to produce the
        signature, such as the transaction, input index, the private keys,
        etc. The only argument to the callback is the public key. It should
        return the signature, or None if it cannot produce the signature.

        If some of the signatures are already known, a doct of
        pubkey -> signature can be supplied via `partial_sigs` argument"""

        if partial_sigs:
            for pub, sig in partial_sigs.items():
                if self.collect_sig(pub, sig):
                    break

        new_sigs: Dict['bitcointx.core.key.CPubKey', bytes] = {}
        if self.is_enough_signatures():
            return new_sigs, True

        for pub in self.get_pubkeys_without_sig():
            maybe_sig = signer(pub)
            if maybe_sig is not None:
                new_sigs[pub] = maybe_sig
                if self.collect_sig(pub, maybe_sig):
                    break  # 'enough signatures' threshold reached

        return new_sigs, self.is_enough_signatures()


class StandardMultisigSignatureHelper(ComplexScriptSignatureHelper):

    _script: CScript
    _script_info: StandardMultisigScriptInfo
    _signatures: List[Optional[bytes]]

    def __init__(self, script: CScript) -> None:
        self._script_info = parse_standard_multisig_redeem_script(script)
        self._script = script
        self._signatures = [None for _ in self._script_info.pubkeys]

    def num_sigs_missing(self) -> int:
        num_sigs = len(list(s for s in self._signatures if s is not None))

        if num_sigs == self._script_info.required:
            return 0

        if num_sigs > self._script_info.required:
            raise AssertionError('cannot have more signatures than required')

        return self._script_info.required - num_sigs

    def get_pubkeys_without_sig(self) -> Iterable['bitcointx.core.key.CPubKey']:
        return (p for i, p in enumerate(self._script_info.pubkeys)
                if not self._signatures[i])

    def construct_witness_stack(self) -> List[ScriptElement_Type]:
        if not self.is_enough_signatures():
            raise ValueError('not enough signatures')

        sigs = [s for s in self._signatures if s is not None]
        return standard_multisig_witness_stack(sigs, self._script)

    def collect_sig(self, pub: 'bitcointx.core.key.CPubKey',
                    sig: Union[bytes, bytearray]) -> bool:

        for index, s_pub in enumerate(self._script_info.pubkeys):
            if pub == s_pub:
                break
        else:
            raise ValueError('pubkey is not in redeem script')

        if self.is_enough_signatures():
            return True

        if self._signatures[index] is not None:
            return False  # signature is already present

        self._signatures[index] = bytes(sig)

        if self.is_enough_signatures():
            return True

        return False


# default dispatcher for the module
activate_class_dispatcher(ScriptBitcoinClassDispatcher)


__all__ = (
    'MAX_SCRIPT_SIZE',
    'MAX_SCRIPT_ELEMENT_SIZE',
    'MAX_SCRIPT_OPCODES',
    'OPCODE_NAMES',
    'CScriptOp',

    # every opcode
    'OP_0',
    'OP_FALSE',
    'OP_PUSHDATA1',
    'OP_PUSHDATA2',
    'OP_PUSHDATA4',
    'OP_1NEGATE',
    'OP_RESERVED',
    'OP_1',
    'OP_TRUE',
    'OP_2',
    'OP_3',
    'OP_4',
    'OP_5',
    'OP_6',
    'OP_7',
    'OP_8',
    'OP_9',
    'OP_10',
    'OP_11',
    'OP_12',
    'OP_13',
    'OP_14',
    'OP_15',
    'OP_16',
    'OP_NOP',
    'OP_VER',
    'OP_IF',
    'OP_NOTIF',
    'OP_VERIF',
    'OP_VERNOTIF',
    'OP_ELSE',
    'OP_ENDIF',
    'OP_VERIFY',
    'OP_RETURN',
    'OP_TOALTSTACK',
    'OP_FROMALTSTACK',
    'OP_2DROP',
    'OP_2DUP',
    'OP_3DUP',
    'OP_2OVER',
    'OP_2ROT',
    'OP_2SWAP',
    'OP_IFDUP',
    'OP_DEPTH',
    'OP_DROP',
    'OP_DUP',
    'OP_NIP',
    'OP_OVER',
    'OP_PICK',
    'OP_ROLL',
    'OP_ROT',
    'OP_SWAP',
    'OP_TUCK',
    'OP_CAT',
    'OP_SUBSTR',
    'OP_LEFT',
    'OP_RIGHT',
    'OP_SIZE',
    'OP_INVERT',
    'OP_AND',
    'OP_OR',
    'OP_XOR',
    'OP_EQUAL',
    'OP_EQUALVERIFY',
    'OP_RESERVED1',
    'OP_RESERVED2',
    'OP_1ADD',
    'OP_1SUB',
    'OP_2MUL',
    'OP_2DIV',
    'OP_NEGATE',
    'OP_ABS',
    'OP_NOT',
    'OP_0NOTEQUAL',
    'OP_ADD',
    'OP_SUB',
    'OP_MUL',
    'OP_DIV',
    'OP_MOD',
    'OP_LSHIFT',
    'OP_RSHIFT',
    'OP_BOOLAND',
    'OP_BOOLOR',
    'OP_NUMEQUAL',
    'OP_NUMEQUALVERIFY',
    'OP_NUMNOTEQUAL',
    'OP_LESSTHAN',
    'OP_GREATERTHAN',
    'OP_LESSTHANOREQUAL',
    'OP_GREATERTHANOREQUAL',
    'OP_MIN',
    'OP_MAX',
    'OP_WITHIN',
    'OP_RIPEMD160',
    'OP_SHA1',
    'OP_SHA256',
    'OP_HASH160',
    'OP_HASH256',
    'OP_CODESEPARATOR',
    'OP_CHECKSIG',
    'OP_CHECKSIGVERIFY',
    'OP_CHECKMULTISIG',
    'OP_CHECKMULTISIGVERIFY',
    'OP_NOP1',
    'OP_NOP2',
    'OP_CHECKLOCKTIMEVERIFY',
    'OP_NOP3',
    'OP_NOP4',
    'OP_NOP5',
    'OP_NOP6',
    'OP_NOP7',
    'OP_NOP8',
    'OP_NOP9',
    'OP_NOP10',
    'OP_SMALLINTEGER',
    'OP_PUBKEYS',
    'OP_PUBKEYHASH',
    'OP_PUBKEY',
    'OP_INVALIDOPCODE',

    'OPCODES_BY_NAME',
    'DISABLED_OPCODES',
    'CScriptInvalidError',
    'CScriptTruncatedPushDataError',
    'CScript',
    'CBitcoinScript',
    'CScriptWitness',
    'SIGHASH_ALL',
    'SIGHASH_NONE',
    'SIGHASH_SINGLE',
    'SIGHASH_ANYONECANPAY',
    'SIGHASH_Type',
    'FindAndDelete',
    'RawSignatureHash',
    'RawBitcoinSignatureHash',
    'SignatureHash',
    'IsLowDERSignature',

    'SIGVERSION_BASE',
    'SIGVERSION_WITNESS_V0',
    'SIGVERSION_Type',

    'ScriptCoinClassDispatcher',
    'ScriptCoinClass',
    'parse_standard_multisig_redeem_script',
    'standard_multisig_redeem_script',
    'standard_multisig_witness_stack',
    'standard_scripthash_scriptpubkey',
    'standard_keyhash_scriptpubkey',
    'standard_witness_v0_scriptpubkey',
    'ComplexScriptSignatureHelper',
    'StandardMultisigSignatureHelper',
)
