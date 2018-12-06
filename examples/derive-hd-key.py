#!/usr/bin/env python3
#
# Copyright (C) 2018 The python-bitcointx developers
#
# This file is part of python-bitcointx.
#
# It is subject to the license terms in the LICENSE file found in the top-level
# directory of this distribution.
#
# No part of python-bitcoinlib, including this file, may be copied, modified,
# propagated, or distributed except according to the terms contained in the
# LICENSE file.

import sys
import ssl
from bitcointx.core import BIP32_HARDENED_KEY_LIMIT
from bitcointx.core.key import CExtKey
from bitcointx.base58 import Base58Error
from bitcointx.wallet import CBitcoinExtKey, CBitcoinExtPubKey

if __name__ == '__main__':
    if len(sys.argv) < 2 or len(sys.argv) > 3:
        print("usage: {} <derivation_path> [xpriv_or_xpub]"
              .format(sys.argv[0]))
        sys.exit(-1)

    if len(sys.argv) == 2:
        xkey = CBitcoinExtKey.from_xpriv(CExtKey.from_seed(ssl.RAND_bytes(32)))
        print("generated xpriv: ", xkey)
    else:
        for cls in (CBitcoinExtKey, CBitcoinExtPubKey):
            try:
                xkey = cls(sys.argv[2])
                break
            except Base58Error:
                print("ERROR: specified key is incorrectly encoded")
                sys.exit(-1)
            except ValueError:
                pass
        else:
            print("ERROR: specified key does not appear to be valid")
            sys.exit(-1)

    path = sys.argv[1]
    if path.startswith('m'):
        path = path[1:]

    numeric_path = []
    for elt in path.split('/'):
        if elt == '':
            continue

        c = elt
        hardened = 0
        if c.endswith("'") or c.endswith('h'):
            hardened = BIP32_HARDENED_KEY_LIMIT
            c = c[:-1]
        try:
            n = int(c) + hardened
        except ValueError:
            print("ERROR: invalid element in the path:", elt)
            sys.exit(-1)

        print("child: {:08x}".format(n))
        if isinstance(xkey, CBitcoinExtKey):
            xkey = CBitcoinExtKey.from_xpriv(xkey.xpriv.derive(n))
            print("xpriv:", xkey)
            print("xpub: ",  CBitcoinExtPubKey.from_xpub(xkey.xpriv.neuter()))
        else:
            assert isinstance(xkey, CBitcoinExtPubKey)
            xkey = CBitcoinExtPubKey.from_xpub(xkey.xpub.derive(n))
            print("xpub:",  xkey)
