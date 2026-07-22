#!/usr/bin/env python3
"""Generate cross-language golden vectors from rsmt6a.py (DEVPLAN D10 / M0).

Runs seeded multi-round insertion scenarios and dumps a simple line-based
format that `crates/rsmt-core/tests/differential.rs` replays through
`Sha256RefHasher`, asserting byte-identical roots and opcode streams.

Line format (whitespace-separated tokens):

    SCENARIO <name>
    ROUND
    BATCH <n>
      <key_hex64> <value_hex>          (n lines; value_hex may be empty -> "-")
    APPLIED <a>
      <key_hex64> <value_hex>          (a lines)
    OLD <root_hex64|none>
    NEW <root_hex64|none>
    PROOF <m>
      S  <hex64>
      O  <depth> <region_hex64> <lh_hex64> <rh_hex64>
      OL <key_hex64> <value_hex>
      L
      N  <depth>
    ENDROUND
    ENDSCENARIO

Usage: python3 gen_vectors.py > ../crates/rsmt-core/tests/vectors.txt
"""

import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "ndsmt-experiments"))
import rsmt6a as R  # noqa: E402

KEY_HEX = 64  # 32 bytes


def kh(k):
    return "%064x" % k


def vh(v):
    return v.hex() if v else "-"


def h32(digest):
    return "none" if digest is None else digest.hex()


def emit_round(out, tree, batch):
    old_root = tree.get_root()
    applied, proof = tree.batch_insert(batch)
    new_root = tree.get_root()
    out.append("ROUND")
    out.append("BATCH %d" % len(batch))
    for k, v in batch:
        out.append("%s %s" % (kh(k), vh(v)))
    out.append("APPLIED %d" % len(applied))
    for k, v in applied:
        out.append("%s %s" % (kh(k), vh(v)))
    out.append("OLD %s" % h32(old_root))
    out.append("NEW %s" % h32(new_root))
    # serialize proof
    ser = []
    i = 0
    while i < len(proof):
        tag = proof[i]
        i += 1
        if tag == "S":
            ser.append("S %s" % proof[i].hex()); i += 1
        elif tag == "O":
            d, p, lh, rh = proof[i:i + 4]; i += 4
            packed = (p << (256 - d)).to_bytes(32, "big")
            ser.append("O %d %s %s %s" % (d, packed.hex(), lh.hex(), rh.hex()))
        elif tag == "OL":
            k, v = proof[i:i + 2]; i += 2
            ser.append("OL %s %s" % (kh(k), vh(v)))
        elif tag == "L":
            ser.append("L")
        elif tag == "N":
            ser.append("N %d" % proof[i]); i += 1
        else:
            raise ValueError("bad tag %r" % tag)
    out.append("PROOF %d" % len(ser))
    out.extend(ser)
    out.append("ENDROUND")


def scenario(out, name, seed, rounds):
    out.append("SCENARIO %s" % name)
    rng = random.Random(seed)
    tree = R.SparseMerkleTree()
    for _ in range(rounds):
        n = rng.choice([1, 1, 2, 3, 5, 17, 64, 200])
        batch = []
        for _ in range(n):
            k = rng.getrandbits(256)
            v = rng.getrandbits(256).to_bytes(32, "big")  # exact 32-byte Value32 (R3-D1)
            batch.append((k, v))
        # occasionally re-record a possibly-present key (dedup path)
        if rng.random() < 0.3 and batch:
            batch.append((batch[0][0], (b"dup").ljust(32, b"\x00")))
        emit_round(out, tree, batch)
    out.append("ENDSCENARIO")


def scenario_shared_prefix(out, name, seed, rounds):
    """Keys sharing long prefixes -> deep junctions, splits in the tail limb."""
    out.append("SCENARIO %s" % name)
    rng = random.Random(seed)
    tree = R.SparseMerkleTree()
    base = rng.getrandbits(256) & ~((1 << 40) - 1)  # zero low 40 bits
    for _ in range(rounds):
        n = rng.choice([1, 2, 3, 8])
        batch = []
        for _ in range(n):
            k = base | rng.getrandbits(40)  # differ only in low 40 bits
            v = rng.getrandbits(256).to_bytes(32, "big")  # exact 32-byte Value32 (R3-D1)
            batch.append((k, v))
        emit_round(out, tree, batch)
    out.append("ENDSCENARIO")


def main():
    out = []
    for s in range(6):
        scenario(out, "mixed_%d" % s, 1000 + s, rounds=8)
    scenario_shared_prefix(out, "shared_prefix_a", 77, rounds=10)
    scenario_shared_prefix(out, "shared_prefix_b", 88, rounds=10)
    # single-leaf and tiny edge cases
    scenario(out, "tiny_a", 5, rounds=12)
    scenario(out, "tiny_b", 9, rounds=12)
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
