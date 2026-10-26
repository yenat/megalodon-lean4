#!/usr/bin/env python3
"""Compare recomputed content hashes against the ones Megalodon exported.

The round trip in `reverse_translate.py` compares s-expressions. This
compares *hashes*: `hashcheck.ml` recomputes each reconstructed term's id
with Megalodon's own `ptm_all_id` / `ptm_lam_id`, and this checks those
against the ids recorded in the original `-sexprinfo` export.

    python3 reverse_translate.py corpus.sexpr corpus_expr.sexpr \
        --emit recon.txt
    <megalodon>/bin/hashcheck recon.txt > recon_hashes.txt
    python3 compare_hashes.py corpus.sexpr recon_hashes.txt

Exits 0 only if every theorem, axiom and definition of the corpus has exactly
one recomputed hash and all of them match; a missing, duplicate, unknown or
malformed record fails the check.
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(200000)

import reverse_translate as R
from sexpr_translate import parse_toplevel_forms

ELIGIBLE = {"THM", "AXIOM", "DEF"}   # declarations whose content hash is checked


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(2)
    corpus = R.Corpus(parse_toplevel_forms(open(sys.argv[1]).read()))
    # every theorem, axiom and definition must come back with its hash:
    # a missing one is missing evidence, not a pass
    expected = {n for n, k in corpus.kind.items() if k in ELIGIBLE}
    recon, duplicate, malformed = {}, [], []
    for line in open(sys.argv[2]):
        parts = line.split()
        if not parts:
            continue
        if len(parts) != 2:
            malformed.append(line.strip()[:80])
        elif parts[0] in recon:
            duplicate.append(parts[0])
        else:
            recon[parts[0]] = parts[1]

    match = differ = 0
    unknown, bad = [], []
    for name, got in recon.items():
        want = corpus.hash.get(name)
        if name not in expected:
            unknown.append(name)
        elif want == got:
            match += 1
        else:
            differ += 1
            bad.append((name, corpus.kind.get(name), got, want))
    missing = sorted(expected - set(recon), key=corpus.order.index)

    print("  expected (THM, AXIOM, DEF)      %d" % len(expected))
    print("  hashes recomputed by Megalodon  %d" % len(recon))
    print("  MATCH the original hash         %d" % match)
    print("  differ                          %d" % differ)
    print("  missing                         %d %s" % (len(missing), missing[:5]))
    print("  duplicate                       %d %s" % (len(duplicate), duplicate[:5]))
    print("  not expected / unknown          %d %s" % (len(unknown), unknown[:5]))
    print("  malformed lines                 %d %s" % (len(malformed), malformed[:3]))
    for name, kind, got, want in bad[:10]:
        print("    %s (%s)\n      recomputed %s\n      original   %s"
              % (name, kind, got, want))
    complete = expected and match == len(expected) and not (
        differ or missing or duplicate or unknown or malformed)
    print("  verdict: %s" % ("COMPLETE: every expected hash matches" if complete
                             else "FAILED (or partial): see the counts above"))
    sys.exit(0 if complete else 1)


if __name__ == "__main__":
    main()
