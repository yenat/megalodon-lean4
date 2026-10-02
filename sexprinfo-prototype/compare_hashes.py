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
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(200000)

import reverse_translate as R
from sexpr_translate import parse_toplevel_forms


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(2)
    corpus = R.Corpus(parse_toplevel_forms(open(sys.argv[1]).read()))
    recon = {}
    for line in open(sys.argv[2]):
        parts = line.split()
        if len(parts) == 2:
            recon[parts[0]] = parts[1]

    match = differ = absent = 0
    bad = []
    for name, got in recon.items():
        want = corpus.hash.get(name)
        if want is None:
            absent += 1
        elif want == got:
            match += 1
        else:
            differ += 1
            bad.append((name, corpus.kind.get(name), got, want))

    print("  hashes recomputed by Megalodon  %d" % len(recon))
    print("  MATCH the original hash         %d" % match)
    print("  differ                          %d" % differ)
    print("  not in the corpus               %d" % absent)
    for name, kind, got, want in bad[:10]:
        print("    %s (%s)\n      recomputed %s\n      original   %s"
              % (name, kind, got, want))
    sys.exit(1 if differ else 0)


if __name__ == "__main__":
    main()
