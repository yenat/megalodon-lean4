#!/usr/bin/env python3
"""Negative control for the hash comparison.

"Every hash matched" is only meaningful if a *wrong* term would have
produced a different hash. Two ways that could fail to hold: the hashing
could be insensitive to the structure we are varying, or the comparison
could be silently passing everything. This perturbs each reconstructed
term in a way that keeps it well-formed but changes its meaning -- it
swaps the operands of one application -- and checks that Megalodon
assigns the perturbed term a different id.

    python3 hash_negative_control.py <recon.txt> <path/to/hashcheck>
"""
import re
import subprocess
import sys
import tempfile
import os

AP = re.compile(r'\(AP (\([^()]*\)) (\([^()]*\))\)')


def perturb(line):
    m = AP.search(line)
    if not m:
        return None
    return line[:m.start()] + "(AP %s %s)" % (m.group(2), m.group(1)) + line[m.end():]


def hashes(hashcheck, path):
    out = subprocess.run([hashcheck, path], capture_output=True, text=True)
    d = {}
    for line in out.stdout.splitlines():
        p = line.split()
        if len(p) == 2:
            d[p[0]] = p[1]
    return d


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(2)
    recon, hashcheck = sys.argv[1], sys.argv[2]
    tmp = tempfile.mkdtemp()
    orig_p = os.path.join(tmp, "orig.txt")
    pert_p = os.path.join(tmp, "pert.txt")
    orig, pert = [], []
    for line in open(recon):
        q = perturb(line)
        if q:
            orig.append(line)
            pert.append(q)
    open(orig_p, "w").writelines(orig)
    open(pert_p, "w").writelines(pert)

    a, b = hashes(hashcheck, orig_p), hashes(hashcheck, pert_p)
    changed = [k for k in b if k in a and a[k] != b[k]]
    same = [k for k in b if k in a and a[k] == b[k]]
    print("perturbable terms:            %d" % len(pert))
    print("  hash changed (as it must):  %d" % len(changed))
    print("  hash unchanged (a problem): %d %s" % (len(same), same[:5]))
    sys.exit(1 if same else 0)


if __name__ == "__main__":
    main()
