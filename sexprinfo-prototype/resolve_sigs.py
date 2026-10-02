#!/usr/bin/env python3
"""Work out which signature files a Megalodon source file needs.

Some mgwiki files -- the conjecture-style ones -- reference identifiers by
content hash without declaring, via `$I`, which signature file establishes
them. Supplying every `sig/*.mgs` does not work: they overlap, and
Megalodon rejects the duplicate declarations ("False has already been
used"). So the set has to be discovered, not guessed.

This drives Megalodon in a loop. Each run fails with one unknown hash;
that hash is looked up across `sig/*.mgs`, the file declaring it is added
to the `-I` set, and the run is repeated. It converges on a working set,
or stops and says exactly which hash it could not place.
"""
import re, subprocess, sys, glob, os

# a checkout of https://github.com/mgwiki/mgw_test
WIKI = os.environ.get("MGWIKI", os.path.expanduser("~/mgw_test"))
UNKNOWN = re.compile(r"The given id ([0-9a-f]{64}) for (\S+) is not a known index")
CONFLICT = re.compile(r"(\S+) has already been used")


def sig_index():
    """hash -> [sig files declaring it]"""
    idx = {}
    for p in sorted(glob.glob(os.path.join(WIKI, "sig", "*.mgs"))):
        txt = open(p, errors="replace").read()
        for h in set(re.findall(r"[0-9a-f]{64}", txt)):
            idx.setdefault(h, []).append(os.path.relpath(p, WIKI))
    return idx


def run(meg, target, sigs, ind, own, out):
    cmd = [meg]
    if ind and os.path.getsize(ind):
        cmd += ["-ind", ind]
    if own and os.path.getsize(own):
        cmd += ["-owned", own]
    for s in sigs:
        cmd += ["-I", s]
    cmd += ["-sexprinfo", target]
    with open(out, "w") as f:
        rc = subprocess.run(cmd, cwd=WIKI, stdout=f,
                            stderr=subprocess.STDOUT, timeout=1800).returncode
    return rc, open(out, errors="replace").read()


def resolve(meg, target, ind, own, out, limit=40):
    idx = sig_index()
    sigs, tried = [], set()
    for _ in range(limit):
        rc, log = run(meg, target, sigs, ind, own, out)
        if rc == 0:
            return True, sigs, None
        m = UNKNOWN.search(log)
        if not m:
            c = CONFLICT.search(log)
            return False, sigs, ("conflict on %s" % c.group(1)) if c \
                else (log.strip().splitlines() or ["?"])[-1][:120]
        h, name = m.group(1), m.group(2)
        cands = [s for s in idx.get(h, []) if s not in tried]
        if not cands:
            return False, sigs, "no sig file declares %s (%s)" % (name, h[:16])
        pick = cands[0]
        tried.add(pick)
        sigs.append(pick)
    return False, sigs, "did not converge in %d rounds" % limit


if __name__ == "__main__":
    if len(sys.argv) < 6:
        print(__doc__)
        print("usage: resolve_sigs.py <megalodon> <index> <owned> <outdir> "
              "<file> [<file>...]")
        print("       set MGWIKI if the wiki checkout is not at ~/mgw_test")
        sys.exit(2)
    meg, ind, own, outdir = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    for f in sys.argv[5:]:
        tgt = "mglib/%s.mg" % f
        out = os.path.join(outdir, f + ".sexpr")
        ok, sigs, why = resolve(meg, tgt, ind, own, out)
        txt = open(out, errors="replace").read()
        thm = txt.count("\n(THM ") + txt.startswith("(THM ")
        prf = txt.count("\n(PROOF ") + txt.startswith("(PROOF ")
        print("%-24s %s  THM=%-5d PROOF=%-5d sigs=%d %s"
              % (f, "OK " if ok else "FAIL", thm, prf, len(sigs),
                 "" if ok else "<- " + str(why)))
        if ok and sigs:
            print("     needed: %s" % " ".join(sigs))
