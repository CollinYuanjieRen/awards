#!/usr/bin/env python3
"""Fetch the pinned upstream Lean sources this package depends on but does not redistribute.

Two upstream trees are fetched here; everything else in this package is either
first-party (`Erdos381Lower/`) or Apache-2.0 material shipped in place
(`PrimeNumberTheoremAnd/`, see `LICENSES/`).

1. plby/lean-proofs -> `ErdosProblems/` (182 files)
   Commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e.  That repository carries no license
   grant (no LICENSE at its root; `src/latest/LICENSE` is only a notice that *some*
   files come from elsewhere under Apache-2.0, and 95 of the 182 files in this cone carry
   Apache-2.0 headers inherited from other upstream sources, the rest carry none, and the
   repository itself grants no license).  So none of their text is copied into this
   submission.  Each file is downloaded from raw.githubusercontent.com, checked against
   its pinned SHA-256, and written unmodified to `ErdosProblems/<path>`.  There is no
   import rewrite and no patch: every one of the 182 files is byte-identical to upstream.

2. frenzymath/FormalPantheon -> `vendor/formalpantheon/{BoundedGaps,Warning}` (886 .lean files)
   Commit ffbb65c21afc8a36ace67720f1b0df1c63d26bd1, Apache-2.0 (repository LICENSE, which
   is extracted to `vendor/formalpantheon/LICENSE`).  The commit tarball is downloaded and
   hash-checked, the two packages are extracted, and `patches/formalpantheon-mathlib-v4.33.0.patch`
   is applied with `patch -p1`.  That patch is our own regenerated `diff -u` (91 files) carrying
   the Mathlib v4.32 -> v4.33 adaptation; its SHA-256 is pinned in `pinned-sources.json`, and
   every resulting .lean file is verified against its recorded post-patch SHA-256, so the
   vendored tree is reproduced byte-for-byte.

   GitHub's generated tarballs are not contractually byte-stable, so a tarball hash mismatch
   is reported as a warning and the per-file hashes below remain the authoritative check;
   any file-level mismatch is a hard failure.

All pinned hashes live in `pinned-sources.json`.

Usage:
    python3 fetch_pinned.py           # fetch and verify everything
    python3 fetch_pinned.py --check   # verify what is already on disk, write nothing
    python3 fetch_pinned.py --list    # print the file lists and exit

Run it once before `lake build`.
"""
import argparse
import hashlib
import io
import json
import pathlib
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent
DATA = json.loads((ROOT / "pinned-sources.json").read_text())
VENDOR = ROOT / "vendor" / "formalpantheon"


def sha256(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def fetch(url: str) -> bytes:
    with urllib.request.urlopen(url, timeout=180) as r:
        return r.read()


def check_tree(pairs, label: str) -> int:
    """pairs: iterable of (path, expected sha256). Returns number of failures."""
    bad = 0
    for rel, want in pairs:
        p = ROOT / rel
        if not p.is_file():
            print("MISSING  %s" % rel)
            bad += 1
            continue
        got = sha256(p.read_bytes())
        if got != want:
            print("BAD      %s  (expected %s, got %s)" % (rel, want, got))
            bad += 1
    if bad == 0:
        print("ok  %s: all %d files verified" % (label, len(list(pairs))))
    return bad


def do_plby(check: bool) -> int:
    d = DATA["plby"]
    items = sorted(d["files"].items())
    if check:
        return check_tree(items, "ErdosProblems (%s)" % d["commit"][:12])
    bad = 0
    for rel, want in items:
        raw = fetch(d["raw_prefix"] + rel)
        got = sha256(raw)
        if got != want:
            print("HASH MISMATCH %s: expected %s, got %s" % (rel, want, got))
            bad += 1
            continue
        out = ROOT / rel
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_bytes(raw)
    if bad:
        print("%d of %d plby files failed" % (bad, len(items)))
    else:
        print("ok  ErdosProblems: %d files fetched from plby/lean-proofs @ %s and hash-verified"
              % (len(items), d["commit"]))
    return bad


def fp_expected():
    d = DATA["formalpantheon"]
    out = [("vendor/formalpantheon/" + rel, sha)
           for rel, sha in d["lean_files_after_patch"].items()]
    out += [("vendor/formalpantheon/" + rel, sha) for rel, sha in d["support_files"].items()]
    return sorted(out)


def do_formalpantheon(check: bool) -> int:
    d = DATA["formalpantheon"]
    if check:
        return check_tree(fp_expected(), "FormalPantheon (%s)" % d["commit"][:12])

    patch_path = ROOT / d["patch"]["path"]
    got = sha256(patch_path.read_bytes())
    if got != d["patch"]["sha256"]:
        print("BAD PATCH FILE %s: expected %s, got %s"
              % (d["patch"]["path"], d["patch"]["sha256"], got))
        return 1

    blob = fetch(d["tarball_url"])
    tsha = sha256(blob)
    if tsha != d["tarball_sha256"]:
        print("warning: tarball sha256 %s != pinned %s; GitHub-generated archives are not "
              "byte-stable, continuing to the authoritative per-file check" % (tsha, d["tarball_sha256"]))
    else:
        print("ok  FormalPantheon tarball sha256 %s" % tsha)

    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        with tarfile.open(fileobj=io.BytesIO(blob), mode="r:gz") as tf:
            tf.extractall(tmp)
        base = tmp / d["tarball_root"]
        if not base.is_dir():
            print("tarball root %s not found" % d["tarball_root"])
            return 1
        VENDOR.mkdir(parents=True, exist_ok=True)
        shutil.copy2(base / "LICENSE", VENDOR / "LICENSE")
        shutil.copy2(base / "README.md", VENDOR / "README.md")
        for pkg in d["packages"]:
            dest = VENDOR / pkg
            if dest.exists():
                shutil.rmtree(dest)
            shutil.copytree(base / pkg, dest)

    proc = subprocess.run(["patch", "-p1", "--no-backup-if-mismatch", "-i", str(patch_path)],
                          cwd=str(VENDOR), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if proc.returncode != 0:
        print(proc.stdout.decode(errors="replace"))
        print("patch failed")
        return 1
    print("ok  applied %s (%d files, Mathlib v4.32 -> v4.33 adaptation)"
          % (d["patch"]["path"], d["patch"]["files_changed"]))

    bad = check_tree(fp_expected(), "FormalPantheon (%s)" % d["commit"][:12])
    return bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="verify the files already on disk; download and write nothing")
    ap.add_argument("--list", action="store_true", help="print the file lists and exit")
    args = ap.parse_args()

    if args.list:
        p = DATA["plby"]
        print("plby/lean-proofs @ %s -- %d files, no license grant, fetched not redistributed:\n"
              % (p["commit"], len(p["files"])))
        for rel in sorted(p["files"]):
            print("      " + rel)
        f = DATA["formalpantheon"]
        print("\nfrenzymath/FormalPantheon @ %s -- %d .lean files, Apache-2.0, fetched as a tarball\n"
              "and patched by %s:\n" % (f["commit"], len(f["lean_files_after_patch"]), f["patch"]["path"]))
        for pkg in f["packages"]:
            n = sum(1 for k in f["lean_files_after_patch"] if k.startswith(pkg + "/"))
            print("      vendor/formalpantheon/%s  (%d .lean files)" % (pkg, n))
        print("\nShipped in this package instead of fetched:")
        print("      PrimeNumberTheoremAnd/  (9 files, Apache-2.0, see LICENSES/)")
        print("      Erdos381Lower/          (10 files, first-party)")
        return 0

    bad = do_plby(args.check) + do_formalpantheon(args.check)
    if bad:
        print("\n%d pinned source(s) failed verification." % bad)
        return 1
    print("\nall pinned sources %s" % ("verified" if args.check else "fetched and verified"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
