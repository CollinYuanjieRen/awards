#!/usr/bin/env python3
"""Fetch the pinned upstream Lean sources this package depends on but does not redistribute.

The nine files below come from github.com/plby/lean-proofs at commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e. The two Erdos444 files carry Apache-2.0 headers; the
other seven and the repository carry no license notice, so none of them is copied into
this submission. This script downloads each
file, checks its SHA-256 against the pinned value, rewrites its `import ErdosProblems.*`
lines to `import Erdos439Power.Vendor.ErdosProblems.*`, and writes it under
Erdos439Power/Vendor/. Nothing else is changed. Run it once before `lake build`.
"""
import hashlib, pathlib, re, sys, urllib.request

PIN = "8822f7ddef30fadbd92e1c6ab4ed897af356af5e"
SOURCES = [
    ("ErdosProblems.Erdos439.PowerSums",
     "https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos439/PowerSums.lean",
     "7bff421df3352f0011b20eae27718e7bd4abed64038e37e7f773b558f5b55989"),
    ("ErdosProblems.Erdos444.Moment",
     "https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos444/Moment.lean",
     "0794ddb8dbcfc1d920c059c8dd2935347d2bf23748db0048f1d650da0630111d"),
    ("ErdosProblems.Erdos444.Basic",
     "https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos444/Basic.lean",
     "9c657003e30a022b7b20811694889c4f52ff822c4374c66ddf874f6eb4690603"),
    ("ErdosProblems.Erdos443",
     "https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos443.lean",
     "f931ce4fe079203fccacc1321c535d69c2c99dcf4aeff0c1884e1db5bc45bbc5"),
    ("ErdosProblems.Erdos387.FiniteWeylInequality",
     "https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos387/FiniteWeylInequality.lean",
     "a2f010cdb5c9832e3c5de1e58882ce1640be3f55d4436147bfb28fd40e1e0395"),
    ("ErdosProblems.Erdos387.InverseWeylDifferencing",
     "https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos387/InverseWeylDifferencing.lean",
     "4359a05d543fe2822455271b9fe4430f92d91786b91f01fe5caa47348c4c6426"),
    ("ErdosProblems.Erdos387.KloostermanOrthogonality",
     "https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos387/KloostermanOrthogonality.lean",
     "9f780d2fba0309899c347ee48a7bd7c151934fe06716844e8e8648fa52bae409"),
    ("ErdosProblems.Erdos387.AdditiveCharacterOrthogonality",
     "https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos387/AdditiveCharacterOrthogonality.lean",
     "085577fce2785bf2bac7cc2ef36535e4fa3b92c9ee921a7ed5e623a95c8ec858"),
    ("ErdosProblems.Erdos438.Fourier",
     "https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos438/Fourier.lean",
     "55d6425e50d52fe0e712ddb7396abb68d38237bbdc9ace89d5f9a6903162e6dd")
]

root = pathlib.Path(__file__).resolve().parent
for module, url, sha in SOURCES:
    raw = urllib.request.urlopen(url, timeout=60).read()
    got = hashlib.sha256(raw).hexdigest()
    if got != sha:
        sys.exit(f"hash mismatch for {module}: expected {sha}, got {got}")
    text = re.sub(rb"^import ErdosProblems\.", b"import Erdos439Power.Vendor.ErdosProblems.", raw, flags=re.M)
    rel = pathlib.Path("Erdos439Power/Vendor") / (module.replace(".", "/") + ".lean")
    out = root / rel
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(text)
    print(f"ok  {rel}  source sha256 {sha}")
print("all pinned sources fetched and verified")
