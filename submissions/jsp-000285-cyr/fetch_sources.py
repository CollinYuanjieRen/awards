#!/usr/bin/env python3
"""Fetch and verify the pinned Lean dependencies used by this submission."""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import tempfile
import urllib.request


PIN = "8822f7ddef30fadbd92e1c6ab4ed897af356af5e"
RAW_ROOT = f"https://raw.githubusercontent.com/plby/lean-proofs/{PIN}/src/latest"

SOURCES = {
    "ErdosProblems/Erdos13/Erdos13Additive.lean": "5da02d7a5885813a80e97319510fe69823a59d4603bb69ed5a485135aad3037d",
    "ErdosProblems/Erdos13/Erdos13Kneser.lean": "cb0d5c08c5c8db560f5ccfd4dff0160972941ffbfc7fa3117aa5e73558f8e9af",
    "ErdosProblems/Erdos13/Erdos13MulStab.lean": "0b5c6339a5e2518ea0086245602b49738f79f83398363d31ac62525d5328394d",
    "ErdosProblems/Erdos344.lean": "1dd262671722e317dcf5e449d40d572bb76b42e1012f9d207c21dd25ff74ef43",
    "ErdosProblems/Erdos360/Core.lean": "1c289f0daf906cce05cb4b917a82d0e40d965f4951986e60137270fbaff66830",
    "ErdosProblems/Erdos587/Erdos587Core.lean": "d2c087152af063cb2d0b4653256fd9967159ac6557f6a40cde43e69084b096f2",
    "ErdosProblems/Erdos697/Erdos697Bernoulli.lean": "ce331dc4cc1fefa6efac7208fba2ea9cb97fe2defe1e1d289f24f829ac01b59b",
}
LICENSE_SOURCE_SHA256 = "41e26750cf7403beef1b82310454ca79eb1da04b1dab82d4d42f377e15c01ea9"

CORE_PATH = "ErdosProblems/Erdos360/Core.lean"
CORE_FINAL_SHA256 = "78d35472ccf79b5ec7c40df5b06bb5300d1cc7dae39e2ef3e55ad76d5cc8d8f9"
CORE_PREFIX = """/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
VENDORED AND TRIMMED COPY.  Source: plby/lean-proofs, commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, file
src/latest/ErdosProblems/Erdos360/Core.lean. Upstream lists no individual authors;
License notice: see ../LICENSE.  Only the contiguous almost-period / iterated-sumset
section imported by ErdosProblems.Erdos344 is kept verbatim (original lines
2970-3433); the original module's other imports (Erdos851, Erdos4, Erdos360.*
sub-modules, UnitFractions) are not needed by these declarations and are dropped.
Nothing here is claimed as our work.
-/
import Mathlib
import ErdosProblems.Erdos587.Erdos587Core
import ErdosProblems.Erdos13.Erdos13Kneser
import ErdosProblems.Erdos13.Erdos13Additive

namespace Erdos360

open Filter
open scoped BigOperators Pointwise ComplexConjugate

attribute [local instance] Classical.propDecidable

""".encode()


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def fetch(url: str) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": "jsp285-pinned-source-fetch/1"})
    with urllib.request.urlopen(request, timeout=60) as response:
        return response.read()


def transform_core(upstream: bytes) -> bytes:
    lines = upstream.splitlines(keepends=True)
    if len(lines) < 3433:
        raise RuntimeError(f"upstream Core has only {len(lines)} lines; expected at least 3433")
    body = b"".join(lines[2969:3433])
    return CORE_PREFIX + body + b"end Erdos360\n"


def atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, prefix=f".{path.name}.", delete=False) as handle:
        temporary = Path(handle.name)
        handle.write(payload)
        handle.flush()
        os.fsync(handle.fileno())
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--directory",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="destination project directory (default: directory containing this script)",
    )
    destination = parser.parse_args().directory.resolve()

    prepared: dict[str, tuple[bytes, str]] = {}
    with tempfile.TemporaryDirectory(prefix="jsp285-source-fetch-") as staging_name:
        staging = Path(staging_name)
        for relative, expected_source_hash in SOURCES.items():
            payload = fetch(f"{RAW_ROOT}/{relative}")
            actual = sha256(payload)
            if actual != expected_source_hash:
                raise RuntimeError(
                    f"source digest mismatch for {relative}: expected {expected_source_hash}, got {actual}"
                )
            staged = staging / relative
            staged.parent.mkdir(parents=True, exist_ok=True)
            staged.write_bytes(payload)
            final = transform_core(payload) if relative == CORE_PATH else payload
            expected_final = CORE_FINAL_SHA256 if relative == CORE_PATH else expected_source_hash
            if sha256(final) != expected_final:
                raise RuntimeError(f"final digest mismatch after transformation for {relative}")
            prepared[relative] = (final, expected_final)

        license_payload = fetch(f"{RAW_ROOT}/LICENSE")
        if sha256(license_payload) != LICENSE_SOURCE_SHA256:
            raise RuntimeError("source digest mismatch for src/latest/LICENSE")
        (staging / "LICENSE").write_bytes(license_payload)
        prepared["ErdosProblems/LICENSE"] = (license_payload, LICENSE_SOURCE_SHA256)

    conflicts = []
    for relative, (_, expected) in prepared.items():
        target = destination / relative
        if target.exists() and sha256(target.read_bytes()) != expected:
            conflicts.append(f"{relative}: existing SHA-256 {sha256(target.read_bytes())}, expected {expected}")
    if conflicts:
        raise RuntimeError("refusing to overwrite different local files:\n  " + "\n  ".join(conflicts))

    written = 0
    skipped = 0
    for relative, (payload, expected) in prepared.items():
        target = destination / relative
        if target.exists() and sha256(target.read_bytes()) == expected:
            skipped += 1
            print(f"verified {relative}")
        else:
            atomic_write(target, payload)
            written += 1
            print(f"wrote {relative}")
    print(f"complete: {written} written, {skipped} already verified; pin {PIN}")


if __name__ == "__main__":
    main()
