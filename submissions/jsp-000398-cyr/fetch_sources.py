#!/usr/bin/env python3
"""Fetch the pinned Dirichlet proof, preserving and checking its exact bytes."""
from pathlib import Path
import hashlib
import json
import os
import tempfile
import urllib.request


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "external-proof-sources.json").read_text())
    for entry in manifest["files"]:
        destination = root / entry["path"]
        if destination.exists():
            if digest(destination.read_bytes()) != entry["adapted_sha256"]:
                raise RuntimeError(f"Preserving changed file: {entry['path']}")
            print(f"Verified {entry['path']}")
            continue
        request = urllib.request.Request(
            entry["url"], headers={"User-Agent": "JSP398-source-reproducer"}
        )
        with urllib.request.urlopen(request, timeout=60) as response:
            source = response.read()
        if digest(source) != entry["source_sha256"]:
            raise RuntimeError(f"Downloaded source hash mismatch: {entry['path']}")
        heading = b"# A finite simultaneous Dirichlet approximation lemma\n"
        note = (
            "\nCopied from the pinned plby Erdős 485 development for replay; provenance and\n"
            "license verification are maintained by the campaign owner.\n"
        ).encode()
        if source.count(heading) != 1:
            raise RuntimeError("Expected unique source heading")
        source = source.replace(heading, heading + note, 1)
        if digest(source) != entry["adapted_sha256"]:
            raise RuntimeError(f"Adapted source hash mismatch: {entry['path']}")
        destination.parent.mkdir(parents=True, exist_ok=True)
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(dir=destination.parent, delete=False) as output:
                temporary = Path(output.name)
                output.write(source)
            os.replace(temporary, destination)
        finally:
            if temporary is not None and temporary.exists():
                temporary.unlink()
        print(f"Fetched and verified {entry['path']}")


if __name__ == "__main__":
    main()
