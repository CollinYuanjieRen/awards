#!/usr/bin/env python3
"""Fetch the pinned external proof source and verify every source byte."""

from pathlib import Path
import hashlib
import json
import os
import tempfile
import urllib.request


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
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
            entry["url"], headers={"User-Agent": "JSP360-source-reproducer"}
        )
        with urllib.request.urlopen(request, timeout=60) as response:
            source = response.read()
        if digest(source) != entry["source_sha256"]:
            raise RuntimeError(f"Downloaded source hash mismatch: {entry['path']}")

        source_import = entry["source_import"].encode()
        adapted_import = entry["adapted_import"].encode()
        if source.count(source_import) != 1:
            raise RuntimeError(f"Expected one exact import replacement: {entry['path']}")
        adapted = source.replace(source_import, adapted_import)
        if digest(adapted) != entry["adapted_sha256"]:
            raise RuntimeError(f"Adapted source hash mismatch: {entry['path']}")

        destination.parent.mkdir(parents=True, exist_ok=True)
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(dir=destination.parent, delete=False) as output:
                temporary = Path(output.name)
                output.write(adapted)
            os.replace(temporary, destination)
        finally:
            if temporary is not None and temporary.exists():
                temporary.unlink()
        print(f"Fetched and verified {entry['path']}")


if __name__ == "__main__":
    main()
