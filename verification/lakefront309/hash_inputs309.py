"""Single-file SHA256 helper; no compiler, mutation, or external commands."""
from __future__ import annotations

import hashlib
import pathlib
import sys


def main() -> int:
    if len(sys.argv) != 2:
        raise ValueError("expected exactly one existing file")
    path = pathlib.Path(sys.argv[1]).resolve(strict=True)
    if not path.is_file():
        raise ValueError("input must be a regular file")
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    print(digest.hexdigest())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
