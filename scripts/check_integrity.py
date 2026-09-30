#!/usr/bin/env python3
"""Check release file hashes and correspondence to the frozen Lean sources."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    failures = []
    manifest = ROOT / "MANIFEST.json"
    if manifest.is_file():
        entries = json.loads(manifest.read_text())["files"]
        for entry in entries:
            path = ROOT / entry["path"]
            if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
                failures.append(entry["path"])
    else:
        entries = []
        failures.append("MANIFEST.json is missing")
    mapping = json.loads((ROOT / "formalization/source_mapping.json").read_text())
    retained = [row for row in mapping["entries"] if row["status"] == "retained_byte_for_byte"]
    for row in retained:
        path = ROOT / row["release_relative_path"]
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != row["original_sha256"]:
            failures.append(row["release_relative_path"])
    report = {"passed": not failures, "release_files_checked": len(entries),
              "frozen_source_entries_checked": len(retained), "failures": sorted(set(failures))}
    print(json.dumps(report, indent=2))
    raise SystemExit(0 if report["passed"] else 1)


if __name__ == "__main__":
    main()
