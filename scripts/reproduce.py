#!/usr/bin/env python3
"""Regenerate all numerical experiments and compare the reference results."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "results")
    parser.add_argument("--figures", action="store_true", help="Also compile the ten TeX figures.")
    args = parser.parse_args()
    output = args.output_dir.expanduser().resolve()
    if output == ROOT or ROOT in output.parents and output.parts[len(ROOT.parts)] in {
        "formalization", "numerics", "figures", "evidence", "docs", "scripts"
    }:
        parser.error("Use results/ or a separate output directory to preserve release files.")
    runs = []
    for name in ("generate", "phase_dynamics", "transport_atlas", "orientation_sphere", "energy_landscape_3d"):
        command = [sys.executable, str(ROOT / "numerics" / f"{name}.py"), "--output-dir", str(output)]
        if name == "transport_atlas":
            command.append("--skip-tex")
        print(f"Running {name}.py", flush=True)
        start = time.perf_counter()
        result = subprocess.run(command, capture_output=True, text=True)
        runs.append({"script": f"{name}.py", "seconds": round(time.perf_counter() - start, 4),
                     "exit_code": result.returncode})
        if result.returncode:
            sys.stderr.write(result.stdout + result.stderr)
            raise SystemExit(result.returncode)
    comparison = subprocess.run([sys.executable, str(ROOT / "numerics" / "compare_reference.py"),
                                 "--output-dir", str(output), "--report",
                                 str(output / "reference_comparison.json")], capture_output=True, text=True)
    if comparison.returncode:
        sys.stderr.write(comparison.stdout + comparison.stderr)
        raise SystemExit(comparison.returncode)
    from pdf_metadata import clear_pdf_metadata
    for pdf in (output / "figures").glob("*.pdf"):
        clear_pdf_metadata(pdf)
    if args.figures:
        subprocess.run([sys.executable, str(ROOT / "scripts" / "build_figures.py"),
                        "--output-dir", str(output)], check=True)
    (output / "reproduction.json").write_text(json.dumps({"runs": runs, "passed": True,
        "reference_comparison": "reference_comparison.json", "tex_figures": args.figures}, indent=2) + "\n")
    print("Passed: 20 CSVs and 5 validation reports. Outputs are in the selected results directory.")


if __name__ == "__main__":
    main()
