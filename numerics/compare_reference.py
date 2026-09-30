#!/usr/bin/env python3
"""Compare regenerated CSV files and check reports with the supplied references.

The tolerance permits small differences between BLAS and plotting environments.
Certified continuum error bounds require additional numerical analysis.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent


def compare_results(output_dir: Path, *, atol: float = 1e-9, rtol: float = 1e-8) -> dict:
    generated = output_dir.resolve() / "numerics"
    failures: list[str] = []
    csv_results: list[dict] = []
    report_results: list[dict] = []
    for reference in sorted((HERE / "data").glob("*.csv")):
        target = generated / "data" / reference.name
        if not target.is_file():
            failures.append(f"Missing generated file: {target.name}")
            continue
        with reference.open(newline="") as stream:
            expected = list(csv.reader(stream))
        with target.open(newline="") as stream:
            observed = list(csv.reader(stream))
        if not observed or observed[0] != expected[0] or len(observed) != len(expected):
            failures.append(f"CSV schema/row count differs: {reference.name}")
            continue
        max_error = 0.0
        numeric_count = 0
        for row_index, (a, b) in enumerate(zip(expected[1:], observed[1:]), start=2):
            if len(a) != len(b):
                failures.append(f"CSV column count differs: {reference.name}:{row_index}")
                continue
            for field_index, (x, y) in enumerate(zip(a, b)):
                try:
                    xx, yy = float(x), float(y)
                except ValueError:
                    if x != y:
                        failures.append(f"CSV text differs: {reference.name}:{row_index}:{field_index}")
                    continue
                numeric_count += 1
                if math.isnan(xx) and math.isnan(yy):
                    continue
                if not np.isclose(xx, yy, atol=atol, rtol=rtol):
                    failures.append(f"CSV numeric value differs: {reference.name}:{row_index}:{field_index}")
                if math.isfinite(xx) and math.isfinite(yy):
                    max_error = max(max_error, abs(xx - yy))
        csv_results.append({"file": reference.name, "data_rows": len(expected)-1,
                            "numeric_values": numeric_count, "max_absolute_difference": max_error})

    def compare_json(expected, observed, location: str, numeric_errors: list[float]):
        if isinstance(expected, dict):
            if not isinstance(observed, dict) or expected.keys() != observed.keys():
                failures.append(f"JSON keys differ: {location}")
                return
            for key, value in expected.items():
                # Output locations are handled separately from scientific result fields.
                if key == "output_pdf":
                    continue
                compare_json(value, observed[key], f"{location}.{key}", numeric_errors)
        elif isinstance(expected, list):
            if not isinstance(observed, list) or len(expected) != len(observed):
                failures.append(f"JSON list differs: {location}")
                return
            for index, (x, y) in enumerate(zip(expected, observed)):
                compare_json(x, y, f"{location}[{index}]", numeric_errors)
        elif isinstance(expected, (int, float)) and not isinstance(expected, bool):
            if not isinstance(observed, (int, float)) or not np.isclose(expected, observed, atol=atol, rtol=rtol):
                failures.append(f"JSON numerical value differs: {location}")
            if isinstance(observed, (int, float)):
                numeric_errors.append(abs(expected - observed))
        elif expected != observed:
            failures.append(f"JSON value differs: {location}")

    for reference in sorted((HERE / "reference_checks").glob("*.json")):
        target = generated / reference.name
        if not target.is_file():
            failures.append(f"Missing generated report: {reference.name}")
            continue
        errors: list[float] = []
        compare_json(json.loads(reference.read_text()), json.loads(target.read_text()), reference.name, errors)
        report_results.append({"file": reference.name, "numeric_values": len(errors),
                               "max_absolute_difference": max(errors, default=0.0)})
    return {"passed": not failures, "absolute_tolerance": atol, "relative_tolerance": rtol,
            "csv_files": csv_results, "check_reports": report_results, "failures": failures}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=HERE.parent / "results",
                        help="Root used with the numerical programs' --output-dir option.")
    parser.add_argument("--report", type=Path, help="Optional JSON comparison report destination.")
    args = parser.parse_args()
    report = compare_results(args.output_dir)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    raise SystemExit(0 if report["passed"] else 1)


if __name__ == "__main__":
    main()
