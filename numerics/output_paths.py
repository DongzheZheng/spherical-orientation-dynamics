"""Portable output locations shared by numerical command-line programs."""

from __future__ import annotations

import argparse
from pathlib import Path


def parse_output_args(description: str | None, *, allow_skip_tex: bool = False):
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument(
        "--output-dir", type=Path,
        default=Path(__file__).resolve().parent.parent / "results",
        help="Regeneration root (default: package-root/results). Reference files are not overwritten.",
    )
    if allow_skip_tex:
        parser.add_argument(
            "--skip-tex", action="store_true",
            help="Generate CSV data and validation reports without invoking pdflatex.",
        )
    return parser.parse_args()


def output_tree(output_dir: Path):
    root = output_dir.expanduser().resolve()
    package_root = Path(__file__).resolve().parent.parent
    if root == package_root:
        raise ValueError("Choose a separate output root; package reference files must be preserved.")
    reports = root / "numerics"
    data = reports / "data"
    figures = root / "figures"
    data.mkdir(parents=True, exist_ok=True)
    figures.mkdir(parents=True, exist_ok=True)
    return root, reports, data, figures
