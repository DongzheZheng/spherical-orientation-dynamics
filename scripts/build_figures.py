#!/usr/bin/env python3
"""Compile the ten English standalone TeX figures using regenerated tables."""
from __future__ import annotations

import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from pdf_metadata import clear_pdf_metadata

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    output = args.output_dir.expanduser().resolve()
    if output == ROOT or ROOT in output.parents and output.parts[len(ROOT.parts)] in {
        "formalization", "numerics", "figures", "evidence", "docs", "scripts"
    }:
        parser.error("Use results/ or a separate output directory to preserve release files.")
    if not (output / "numerics" / "data" / "spectrum.csv").is_file():
        parser.error("Regenerate the numerical tables first with scripts/reproduce.py.")
    compiler = shutil.which("pdflatex")
    if not compiler:
        parser.error("pdflatex is required; install a TeX distribution with standalone, TikZ and PGFPlots.")
    destination = output / "figures"
    destination.mkdir(parents=True, exist_ok=True)
    for source in sorted((ROOT / "figures" / "source").glob("*.tex")):
        editable = destination / source.name
        shutil.copyfile(source, editable)
        with tempfile.TemporaryDirectory(prefix="dfl-figure-") as temporary:
            result = subprocess.run([compiler, "-interaction=nonstopmode", "-halt-on-error",
                                     "-output-directory", temporary, editable.name],
                                    cwd=destination, capture_output=True, text=True)
            if result.returncode:
                raise RuntimeError(f"Figure compilation failed: {source.name}\n{result.stdout[-6000:]}")
            pdf = destination / f"{source.stem}.pdf"
            shutil.copyfile(Path(temporary) / pdf.name, pdf)
        clear_pdf_metadata(pdf)
        print(f"Built {pdf.name}")


if __name__ == "__main__":
    main()
