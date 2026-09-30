#!/usr/bin/env python3
"""Run the supplied reference comparator from the package root."""
from pathlib import Path
import runpy

runpy.run_path(str(Path(__file__).resolve().parents[1] / "numerics" / "compare_reference.py"),
               run_name="__main__")
