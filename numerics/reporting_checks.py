#!/usr/bin/env python3
"""Independent temporal and spatial refinements for the ordered basin.

The Scharfetter--Gummel solver in phase_dynamics supplies all trajectories.
This program writes reporting_checks.json to the selected output directory.
"""

from __future__ import annotations

import json

from output_paths import output_tree, parse_output_args
from phase_dynamics import run_pde


RHO = 1.9
R_INITIAL = 1.8


def observation(cells: int, dt: float, end: float) -> dict:
    record = run_pde(RHO, R_INITIAL, cells=cells, dt=dt, end=end)
    return {
        "rho": RHO,
        "r_initial": R_INITIAL,
        "end": end,
        "cells": cells,
        "dt": dt,
        "terminal_polarization": record["terminal_polarization"],
        "terminal_energy_relative_uniform": record["terminal_energy_relative_uniform"],
        "max_mass_error": record["max_mass_error"],
        "max_energy_step_increase": record["max_energy_step_increase"],
        "minimum_density": record["minimum_density"],
    }


def refinement_summary(records: list[dict]) -> dict:
    first = abs(records[0]["terminal_polarization"]
                - records[1]["terminal_polarization"])
    second = abs(records[1]["terminal_polarization"]
                 - records[2]["terminal_polarization"])
    return {
        "coarse_fine_polarization_difference": first,
        "fine_finer_polarization_difference": second,
        "successive_polarization_difference_ratio": first / second,
    }


def main() -> None:
    args = parse_output_args(__doc__)
    _, reports, _, _ = output_tree(args.output_dir)
    temporal = [observation(160, dt, 10.0) for dt in (0.08, 0.04, 0.02)]
    spatial = [observation(cells, 0.02, 40.0) for cells in (80, 160, 320)]
    for record in temporal + spatial:
        assert record["max_mass_error"] < 1e-9
        assert record["max_energy_step_increase"] < 1e-11
        assert record["minimum_density"] > 0
    report = {
        "model": {
            "embedding_dimension": 3,
            "sphere_dimension": 2,
            "alignment_frequency": "nu(J)=J",
            "angular_noise": "tau_noise(J)=1/(1+J)",
            "axisymmetric_initial_density": "rho*M_r_initial",
            "initial_polarization_direction": "positive axis",
            "solver": "Scharfetter-Gummel finite volume; lagged-J implicit Euler",
            "boundary_condition": "zero flux at t=-1 and t=1",
        },
        "temporal_refinement": {
            "fixed_cells": 160,
            "end": 10.0,
            "records": temporal,
            **refinement_summary(temporal),
        },
        "spatial_refinement": {
            "fixed_dt": 0.02,
            "end": 40.0,
            "records": spatial,
            **refinement_summary(spatial),
        },
        "interpretation": "Refinement differences quantify observed numerical sensitivity.",
    }
    (reports / "reporting_checks.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
