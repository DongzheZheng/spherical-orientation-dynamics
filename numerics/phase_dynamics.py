#!/usr/bin/env python3
"""Energy landscape and axisymmetric *original-PDE* dynamics for DFL k(J)=J+J².

This script does not impose a von Mises--Fisher evolution ansatz.  Initial
densities are vMF, but the dynamics solves the n=3 axial PDE for f(t,tau),
where t=omega dot Omega.  It uses a positivity-preserving Scharfetter--Gummel
finite-volume flux and an implicit diffusion/drift step with J lagged by one
time step.  The equilibrium landscape is exact up to scalar root finding:
for a fixed first moment, vMF minimizes the entropy by relative entropy.

Requires NumPy only.  Run: python3 numerics/phase_dynamics.py
"""

from __future__ import annotations

import csv
import json
from pathlib import Path

from output_paths import parse_output_args, output_tree

import numpy as np


HERE = Path(__file__).resolve().parent
OUTPUT_ROOT = HERE.parent / "results"
DATA = OUTPUT_ROOT / "numerics" / "data"


def write_csv(name: str, columns: tuple[str, ...], rows: list[tuple[float, ...]]) -> None:
    with (DATA / name).open("w", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(columns)
        writer.writerows((f"{x:.15g}" for x in row) for row in rows)


def c3(r: float | np.ndarray) -> float | np.ndarray:
    """Mean polar cosine on S², with a cancellation-free small-r branch."""
    x = np.asarray(r, dtype=float)
    result = np.empty_like(x)
    small = np.abs(x) < 0.02
    y = x[small]
    result[small] = y / 3 - y**3 / 45 + 2 * y**5 / 945 - y**7 / 4725
    y = x[~small]
    result[~small] = 1 / np.tanh(y) - 1 / y
    return float(result) if result.ndim == 0 else result


def c3_prime(r: float) -> float:
    if abs(r) < 0.02:
        return 1 / 3 - r**2 / 15 + 2 * r**4 / 189 - r**6 / 675
    return 1 / r**2 - 1 / np.sinh(r) ** 2


def log_z3(r: float | np.ndarray) -> float | np.ndarray:
    x = np.asarray(r, dtype=float)
    result = np.empty_like(x)
    small = np.abs(x) < 0.02
    y = x[small]
    result[small] = y**2 / 6 - y**4 / 180 + y**6 / 2835 - y**8 / 37800
    y = x[~small]
    result[~small] = np.log(np.sinh(y) / y)
    return float(result) if result.ndim == 0 else result


def j_of_r(r: float | np.ndarray) -> float | np.ndarray:
    return 2 * np.asarray(r) / (1 + np.sqrt(1 + 4 * np.asarray(r)))


def R(r: float) -> float:
    return float(j_of_r(r) / c3(r))


def R_prime(r: float) -> float:
    c = c3(r)
    j = float(j_of_r(r))
    jp = 1 / np.sqrt(1 + 4 * r)
    return float(jp / c - j * c3_prime(r) / c**2)


def phi(J: float | np.ndarray) -> float | np.ndarray:
    return J**2 / 2 + J**3 / 3


def delta_energy(rho: float, r: float | np.ndarray) -> float | np.ndarray:
    """F(rho M_r)-F(rho), with J=rho*c3(r)."""
    c = c3(r)
    return -rho * log_z3(r) + rho * np.asarray(r) * c - phi(rho * c)


def bisect(fun, left: float, right: float, *, iters: int = 90) -> float:
    fl = fun(left)
    fr = fun(right)
    assert fl * fr < 0, (left, right, fl, fr)
    for _ in range(iters):
        middle = (left + right) / 2
        fm = fun(middle)
        if fl * fm <= 0:
            right, fr = middle, fm
        else:
            left, fl = middle, fm
    return (left + right) / 2


def ordered_roots(rho: float, rstar: float) -> tuple[float, float]:
    assert rho > R(rstar) and rho < 3
    return (bisect(lambda r: R(r) - rho, 0.001, rstar),
            bisect(lambda r: R(r) - rho, rstar, 20))


def bernoulli(x: float) -> float:
    if abs(x) < 1e-4:
        return 1 - x / 2 + x**2 / 12 - x**4 / 720
    return x / np.expm1(x)


def tridiagonal(lower: np.ndarray, diagonal: np.ndarray,
                upper: np.ndarray, rhs: np.ndarray) -> np.ndarray:
    """Thomas solver. lower[0] and upper[-1] are unused and zero."""
    n = len(rhs)
    d = diagonal.copy()
    b = rhs.copy()
    for i in range(1, n):
        factor = lower[i] / d[i - 1]
        d[i] -= factor * upper[i - 1]
        b[i] -= factor * b[i - 1]
    out = np.empty(n)
    out[-1] = b[-1] / d[-1]
    for i in range(n - 2, -1, -1):
        out[i] = (b[i] - upper[i] * out[i + 1]) / d[i]
    return out


def metrics(f: np.ndarray, t: np.ndarray, h: float, rho: float) -> tuple[float, float, float]:
    mass = float(h * np.sum(f) / 2)
    J = float(h * np.dot(t, f) / 2)
    energy = float(h * np.sum(f * np.log(f)) / 2 - phi(J) - rho * np.log(rho))
    return mass, J / rho, energy


def run_pde(rho: float, r_initial: float, *, cells: int, dt: float, end: float,
            sample_every: int = 20, profiles_at: tuple[float, ...] = ()) -> dict:
    """Solve original n=3 axisymmetric PDE with no-flux t=±1 endpoints.

    ∂tau f = ∂t[(1-t²)(D(J) ∂t f - J f)],
    J = (1/2)∫t f dt, D(J)=(1+J)^(-1).
    """
    h = 2 / cells
    t = -1 + (np.arange(cells) + 0.5) * h
    face = -1 + np.arange(1, cells) * h
    z = h * np.sum(np.exp(r_initial * t)) / 2
    f = rho * np.exp(r_initial * t) / z
    step_count = round(end / dt)
    assert abs(step_count * dt - end) < 1e-9
    rows = []
    profile = {}
    initial_mass, _, initial_energy = metrics(f, t, h, rho)
    max_mass_error = abs(initial_mass - rho)
    max_energy_increase = 0.0
    minimum_density = float(f.min())
    previous_energy = initial_energy
    profile_steps = {round(time / dt): time for time in profiles_at}
    for step in range(step_count + 1):
        tau = step * dt
        mass, polarization, energy = metrics(f, t, h, rho)
        max_mass_error = max(max_mass_error, abs(mass - rho))
        max_energy_increase = max(max_energy_increase, energy - previous_energy)
        minimum_density = min(minimum_density, float(np.min(f)))
        previous_energy = energy
        if step % sample_every == 0 or step == step_count:
            rows.append((tau, polarization, energy))
        if step in profile_steps:
            profile[profile_steps[step]] = f.copy()
        if step == step_count:
            break

        J = rho * polarization
        D = 1 / (1 + J)
        peclet = J * h / D
        K_over_h = D * (1 - face**2) / h
        a = K_over_h * bernoulli(-peclet)
        b = K_over_h * bernoulli(peclet)
        factor = dt / h
        diagonal = np.ones(cells)
        diagonal[:-1] += factor * a
        diagonal[1:] += factor * b
        lower = np.zeros(cells)
        upper = np.zeros(cells)
        lower[1:] = -factor * a
        upper[:-1] = -factor * b
        f = tridiagonal(lower, diagonal, upper, f)

    return {
        "rho": rho, "r_initial": r_initial, "cells": cells, "dt": dt,
        "end": end, "t": t, "rows": rows, "profiles": profile,
        "max_mass_error": max_mass_error,
        "max_energy_step_increase": max_energy_increase,
        "minimum_density": minimum_density,
        "terminal_polarization": rows[-1][1],
        "terminal_energy_relative_uniform": rows[-1][2],
    }


def make_landscape() -> dict:
    rstar = bisect(R_prime, 0.4, 5)
    rhostar = R(rstar)
    rmaxwell = bisect(lambda r: delta_energy(R(r), r), rstar + 0.01, 4)
    rhomaxwell = R(rmaxwell)
    rho_bi = 1.9
    lower, upper = ordered_roots(rho_bi, rstar)

    # Sample the exact (relative-entropy) lower envelope at fixed J.
    values = np.linspace(0, 5.3, 450)
    densities = (1.8, rhostar, rho_bi, rhomaxwell, 2.0)
    rows = []
    for r in values:
        m = c3(float(r))
        rows.append((m, *(float(delta_energy(rho, r)) for rho in densities)))
    write_csv("phase_landscape.csv",
              ("m", "rho180", "rhostar", "rho190", "rhomaxwell", "rho200"), rows)

    # Local-minimum and saddle branches of positive ordered equilibria.
    branch_rows = []
    for r in np.sort(np.r_[np.linspace(0.001, 13, 600), rstar, rmaxwell]):
        rho = R(float(r))
        m = c3(float(r))
        branch_rows.append((r, rho, m,
                            m if r < rstar else float("nan"),
                            m if rstar <= r <= rmaxwell else float("nan"),
                            m if r >= rmaxwell else float("nan")))
    write_csv("phase_branches.csv",
              ("r", "rho", "m", "saddle_m", "metastable_m", "global_m"),
              branch_rows)
    return {
        "r_star": rstar, "rho_star": rhostar, "m_star": c3(rstar),
        "r_Maxwell": rmaxwell, "rho_Maxwell": rhomaxwell,
        "m_Maxwell": c3(rmaxwell),
        "rho_1p9_lower_r": lower, "rho_1p9_upper_r": upper,
        "rho_1p9_lower_m": c3(lower), "rho_1p9_upper_m": c3(upper),
        "rho_1p9_saddle_height": delta_energy(rho_bi, lower),
        "rho_1p9_ordered_depth": delta_energy(rho_bi, upper),
        "fold_height": delta_energy(rhostar, rstar),
        "Maxwell_equal_depth_residual": delta_energy(rhomaxwell, rmaxwell),
        "comparison_previous_r_star": abs(rstar - 1.901364387725759),
        "comparison_previous_rho_star": abs(rhostar - 1.860214757027207),
    }


def make_dynamics(info: dict) -> dict:
    # Two basins at one fixed mass; both initial states are positive vMF.
    # r=1.0 is below the ordered saddle; r=1.8 is above it.
    cases = (
        ("uniform_basin", 1.9, 1.0, 80.0),
        ("ordered_basin", 1.9, 1.8, 80.0),
        ("critical_small", 3.0, 0.03, 120.0),
        ("critical_large", 3.0, 0.06, 120.0),
    )
    all_rows = []
    results = {}
    for name, rho, r0, end in cases:
        record = run_pde(rho, r0, cells=160, dt=0.04, end=end,
                         sample_every=5,
                         profiles_at=(0, 2, 10, end) if name == "ordered_basin" else ())
        results[name] = record
        all_rows.extend((name, *row) for row in record["rows"])
    with (DATA / "quench_dynamics.csv").open("w", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(("case", "tau", "m", "deltaF"))
        for row in all_rows:
            writer.writerow((row[0], *(f"{x:.15g}" for x in row[1:])))

    # Split CSV avoids reliance on pgfplots string filters.
    for name, record in results.items():
        write_csv("quench_" + name + ".csv", ("tau", "m", "deltaF"), record["rows"])
    profile = results["ordered_basin"]
    write_csv("quench_profiles.csv", ("t", "initial", "tau2", "tau10", "final"),
              list(zip(profile["t"], profile["profiles"][0], profile["profiles"][2],
                       profile["profiles"][10], profile["profiles"][80])))

    # Independent halving check for the two-basin trajectories at a finite time.
    # The terminal states are not used as a formal error bound; the comparison
    # is a measured space-time discretization sensitivity.
    convergence = {}
    for name, rho, r0 in (("uniform_basin", 1.9, 1.0),
                          ("ordered_basin", 1.9, 1.8)):
        coarse = run_pde(rho, r0, cells=80, dt=0.08, end=40.0)
        fine = run_pde(rho, r0, cells=160, dt=0.04, end=40.0)
        finer = run_pde(rho, r0, cells=320, dt=0.02, end=40.0)
        convergence[name] = {
            "tau": 40.0,
            "m_N80_dt008": coarse["terminal_polarization"],
            "m_N160_dt004": fine["terminal_polarization"],
            "m_N320_dt002": finer["terminal_polarization"],
            "coarse_fine_difference": abs(coarse["terminal_polarization"] - fine["terminal_polarization"]),
            "fine_finer_difference": abs(fine["terminal_polarization"] - finer["terminal_polarization"]),
        }

    return {
        "scheme": "axisymmetric original PDE; Scharfetter-Gummel finite volume; lagged-J implicit Euler",
        "reference_grid": {"cells": 160, "dt": 0.04},
        "cases": {
            name: {
                "rho": record["rho"], "r_initial": record["r_initial"],
                "end": record["end"],
                "max_mass_error": record["max_mass_error"],
                "max_energy_step_increase": record["max_energy_step_increase"],
                "minimum_density": record["minimum_density"],
                "terminal_polarization": record["terminal_polarization"],
                "terminal_energy_relative_uniform": record["terminal_energy_relative_uniform"],
            } for name, record in results.items()
        },
        "space_time_refinement": convergence,
    }


def main() -> None:
    global OUTPUT_ROOT, DATA
    args = parse_output_args(__doc__)
    OUTPUT_ROOT, REPORTS, DATA, _ = output_tree(args.output_dir)
    landscape = make_landscape()
    dynamics = make_dynamics(landscape)
    report = {"landscape": landscape, "dynamics": dynamics}
    with (REPORTS / "phase_dynamics_check.json").open("w") as file:
        json.dump(report, file, indent=2, ensure_ascii=False)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
