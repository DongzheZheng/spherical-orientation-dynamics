#!/usr/bin/env python3
"""Reproducible numerical illustrations for the DFL conjectures.

Only NumPy is required.  These computations illustrate theorems proved in the
manuscript; finite Galerkin matrices and quadrature are not used as proofs.
Run: python3 numerics/generate.py   (from any working directory)
"""

from __future__ import annotations

import csv
import json
from pathlib import Path

from output_paths import parse_output_args, output_tree

import numpy as np
from numpy.polynomial.legendre import Legendre, leggauss


HERE = Path(__file__).resolve().parent
OUTPUT_ROOT = HERE.parent / "results"
DATA = OUTPUT_ROOT / "numerics" / "data"


def save_csv(name: str, header: tuple[str, ...], rows: list[tuple[float, ...]]) -> None:
    with (DATA / name).open("w", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(header)
        writer.writerows((f"{x:.14g}" for x in row) for row in rows)


class Quadrature:
    def __init__(self, order: int):
        self.t, self.weight = leggauss(order)
        self.w = 1.0 - self.t * self.t

    def moments(self, d: int, r: float) -> tuple[float, float, float]:
        """Mean, variance, third central moment on S^d with e^{rt} weight."""
        weight = self.weight * self.w ** ((d - 2) / 2) * np.exp(r * (self.t - 1))
        z = np.sum(weight)
        m1 = np.sum(weight * self.t) / z
        m2 = np.sum(weight * self.t**2) / z
        m3 = np.sum(weight * self.t**3) / z
        return float(m1), float(m2 - m1 * m1), float(m3 - 3 * m2 * m1 + 2 * m1**3)


def inverse_feedback(r: float) -> tuple[float, float, float]:
    root = np.sqrt(1 + 4 * r)
    return 2 * r / (root + 1), 1 / root, -2 / root**3


def branch(d: int, r: float, quad: Quadrature) -> tuple[float, float, float]:
    c, cp, cpp = quad.moments(d, r)
    j, jp, jpp = inverse_feedback(r)
    rho = j / c
    slope = jp / c - j * cp / c**2
    curvature = jpp / c - 2 * jp * cp / c**2 - j * cpp / c**2 + 2 * j * cp**2 / c**3
    return rho, slope, curvature


def fold(d: int, quad: Quadrature) -> tuple[float, float, float]:
    left, right = 0.1, 10.0
    assert branch(d, left, quad)[1] < 0 < branch(d, right, quad)[1]
    for _ in range(70):
        middle = (left + right) / 2
        if branch(d, middle, quad)[1] > 0:
            right = middle
        else:
            left = middle
    root = (left + right) / 2
    rho, slope, curvature = branch(d, root, quad)
    assert abs(slope) < 1e-12 and curvature > 0
    return root, rho, curvature


class Galerkin:
    """d=2, first angular amplitude in L²(e^{rt}(1-t²)dt).

    Basis phi_k=P'_{k+1}/sqrt(2(k+1)(k+2)/(2k+3)), orthonormal
    for r=0.  The radial positive spectrum is represented by the SUSY
    partner P_{r,2} with the same weighted form domain and basis.
    """

    def __init__(self, degree: int, quad: Quadrature):
        t = quad.t
        self.quad = quad
        self.phi = np.empty((len(t), degree))
        self.derivative = np.empty((len(t), degree))
        for k in range(degree):
            n = k + 1
            polynomial = Legendre.basis(n)
            norm = np.sqrt(2 * n * (n + 1) / (2 * n + 1))
            self.phi[:, k] = polynomial.deriv()(t) / norm
            self.derivative[:, k] = polynomial.deriv(2)(t) / norm

    def matrices(self, r: float) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
        t, w = self.quad.t, self.quad.w
        p = self.quad.weight * np.exp(r * (t - 1)) * w
        mass = self.phi.T @ (p[:, None] * self.phi)
        kinetic = self.derivative.T @ ((p * w)[:, None] * self.derivative)
        potential = self.phi.T @ ((p * (2 + r * t))[:, None] * self.phi)
        radial_potential = self.phi.T @ ((p * (2 + 2 * r * t))[:, None] * self.phi)
        source = self.phi.T @ p
        return mass, kinetic + potential, kinetic + radial_potential, source

    @staticmethod
    def ground(matrix: np.ndarray, mass: np.ndarray) -> float:
        lower = np.linalg.cholesky(mass)
        left = np.linalg.solve(lower, matrix)
        reduced = np.linalg.solve(lower, left.T).T
        return float(np.linalg.eigvalsh((reduced + reduced.T) / 2)[0])

    def solve(self, r: float) -> tuple[float, float, float, float]:
        mass, angular, radial, source = self.matrices(r)
        gap = self.ground(angular, mass)
        radial_ground = self.ground(radial, mass)
        coeff = np.linalg.solve(angular, source)
        p = self.quad.weight * np.exp(r * (self.quad.t - 1)) * self.quad.w
        h = self.phi @ coeff
        tilde = float(np.sum(p * self.quad.t * h) / np.sum(p * h))
        residual = float(np.linalg.norm(angular @ coeff - source) / np.linalg.norm(source))
        return gap, radial_ground, tilde, residual


def main() -> None:
    global OUTPUT_ROOT, DATA
    args = parse_output_args(__doc__)
    OUTPUT_ROOT, REPORTS, DATA, _ = output_tree(args.output_dir)
    high_quad, low_quad = Quadrature(240), Quadrature(160)
    high, low = Galerkin(24, high_quad), Galerkin(16, low_quad)
    rstar, rhostar, curvature = fold(2, high_quad)
    rstar5, rhostar5, curvature5 = fold(4, high_quad)

    # Fixed-field relaxation: d=2, so the zero-field first positive eigenvalue is 2.
    spectrum_rows = []
    for r in np.linspace(0, 8, 81):
        gap, radial, _, _ = high.solve(float(r))
        spectrum_rows.append((r, gap, radial, radial - gap))
    save_csv("spectrum.csv", ("r", "gap", "radial", "splitting"), spectrum_rows)

    # The self-consistent equilibrium family: n=d+1=3 and 5.
    fold_rows = []
    for r in np.linspace(0.08, 16, 320):
        rho3, slope3, _ = branch(2, float(r), high_quad)
        rho5, _, _ = branch(4, float(r), high_quad)
        fold_rows.append((r, rho3, rho5, slope3))
    save_csv("fold.csv", ("r", "rho3", "rho5", "rho3prime"), fold_rows)

    # GCI comparison and first-order SOH pressure in the distinct linear feedback model.
    gci_rows = []
    for r in np.linspace(0.2, 8, 79):
        c2, _, _ = high_quad.moments(2, float(r))
        c4, _, _ = high_quad.moments(4, float(r))
        _, _, tilde, _ = high.solve(float(r))
        q = r * (c2 - c4)
        pressure = (tilde - c4) / q
        assert 0 < tilde < c4 < c2 and pressure < 0
        gci_rows.append((r, tilde, c4, c2, pressure))
    save_csv("gci_pressure.csv", ("r", "ctilde", "c4", "c2", "pressure"), gci_rows)

    # Fold blow-up for the hysteretic k(J)=J+J² branch, not linear feedback.
    _, _, tilde_star, _ = high.solve(rstar)
    cstar, _, _ = high_quad.moments(2, rstar)
    prefactor = (cstar - tilde_star) * rhostar / (rstar * np.sqrt(2 * curvature))
    branch_rows = []
    for dr in np.geomspace(0.002, 1.0, 120):
        r = rstar + dr
        rho, slope, _ = branch(2, r, high_quad)
        c, _, _ = high_quad.moments(2, r)
        _, _, tilde, _ = high.solve(r)
        theta = 1 / r + (tilde - c) * rho / (r * slope)
        assert theta < 0
        delta_rho = rho - rhostar
        branch_rows.append((delta_rho, -theta, prefactor / np.sqrt(delta_rho)))
    save_csv("fold_pressure.csv", ("delta_rho", "minus_theta", "fold_asymptotic"), branch_rows)

    # Directional first-order symbol for linear feedback at r=2.
    rangle = 2.0
    c2_angle, _, _ = high_quad.moments(2, rangle)
    c4_angle, _, _ = high_quad.moments(4, rangle)
    _, _, tilde_angle, _ = high.solve(rangle)
    q_angle = rangle * (c2_angle - c4_angle)
    gamma_angle = c2_angle / q_angle
    pressure_angle = (tilde_angle - c4_angle) / q_angle
    theta_crit = np.arctan((gamma_angle - tilde_angle) / (2 * np.sqrt(-pressure_angle * c2_angle)))
    angle_rows = []
    for theta_deg in np.linspace(0, 90, 181):
        angle = np.deg2rad(theta_deg)
        discriminant = (gamma_angle - tilde_angle) ** 2 * np.cos(angle) ** 2 + 4 * pressure_angle * c2_angle * np.sin(angle) ** 2
        angle_rows.append((theta_deg, discriminant))
    save_csv("angle.csv", ("theta_deg", "discriminant"), angle_rows)

    # Two independent quadrature orders and two Galerkin degrees give the
    # reported discretization sensitivity.  These are not certified bounds.
    checks = []
    for r in (0.0, 0.5, 2.0, 5.0, 8.0):
        g_hi, p_hi, t_hi, residual = high.solve(r)
        g_lo, p_lo, t_lo, _ = low.solve(r)
        checks.append({
            "r": r,
            "gap_K24_N240": g_hi,
            "gap_K16_N160": g_lo,
            "gap_absolute_change": abs(g_hi - g_lo),
            "radial_absolute_change": abs(p_hi - p_lo),
            "ctilde_absolute_change": abs(t_hi - t_lo),
            "linear_system_relative_residual": residual,
        })
    fold_low = fold(2, low_quad)
    analytic_checks = []
    for r in (0.5, 2.0, 8.0):
        c2_check, cp2_check, _ = high_quad.moments(2, r)
        # On S² the partition function is sinh(r)/r, so this is an
        # independent normalization/sign check for the quadrature.
        exact_c2 = 1 / np.tanh(r) - 1 / r
        riccati_cp2 = 1 - 2 * c2_check / r - c2_check**2
        analytic_checks.append({
            "r": r,
            "S2_mean_vs_coth_minus_inverse_r": abs(c2_check - exact_c2),
            "variance_vs_Riccati_identity": abs(cp2_check - riccati_cp2),
        })
    report = {
        "method": "Gauss-Legendre quadrature; d=2 Legendre-derivative Galerkin",
        "high_resolution": {"quadrature_nodes": 240, "Galerkin_dimension": 24},
        "low_resolution": {"quadrature_nodes": 160, "Galerkin_dimension": 16},
        "fold_n3": {"r_star": rstar, "rho_star": rhostar, "R_second_derivative": curvature},
        "fold_n5": {"r_star": rstar5, "rho_star": rhostar5, "R_second_derivative": curvature5},
        "fold_n3_resolution_change": {
            "r_star": abs(rstar - fold_low[0]),
            "rho_star": abs(rhostar - fold_low[1]),
            "R_second_derivative": abs(curvature - fold_low[2]),
        },
        "linear_feedback_r2": {
            "rho": rangle / c2_angle,
            "pressure": pressure_angle,
            "theta_crit_deg": float(np.rad2deg(theta_crit)),
            "transverse_discriminant": 4 * pressure_angle * c2_angle,
        },
        "hysteretic_fold_asymptotic_prefactor": prefactor,
        "analytic_checks": analytic_checks,
        "resolution_checks": checks,
    }
    (REPORTS / "convergence.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
