#!/usr/bin/env python3
"""Four reproducible vector figures for the DFL/JPhysA physical narrative.

Run from any directory: python3 numerics/transport_atlas.py

The code evaluates coefficients of the *first-order* SOH principal symbol.  A
negative discriminant is not a claim about the spatial kinetic equation, nor
about the SOH system with K_2 > 0.  The homogeneous rate q*lambda is the
proved guaranteed rate, not an exact nonlinear spectral value.
"""

from __future__ import annotations

import csv
import json
import math
import subprocess
from pathlib import Path

from output_paths import parse_output_args, output_tree

import numpy as np

from generate import Galerkin, Quadrature, fold, inverse_feedback


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUTPUT_ROOT = ROOT / "results"
DATA = OUTPUT_ROOT / "numerics" / "data"
FIGURES = OUTPUT_ROOT / "figures"

QUAD_HIGH = Quadrature(240)
QUAD_LOW = Quadrature(160)
GAL_HIGH = Galerkin(24, QUAD_HIGH)
GAL_LOW = Galerkin(16, QUAD_LOW)


def save_csv(name: str, columns: tuple[str, ...], rows: list[tuple[float, ...]]) -> None:
    with (DATA / name).open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(columns)
        writer.writerows((f"{value:.15g}" for value in row) for row in rows)


def spherical_c(r: float) -> float:
    """S^2 mean coth(r)-1/r, with its regular Taylor limit at zero."""
    if r < 0.01:
        return r / 3 - r**3 / 45 + 2 * r**5 / 945 - r**7 / 4725
    return 1 / math.tanh(r) - 1 / r


def spherical_cp(r: float) -> float:
    if r < 0.01:
        return 1 / 3 - r * r / 15 + 2 * r**4 / 189 - r**6 / 675
    return 1 / r**2 - 1 / math.sinh(r) ** 2


def geometry(r: float, gal: Galerkin = GAL_HIGH, quad: Quadrature = QUAD_HIGH) -> dict[str, float]:
    c = spherical_c(r)
    cp = spherical_cp(r)
    c_plus = quad.moments(4, r)[0]
    gap, _, c_tilde, residual = gal.solve(r)
    assert 0 < c_tilde < c_plus < c
    return {
        "c": c,
        "cp": cp,
        "c_plus": c_plus,
        "c_tilde": c_tilde,
        "gap": gap,
        "residual": residual,
        "e": r * cp / c,
        "g": c_plus - c_tilde,
    }


def model_at_r(model: str, r: float, *, tau: float = 0.3, epsilon: float = 1.0) -> dict[str, float]:
    g = geometry(r)
    if model == "linear":
        j, A = r, 1.0
    elif model == "hysteresis":
        j, jp, _ = inverse_feedback(r)
        A = r * jp / j
    elif model == "regularized":
        assert tau > 0 and 0 < r < 1 / tau
        j = epsilon * tau * r / (1 - tau * r)
        A = 1 / (1 - tau * r)
    else:
        raise ValueError(model)
    D = A - g["e"]
    assert D > 0, "Only a stable increasing density branch is plotted"
    rho = j / g["c"]
    theta = 1 / r + (g["c_tilde"] - g["c"]) / D
    gamma = g["c"] * A / D
    if model == "linear":
        q = r * (g["c"] - g["c_plus"])
        check = (g["c_tilde"] - g["c_plus"]) / q
        # Near r=0 both forms cancel terms of size 1/r; D is O(r^2).
        assert abs(theta - check) < max(3e-12, 1e-10 / D)
    if model == "regularized":
        check = (tau / (1 - tau * r) - g["g"]) / D
        assert abs(theta - check) < max(3e-12, 1e-10 / D)
    return {**g, "r": r, "rho": rho, "A": A, "D": D, "Theta": theta, "gamma": gamma}


def critical_angle(state: dict[str, float]) -> float | None:
    if state["Theta"] >= 0:
        return None
    return math.degrees(math.atan((state["gamma"] - state["c_tilde"]) /
                                  (2 * math.sqrt(-state["c"] * state["Theta"]))))


def wave_speeds(state: dict[str, float], angle_deg: float) -> tuple[float, float, float, float]:
    angle = math.radians(angle_deg)
    s = math.cos(angle)
    p = math.sin(angle)
    disc = (state["gamma"] - state["c_tilde"]) ** 2 * s * s + 4 * state["c"] * state["Theta"] * p * p
    trace = (state["gamma"] + state["c_tilde"]) * s
    plus = (trace + math.sqrt(max(0, disc))) / 2
    minus = (trace - math.sqrt(max(0, disc))) / 2
    imaginary = math.sqrt(max(0, -disc)) / 2
    return plus, minus, imaginary, disc


def regularized_density_ratio(r: float, tau: float) -> float:
    if r == 0:
        return 1.0
    return r / (3 * spherical_c(r) * (1 - tau * r))


def r_at_density_ratio(ratio: float, tau: float) -> float:
    assert ratio > 1 and tau > 0
    left, right = 0.0, (1 - 1e-10) / tau
    for _ in range(75):
        middle = (left + right) / 2
        if regularized_density_ratio(middle, tau) > ratio:
            right = middle
        else:
            left = middle
    return (left + right) / 2


def boundary_tau(r: float, gal: Galerkin = GAL_HIGH, quad: Quadrature = QUAD_HIGH) -> float:
    g = geometry(r, gal=gal, quad=quad)["g"]
    return g / (1 + r * g)


def boundary_r_at_ratio(ratio: float) -> float:
    left, right = 0.05, 12.0
    for _ in range(65):
        middle = (left + right) / 2
        t = boundary_tau(middle)
        if regularized_density_ratio(middle, t) > ratio:
            right = middle
        else:
            left = middle
    return (left + right) / 2


def make_transport() -> dict[str, dict[str, float]]:
    # Same angular concentration r=2, but model-specific mass density rho.
    states = {name: model_at_r(name, 2.0) for name in ("linear", "hysteresis", "regularized")}
    for name, state in states.items():
        rows = []
        for angle in np.linspace(0, 90, 181):
            plus, minus, imaginary, disc = wave_speeds(state, float(angle))
            rows.append((angle, plus, minus, imaginary, disc))
        save_csv(f"transport_{name}.csv", ("angle_deg", "real_plus", "real_minus", "imag_abs", "discriminant"), rows)
    return states


def make_phase_map() -> dict[str, float]:
    r_end = boundary_r_at_ratio(4.0)
    boundary_rows = []
    previous_x = 0.0
    for r in np.linspace(0.01, r_end, 260):
        tau = boundary_tau(float(r))
        x = regularized_density_ratio(float(r), tau)
        assert x > previous_x
        previous_x = x
        boundary_rows.append((x, tau, r))
    save_csv("noise_boundary.csv", ("rho_over_rhoc", "tau_boundary", "r"), boundary_rows)

    pressure_rows = []
    for ratio in np.linspace(1.2, 4.0, 141):
        thetas = []
        for tau in (0.02, 0.04, 0.10, 0.30):
            r = r_at_density_ratio(float(ratio), tau)
            thetas.append(model_at_r("regularized", r, tau=tau)["Theta"])
        pressure_rows.append((ratio, *thetas))
    save_csv("noise_pressure.csv", ("rho_over_rhoc", "tau002", "tau004", "tau010", "tau030"), pressure_rows)

    # One-dimensional numerical maximum of the exact zero set, not a theorem.
    coarse = [(boundary_tau(float(r)), float(r)) for r in np.linspace(0.02, 18.0, 600)]
    best_tau, best_r = max(coarse)
    left, right = best_r - 0.08, best_r + 0.08
    golden = (math.sqrt(5) - 1) / 2
    x1, x2 = right - golden * (right - left), left + golden * (right - left)
    f1, f2 = boundary_tau(x1), boundary_tau(x2)
    for _ in range(45):
        if f1 < f2:
            left, x1, f1 = x1, x2, f2
            x2 = left + golden * (right - left)
            f2 = boundary_tau(x2)
        else:
            right, x2, f2 = x2, x1, f1
            x1 = right - golden * (right - left)
            f1 = boundary_tau(x1)
    r_peak = (left + right) / 2
    tau_peak = boundary_tau(r_peak)
    return {"r_peak": r_peak, "tau_peak": tau_peak,
            "rho_over_rhoc_at_peak": regularized_density_ratio(r_peak, tau_peak),
            "analytic_sufficient_threshold": 1 / (2 * math.sqrt(5)),
            "boundary_r_at_ratio4": r_end}


def make_slow_rate() -> dict[str, float]:
    rows = []
    for r in np.linspace(0, 8, 201):
        gap = GAL_HIGH.solve(float(r))[0]
        if r == 0:
            rho, q = 3.0, 0.0
        else:
            c = spherical_c(float(r))
            c4 = QUAD_HIGH.moments(4, float(r))[0]
            rho = r / c
            q = r * (c - c4)
        rate = q * gap  # epsilon_time = 1, in the manuscript's collision clock.
        rows.append((r, rho - 3, gap, q, rate, 4 * (rho - 3) / 3))
    save_csv("slow_rate.csv", ("r", "rho_minus_3", "fixed_gap", "q", "guaranteed_rate", "onset_asymptotic"), rows)
    return {"r_zero_fixed_gap": rows[0][2], "r_zero_guaranteed_rate": rows[0][4]}


def make_fold_wedge() -> dict[str, float]:
    """No-fit quarter-power laws on the right stable branch of k(J)=J+J²."""
    r_star, rho_star, R_second = fold(2, QUAD_HIGH)
    g_star = geometry(r_star)
    c_star, tilde_star = g_star["c"], g_star["c_tilde"]
    j_star, jp_star, _ = inverse_feedback(r_star)
    A_star = r_star * jp_star / j_star

    # Let delta=rho-rho_*. Since R(r)-rho_* ~ R''(r-r_*)²/2,
    # D=rR'/R ~ [r_* sqrt(2R'')/rho_*] sqrt(delta).
    # Hence -Theta ~ B_theta delta^{-1/2} and
    # gamma ~ B_gamma delta^{-1/2}. The transverse |Im v| and the
    # non-hyperbolic angular half-width have powers -1/4 and +1/4.
    B_theta = (c_star - tilde_star) * rho_star / (r_star * math.sqrt(2 * R_second))
    B_gamma = c_star * A_star * rho_star / (r_star * math.sqrt(2 * R_second))
    C_imaginary = math.sqrt(c_star * B_theta)
    C_wedge_radians = 2 * C_imaginary / B_gamma
    C_wedge_degrees = math.degrees(C_wedge_radians)

    rows = []
    for step in np.geomspace(0.001, 0.8, 160):
        state = model_at_r("hysteresis", r_star + float(step))
        delta = state["rho"] - rho_star
        assert delta > 0 and state["Theta"] < 0
        imaginary = math.sqrt(-state["c"] * state["Theta"])
        half_width = math.degrees(math.atan(2 * imaginary / (state["gamma"] - state["c_tilde"])))
        # The square-root discriminant must vanish exactly at the
        # corresponding angular boundary (up to floating-point rounding).
        critical = 90 - half_width
        _, _, _, discriminant = wave_speeds(state, critical)
        assert abs(discriminant) / (state["gamma"] - state["c_tilde"]) ** 2 < 5e-14
        rows.append((delta, half_width, C_wedge_degrees * delta**0.25,
                     imaginary, C_imaginary * delta**(-0.25),
                     state["Theta"], state["gamma"]))
    save_csv("fold_angle_wedge.csv",
             ("delta_rho", "half_width_deg", "half_width_asymptotic_deg",
              "transverse_imag", "transverse_imag_asymptotic", "Theta", "gamma"), rows)
    slope_half = float(np.polyfit(np.log([row[0] for row in rows[:20]]),
                                   np.log([row[1] for row in rows[:20]]), 1)[0])
    slope_imag = float(np.polyfit(np.log([row[0] for row in rows[:20]]),
                                   np.log([row[3] for row in rows[:20]]), 1)[0])
    small_half_ratio = rows[0][1] / rows[0][2]
    small_imag_ratio = rows[0][3] / rows[0][4]
    assert abs(slope_half - 0.25) < 0.01 and abs(slope_imag + 0.25) < 0.01
    assert abs(small_half_ratio - 1) < 0.002 and abs(small_imag_ratio - 1) < 0.002
    low_r_star, low_rho_star, low_R_second = fold(2, QUAD_LOW)
    return {
        "r_star": r_star, "rho_star": rho_star, "R_second": R_second,
        "c_star": c_star, "ctilde_star": tilde_star, "A_star": A_star,
        "B_theta": B_theta, "B_gamma": B_gamma,
        "C_wedge_degrees": C_wedge_degrees, "C_imaginary": C_imaginary,
        "sampled_delta_rho_range": [rows[0][0], rows[-1][0]],
        "smallest_delta_half_width_ratio_to_no_fit_asymptotic": small_half_ratio,
        "smallest_delta_imag_ratio_to_no_fit_asymptotic": small_imag_ratio,
        "first_20_log_slope_half_width": slope_half,
        "first_20_log_slope_imag": slope_imag,
        "resolution_change_r_star": abs(r_star - low_r_star),
        "resolution_change_rho_star": abs(rho_star - low_rho_star),
        "resolution_change_R_second": abs(R_second - low_R_second),
    }


TRANSPORT_TEX = r"""\documentclass[tikz,border=2mm]{standalone}
\usepackage{amsmath}
\usepackage{pgfplots}
\usepgfplotslibrary{groupplots}
\pgfplotsset{compat=1.18}
\definecolor{navy}{HTML}{174A68}
\definecolor{teal}{HTML}{178878}
\definecolor{orange}{HTML}{C76336}
\begin{document}
\begin{tikzpicture}
\begin{groupplot}[
 group style={group size=3 by 2,horizontal sep=9mm,vertical sep=9mm},
 width=5.0cm,height=4.0cm,grid=major,grid style={black!9},
 xmin=0,xmax=90,xtick={0,30,60,90},
 tick label style={font=\scriptsize},label style={font=\small},
 title style={font=\small},legend style={font=\scriptsize,draw=none,fill=white,fill opacity=.8,text opacity=1}]
\nextgroupplot[title={linear $k(J)=J$},ylabel={$\operatorname{Re}v_\pm$},ymin=-.1,ymax=1.8]
\addplot[navy,very thick] table[x=angle_deg,y=real_plus,col sep=comma]{../numerics/data/transport_linear.csv};
\addlegendentry{$v_+$}
\addplot[teal,very thick,dashed] table[x=angle_deg,y=real_minus,col sep=comma]{../numerics/data/transport_linear.csv};
\addlegendentry{$v_-$}
\draw[orange,densely dotted] (axis cs:66.92935,-.1) -- (axis cs:66.92935,1.8);
\nextgroupplot[title={fold $k(J)=J+J^2$},ymin=-.2,ymax=20]
\addplot[navy,very thick] table[x=angle_deg,y=real_plus,col sep=comma]{../numerics/data/transport_hysteresis.csv};
\addplot[teal,very thick,dashed] table[x=angle_deg,y=real_minus,col sep=comma]{../numerics/data/transport_hysteresis.csv};
\draw[orange,densely dotted] (axis cs:75.23592,-.2) -- (axis cs:75.23592,20);
\nextgroupplot[title={saturated $\tau_0=0.3$},ymin=-.6,ymax=.9]
\addplot[navy,very thick] table[x=angle_deg,y=real_plus,col sep=comma]{../numerics/data/transport_regularized.csv};
\addplot[teal,very thick,dashed] table[x=angle_deg,y=real_minus,col sep=comma]{../numerics/data/transport_regularized.csv};
\nextgroupplot[xlabel={$\theta$ (deg)},ylabel={$|\operatorname{Im}v_+|$},ymin=0,ymax=.32]
\addplot[orange,very thick] table[x=angle_deg,y=imag_abs,col sep=comma]{../numerics/data/transport_linear.csv};
\draw[orange,densely dotted] (axis cs:66.92935,0) -- (axis cs:66.92935,.32);
\nextgroupplot[xlabel={$\theta$ (deg)},ymin=0,ymax=2.6]
\addplot[orange,very thick] table[x=angle_deg,y=imag_abs,col sep=comma]{../numerics/data/transport_hysteresis.csv};
\draw[orange,densely dotted] (axis cs:75.23592,0) -- (axis cs:75.23592,2.6);
\nextgroupplot[xlabel={$\theta$ (deg)},ymin=0,ymax=.32]
\addplot[orange,very thick] table[x=angle_deg,y=imag_abs,col sep=comma]{../numerics/data/transport_regularized.csv};
\end{groupplot}
\end{tikzpicture}
\end{document}
"""


NOISE_TEX = r"""\documentclass[tikz,border=2mm]{standalone}
\usepackage{pgfplots}
\usepgfplotslibrary{groupplots,fillbetween}
\pgfplotsset{compat=1.18}
\definecolor{navy}{HTML}{174A68}
\definecolor{teal}{HTML}{178878}
\definecolor{orange}{HTML}{C76336}
\definecolor{violet}{HTML}{785AA3}
\begin{document}
\begin{tikzpicture}
\begin{groupplot}[
 group style={group size=2 by 1,horizontal sep=18mm},
 width=7.0cm,height=6.1cm,grid=major,grid style={black!9},
 tick label style={font=\small},label style={font=\small},
 legend style={font=\scriptsize,draw=none,fill=white,fill opacity=.86,text opacity=1}]
\nextgroupplot[xlabel={$\rho/\rho_c$},ylabel={noise $\tau_0$},xmin=1,xmax=4,ymin=0,ymax=.25,legend style={at={(.98,.70)},anchor=north east}]
\addplot[name path=base,draw=none,forget plot] coordinates {(1.00001,0) (4,0)};
\addplot[name path=critical,draw=none,forget plot] table[x=rho_over_rhoc,y=tau_boundary,col sep=comma]{../numerics/data/noise_boundary.csv};
\addplot[orange!28,forget plot] fill between[of=base and critical];
\addplot[orange,very thick] table[x=rho_over_rhoc,y=tau_boundary,col sep=comma]{../numerics/data/noise_boundary.csv};
\addlegendentry{$\Theta=0$ (numerical)}
\addplot[navy,densely dashed,very thick] coordinates {(1,.2236068) (4,.2236068)};
\addlegendentry{proved sufficient line}
\node[font=\scriptsize,orange!90!black,anchor=west] at (axis cs:1.67,.018) {$\Theta<0$};
\nextgroupplot[xlabel={$\rho/\rho_c$},ylabel={$\Theta$},xmin=1.2,xmax=4,ymin=-.12,ymax=1.7,legend pos=north east]
\addplot[black!60,densely dotted,forget plot] coordinates {(1.2,0) (4,0)};
\addplot[orange,very thick] table[x=rho_over_rhoc,y=tau002,col sep=comma]{../numerics/data/noise_pressure.csv};
\addlegendentry{$\tau_0=.02$}
\addplot[violet,very thick,dashed] table[x=rho_over_rhoc,y=tau004,col sep=comma]{../numerics/data/noise_pressure.csv};
\addlegendentry{$\tau_0=.04$}
\addplot[teal,very thick,dashdotted] table[x=rho_over_rhoc,y=tau010,col sep=comma]{../numerics/data/noise_pressure.csv};
\addlegendentry{$\tau_0=.10$}
\addplot[navy,very thick] table[x=rho_over_rhoc,y=tau030,col sep=comma]{../numerics/data/noise_pressure.csv};
\addlegendentry{$\tau_0=.30$}
\end{groupplot}
\end{tikzpicture}
\end{document}
"""


SLOW_TEX = r"""\documentclass[tikz,border=2mm]{standalone}
\usepackage{pgfplots}
\usepgfplotslibrary{groupplots}
\pgfplotsset{compat=1.18}
\definecolor{navy}{HTML}{174A68}
\definecolor{orange}{HTML}{C76336}
\begin{document}
\begin{tikzpicture}
\begin{groupplot}[
 group style={group size=2 by 1,horizontal sep=12mm},
 width=7.3cm,height=5.5cm,grid=major,grid style={black!9},
 tick label style={font=\small},label style={font=\small},
 legend style={font=\small,draw=none,fill=white,fill opacity=.86,text opacity=1}]
\nextgroupplot[xlabel={field $r$},ylabel={inverse time},xmin=0,xmax=8,ymin=0,ymax=9,legend pos=north west]
\addplot[navy,very thick] table[x=r,y=fixed_gap,col sep=comma]{../numerics/data/slow_rate.csv};
\addlegendentry{fixed-field $\lambda_2(r)$}
\addplot[orange,very thick,dashed] table[x=r,y=guaranteed_rate,col sep=comma]{../numerics/data/slow_rate.csv};
\addlegendentry{feedback guarantee $q_2\lambda_2$}
\nextgroupplot[xlabel={$\rho-3$},ylabel={inverse time},xmin=0,xmax=1,ymin=0,ymax=1.8,legend pos=north west]
\addplot[orange,very thick] table[x=rho_minus_3,y=guaranteed_rate,col sep=comma]{../numerics/data/slow_rate.csv};
\addlegendentry{$q_2\lambda_2$}
\addplot[navy,densely dotted,very thick] table[x=rho_minus_3,y=onset_asymptotic,col sep=comma]{../numerics/data/slow_rate.csv};
\addlegendentry{$\frac43(\rho-3)$}
\end{groupplot}
\end{tikzpicture}
\end{document}
"""


FOLD_WEDGE_TEX = r"""\documentclass[tikz,border=2mm]{standalone}
\usepackage{amsmath}
\usepackage{pgfplots}
\usepgfplotslibrary{groupplots}
\pgfplotsset{compat=1.18}
\definecolor{navy}{HTML}{174A68}
\definecolor{orange}{HTML}{C76336}
\begin{document}
\begin{tikzpicture}
\begin{groupplot}[
 group style={group size=2 by 1,horizontal sep=17mm},
 width=7.1cm,height=5.7cm,xmode=log,ymode=log,
 grid=major,grid style={black!9},
 tick label style={font=\small},label style={font=\small},
 legend style={font=\small,draw=none,fill=white,fill opacity=.88,text opacity=1}]
\nextgroupplot[xlabel={$\rho-\rho_*$},ylabel={non-hyperbolic half-angle (deg)},
 xmin=8e-8,xmax=.06,ymin=1,ymax=55,legend pos=south east]
\addplot[navy,very thick] table[x=delta_rho,y=half_width_deg,col sep=comma]{../numerics/data/fold_angle_wedge.csv};
\addlegendentry{computed $90^\circ-\theta_c$}
\addplot[orange,very thick,dashed] table[x=delta_rho,y=half_width_asymptotic_deg,col sep=comma]{../numerics/data/fold_angle_wedge.csv};
\addlegendentry{$C_\phi(\rho-\rho_*)^{1/4}$}
\nextgroupplot[xlabel={$\rho-\rho_*$},ylabel={transverse $|\operatorname{Im}v|$},
 xmin=8e-8,xmax=.06,ymin=.7,ymax=31,legend pos=north east]
\addplot[navy,very thick] table[x=delta_rho,y=transverse_imag,col sep=comma]{../numerics/data/fold_angle_wedge.csv};
\addlegendentry{computed $\sqrt{-c\Theta}$}
\addplot[orange,very thick,dashed] table[x=delta_rho,y=transverse_imag_asymptotic,col sep=comma]{../numerics/data/fold_angle_wedge.csv};
\addlegendentry{$C_I(\rho-\rho_*)^{-1/4}$}
\end{groupplot}
\end{tikzpicture}
\end{document}
"""


def compile_tex(name: str, content: str) -> None:
    (FIGURES / f"{name}.tex").write_text(content)
    result = subprocess.run(
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", f"{name}.tex"],
        cwd=FIGURES, capture_output=True, text=True,
    )
    if result.returncode:
        raise RuntimeError(f"pdflatex failed for {name}:\n{result.stdout[-6000:]}\n{result.stderr[-2000:]}")


def validate(states: dict[str, dict[str, float]], phase: dict[str, float], slow: dict[str, float]) -> dict:
    c_checks = []
    resolution_checks = []
    for r in (0.05, 0.5, 2.0, 5.0, 8.0):
        c_quad, cp_quad, _ = QUAD_HIGH.moments(2, r)
        c_checks.append({"r": r, "S2_mean_abs_error": abs(c_quad - spherical_c(r)),
                         "S2_variance_abs_error": abs(cp_quad - spherical_cp(r))})
        hi = geometry(r)
        lo = geometry(r, gal=GAL_LOW, quad=QUAD_LOW)
        resolution_checks.append({"r": r,
                                  "fixed_gap_difference_K24N240_vs_K16N160": abs(hi["gap"] - lo["gap"]),
                                  "gci_speed_difference_K24N240_vs_K16N160": abs(hi["c_tilde"] - lo["c_tilde"]),
                                  "boundary_tau_difference": abs(boundary_tau(r) - boundary_tau(r, GAL_LOW, QUAD_LOW))})
    assert max(c["S2_mean_abs_error"] for c in c_checks) < 1e-12
    assert max(c["S2_variance_abs_error"] for c in c_checks) < 1e-12
    assert max(c["gci_speed_difference_K24N240_vs_K16N160"] for c in resolution_checks) < 1e-10

    matrix_checks = []
    for name, state in states.items():
        rho, c, gamma, tilde, theta = (state[k] for k in ("rho", "c", "gamma", "c_tilde", "Theta"))
        for angle in (0, 45, 70, 90):
            co, si = math.cos(math.radians(angle)), math.sin(math.radians(angle))
            matrix = np.array([[gamma * co, rho * c * si], [theta * si / rho, tilde * co]])
            eigenvalues = np.linalg.eigvals(matrix)
            plus, minus, imag, _ = wave_speeds(state, angle)
            computed = sorted((complex(plus, imag), complex(minus, -imag)), key=lambda z: (z.real, z.imag))
            direct = sorted((complex(x) for x in eigenvalues), key=lambda z: (z.real, z.imag))
            error = max(abs(a - b) for a, b in zip(computed, direct))
            matrix_checks.append({"model": name, "angle_deg": angle, "eigenvalue_error": error})
    # For non-real conjugate eigenvalues ordering by floating real parts is
    # unstable, so compare symmetric polynomials instead.
    for item in matrix_checks:
        if item["eigenvalue_error"] > 1e-8:
            name, angle = item["model"], item["angle_deg"]
            state = states[name]
            plus, minus, imag, _ = wave_speeds(state, angle)
            actual = np.linalg.eigvals(np.array([
                [state["gamma"] * math.cos(math.radians(angle)), state["rho"] * state["c"] * math.sin(math.radians(angle))],
                [state["Theta"] * math.sin(math.radians(angle)) / state["rho"], state["c_tilde"] * math.cos(math.radians(angle))]]))
            expected = np.array([complex(plus, imag), complex(minus, -imag)])
            item["eigenvalue_error"] = max(abs(np.sum(expected) - np.sum(actual)),
                                             abs(np.prod(expected) - np.prod(actual)))
    assert max(item["eigenvalue_error"] for item in matrix_checks) < 1e-9

    # Small-field independent analytic checks: q~(2/15)r^2 and
    # rho-3~r^2/5, so q*lambda/(rho-3) -> 4/3 as lambda -> 2.
    tiny = model_at_r("linear", 0.02)
    q_tiny = 0.02 * (tiny["c"] - tiny["c_plus"])
    slow["asymptotic_ratio_r002"] = q_tiny * tiny["gap"] / (tiny["rho"] - 3)
    assert abs(slow["asymptotic_ratio_r002"] - 4 / 3) < 1e-3
    assert states["linear"]["Theta"] < 0 and states["hysteresis"]["Theta"] < 0
    assert states["regularized"]["Theta"] > 0
    assert phase["tau_peak"] < phase["analytic_sufficient_threshold"]
    return {"S2_analytic_checks": c_checks, "resolution_checks": resolution_checks,
            "principal_symbol_direct_matrix_checks": matrix_checks, "slow_rate": slow}


def main() -> None:
    global OUTPUT_ROOT, DATA, FIGURES
    args = parse_output_args(__doc__, allow_skip_tex=True)
    OUTPUT_ROOT, REPORTS, DATA, FIGURES = output_tree(args.output_dir)
    states = make_transport()
    phase = make_phase_map()
    slow = make_slow_rate()
    fold_wedge = make_fold_wedge()
    validation = validate(states, phase, slow)
    report = {
        "geometry": "n=3 (d=2), unit first-order SOH time and space scales",
        "transport_states_at_same_r2": {
            name: {key: state[key] for key in ("rho", "Theta", "gamma", "c", "c_tilde")}
            | {"critical_angle_deg": critical_angle(state),
               "transverse_abs_imaginary_speed": math.sqrt(max(0, -state["c"] * state["Theta"]))}
            for name, state in states.items()},
        "regularized_model": "nu(J)=J/(epsilon+J), noise=tau0; epsilon=1 in physical-density curves",
        "phase_boundary": phase,
        "fold_angle_wedge": fold_wedge,
        "validation": validation,
        "scope": "K2=0 first-order symbol; for K2>0 only its first-order part; no kinetic ill-posedness assertion",
    }
    (REPORTS / "transport_atlas_validation.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    if not args.skip_tex:
        compile_tex("transport_atlas", TRANSPORT_TEX)
        compile_tex("noise_phase_map", NOISE_TEX)
        compile_tex("slow_rate", SLOW_TEX)
        compile_tex("fold_angle_wedge", FOLD_WEDGE_TEX)
    print(json.dumps({"transport": report["transport_states_at_same_r2"], "phase": phase,
                      "slow_onset_ratio": slow["asymptotic_ratio_r002"],
                      "fold_wedge": fold_wedge}, indent=2))


if __name__ == "__main__":
    main()
