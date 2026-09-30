#!/usr/bin/env python3
"""Three-dimensional view of the exact fixed-polarization DFL free-energy envelope.

Run from anywhere with ``python3 numerics/energy_landscape_3d.py``.  This
plots a *two-dimensional section of the three-dimensional polarization-vector
space*, rather than solving or closing the kinetic dynamics.
"""

from __future__ import annotations

import json
from pathlib import Path

from output_paths import parse_output_args, output_tree

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import colors
from matplotlib.lines import Line2D
from matplotlib.patches import Rectangle
import numpy as np

from phase_dynamics import R, R_prime, bisect, c3, delta_energy, ordered_roots


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUTPUT_ROOT = ROOT / "results"
OUT = OUTPUT_ROOT / "figures" / "energy_landscape_3d.pdf"
CHECK = OUTPUT_ROOT / "numerics" / "energy_landscape_3d_check.json"
PHASE_CHECK = OUTPUT_ROOT / "numerics" / "phase_dynamics_check.json"

RADIUS_MAX = 0.78
DENSITIES = (1.8, 1.9, 2.0)
Z_LIM = (-0.125, 0.285)


def inverse_c3(m: np.ndarray) -> np.ndarray:
    """Monotone scalar inversion by a dense pretabulation on 0 <= m <= .78."""
    r_table = np.linspace(0.0, 5.5, 100_001)
    m_table = c3(r_table)
    assert float(m_table[-1]) > RADIUS_MAX
    return np.interp(m, m_table, r_table)


def landscape(rho: float, m: np.ndarray) -> np.ndarray:
    r = inverse_c3(m)
    return np.asarray(delta_energy(rho, r), dtype=float)


def stationary_data(rho: float, r_star: float) -> dict:
    if rho <= R(r_star):
        return {"rho": rho, "uniform_energy": 0.0, "barrier": None,
                "ordered": None, "global_minimum": "uniform"}
    lower, upper = ordered_roots(rho, r_star)
    saddle_energy = float(delta_energy(rho, lower))
    order_energy = float(delta_energy(rho, upper))
    return {
        "rho": rho,
        "uniform_energy": 0.0,
        "barrier": {"r": lower, "m": float(c3(lower)), "energy": saddle_energy},
        "ordered": {"r": upper, "m": float(c3(upper)), "energy": order_energy},
        "global_minimum": "uniform" if order_energy > 0 else "ordered",
    }


def add_stationary_ring(ax, point: dict, color: str, linestyle: str,
                        linewidth: float = 2.1) -> None:
    theta = np.linspace(0, 2 * np.pi, 361)
    radius = point["m"]
    z = point["energy"]
    ax.plot(radius * np.cos(theta), radius * np.sin(theta),
            z * np.ones_like(theta), color=color, ls=linestyle,
            lw=linewidth, alpha=1.0, zorder=10)


def main() -> None:
    global OUTPUT_ROOT, OUT, CHECK, PHASE_CHECK
    args = parse_output_args(__doc__)
    OUTPUT_ROOT, REPORTS, _, FIGURES = output_tree(args.output_dir)
    OUT = FIGURES / "energy_landscape_3d.pdf"
    CHECK = REPORTS / "energy_landscape_3d_check.json"
    PHASE_CHECK = REPORTS / "phase_dynamics_check.json"
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 9.2,
        "mathtext.fontset": "dejavusans",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "axes.linewidth": 0.7,
        "savefig.facecolor": "white",
    })
    r_star = bisect(R_prime, 0.4, 5.0)
    state = [stationary_data(rho, r_star) for rho in DENSITIES]

    # Polar parameterization gives a smooth circular section, free of masked
    # grid corners.  E(rho, |m|) is evaluated from the original free energy.
    radial = np.linspace(0.0, RADIUS_MAX, 140)
    theta = np.linspace(0.0, 2 * np.pi, 221)
    mm, tt = np.meshgrid(radial, theta, indexing="ij")
    xx = mm * np.cos(tt)
    yy = mm * np.sin(tt)
    norm = colors.TwoSlopeNorm(vmin=-0.11, vcenter=0.0, vmax=0.28)
    cmap = plt.colormaps["RdBu_r"]

    # A two-by-two composition remains legible at the JPhysA text width.  The
    # last cell explains the topology instead of packing tiny 3-D axes in a row.
    fig = plt.figure(figsize=(7.0, 5.7), constrained_layout=False)
    fig.text(0.5, 0.995,
             "Polarization-vector section $m_z=0$ (not physical space)",
             ha="center", va="top", fontsize=8.5)
    positions = [(0.02, 0.53, 0.46, 0.43),
                 (0.51, 0.53, 0.46, 0.43),
                 (0.02, 0.065, 0.46, 0.43)]
    descriptions_en = ("One well: uniform state", "Two wells: metastable order",
                       "Two wells: favored order")
    for index, rho in enumerate(DENSITIES):
        ax = fig.add_axes(positions[index], projection="3d", proj_type="ortho")
        zz = landscape(rho, mm)
        ax.plot_surface(xx, yy, zz, facecolors=cmap(norm(zz)),
                        rstride=2, cstride=3, linewidth=0, antialiased=True,
                        shade=False, alpha=0.99)

        # Zero-energy contour and circular outline clarify the sheet of
        # polarization directions.  The ordered and saddle rings are actual
        # stationary radii of E_rho, not fitted visual guides.
        tline = np.linspace(0, 2 * np.pi, 361)
        ax.plot(RADIUS_MAX * np.cos(tline), RADIUS_MAX * np.sin(tline),
                landscape(rho, np.array([RADIUS_MAX]))[0] * np.ones_like(tline),
                color="#334155", linewidth=0.45, alpha=0.35)
        ax.plot([0], [0], [0.0], linestyle="None", marker="o",
                markersize=6, markerfacecolor="#202936",
                markeredgecolor="white", markeredgewidth=0.8,
                zorder=20)
        if state[index]["barrier"] is not None:
            add_stationary_ring(ax, state[index]["barrier"],
                                "#E39615", (0, (3, 2)), 2.0)
            add_stationary_ring(ax, state[index]["ordered"],
                                "#087E91", "solid", 2.2)

        ax.view_init(elev=29, azim=-55)
        ax.set_xlim(-RADIUS_MAX, RADIUS_MAX)
        ax.set_ylim(-RADIUS_MAX, RADIUS_MAX)
        ax.set_zlim(*Z_LIM)
        ax.set_box_aspect((1, 1, 0.67), zoom=1.18)
        ax.set_axis_off()
        ax.text2D(0.04, 0.96, rf"$\rho={rho:.1f}$", transform=ax.transAxes,
                  fontsize=11, fontweight="semibold")
        ax.text2D(0.03, 0.46, r"$E_\rho\uparrow$", transform=ax.transAxes,
                  fontsize=9)
        arrow = {"arrowstyle": "-|>", "color": "#94A3B8",
                 "lw": 0.8, "mutation_scale": 7}
        ax.annotate("", xy=(0.25, 0.10), xytext=(0.49, 0.18),
                    xycoords="axes fraction", arrowprops=arrow)
        ax.annotate("", xy=(0.73, 0.10), xytext=(0.49, 0.18),
                    xycoords="axes fraction", arrowprops=arrow)
        ax.text2D(0.15, 0.055, r"$m_x$", transform=ax.transAxes,
                  fontsize=9)
        ax.text2D(0.76, 0.055, r"$m_y$", transform=ax.transAxes,
                  fontsize=9)
        fig.text(positions[index][0] + positions[index][2] / 2,
                 positions[index][1] + 0.013,
                 descriptions_en[index],
                 ha="center", va="top", fontsize=9)

    legend = [
        Line2D([], [], marker="o", ls="", color="#202936", markersize=6,
               label="central well: uniform state"),
        Line2D([], [], ls=(0, (3, 2)), color="#E39615", lw=2,
               label="barrier ring"),
        Line2D([], [], ls="-", color="#087E91", lw=2,
               label="ordered ring well"),
    ]
    key = fig.add_axes((0.55, 0.075, 0.41, 0.405))
    key.set_xlim(0, 1)
    key.set_ylim(0, 1)
    key.axis("off")
    key.text(0.0, 0.98, "Physical reading",
             va="top", transform=key.transAxes,
             fontsize=10.5, fontweight="bold")
    key.legend(handles=legend, loc="upper left", bbox_to_anchor=(-0.015, 0.89),
               frameon=False, handlelength=2.1,
               labelspacing=0.75, borderpad=0.0)
    key.plot([0, 1], [0.46, 0.46], color="#CBD5E1", lw=0.7,
             transform=key.transAxes)
    key.text(0.0, 0.40,
             "The ring is directional degeneracy at fixed order;",
             va="top", transform=key.transAxes,
             fontsize=8.3)
    key.text(0.0, 0.32,
             "in the full polarization space it is a sphere.",
             va="top", transform=key.transAxes,
             fontsize=8.3)
    key.text(0.0, 0.23,
             "Height/color: exact free-energy envelope",
             va="top", transform=key.transAxes,
             fontsize=8.3)
    key.text(0.0, 0.15,
             "This is not a vMF closure of the original PDE.",
             va="top", transform=key.transAxes,
             fontsize=8.3)

    cax = fig.add_axes((0.57, 0.075, 0.34, 0.015))
    # Small adjacent rectangles preserve a fully vector PDF, including the
    # otherwise often-rasterized continuous color scale.
    color_edges = np.linspace(-0.11, 0.28, 161)
    for left, right in zip(color_edges[:-1], color_edges[1:]):
        cax.add_patch(Rectangle((left, 0), right - left + 1e-7, 1,
                                facecolor=cmap(norm((left + right) / 2)),
                                edgecolor="none"))
    cax.set_xlim(-0.11, 0.28)
    cax.set_ylim(0, 1)
    cax.set_yticks([])
    cax.set_xticks([-0.1, 0, 0.1, 0.2])
    cax.tick_params(axis="x", labelsize=8, length=2, pad=1)
    for spine in cax.spines.values():
        spine.set_linewidth(0.5)

    OUT.parent.mkdir(exist_ok=True)
    fig.savefig(OUT, dpi=300)
    plt.close(fig)

    # Recompute all stationary values and verify against the independent
    # phase-dynamics report already used by the manuscript.
    validation = {
        "formula": "E_rho(m)=-rho log(sinh(r)/r)+rho*r*m-(rho*m)^2/2-(rho*m)^3/3, m=coth(r)-1/r",
        "cross_section": "m=(m_x,m_y,0), |m|<=0.78",
        "rho_fold": float(R(r_star)),
        "r_fold": float(r_star),
        "panels": state,
        "inverse_max_residual": float(np.max(np.abs(c3(inverse_c3(mm)) - mm))),
        "output_pdf": str(OUT.relative_to(OUTPUT_ROOT)),
    }
    if PHASE_CHECK.exists():
        previous = json.loads(PHASE_CHECK.read_text())["landscape"]
        validation["existing_phase_check_difference"] = {
            "rho_star": abs(validation["rho_fold"] - previous["rho_star"]),
            "rho_1p9_barrier_m": abs(state[1]["barrier"]["m"] - previous["rho_1p9_lower_m"]),
            "rho_1p9_ordered_m": abs(state[1]["ordered"]["m"] - previous["rho_1p9_upper_m"]),
            "rho_1p9_barrier_energy": abs(state[1]["barrier"]["energy"] - previous["rho_1p9_saddle_height"]),
            "rho_1p9_ordered_energy": abs(state[1]["ordered"]["energy"] - previous["rho_1p9_ordered_depth"]),
        }
        assert max(validation["existing_phase_check_difference"].values()) < 1e-10
    assert validation["inverse_max_residual"] < 1e-7
    CHECK.write_text(json.dumps(validation, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(validation, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
