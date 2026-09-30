#!/usr/bin/env python3
"""Vector S² picture of the von Mises--Fisher orientation law and a tilt.

Run from any directory: python3 numerics/orientation_sphere.py
Requires only NumPy and Matplotlib.  The manuscript uses normalized surface
measure dσ₂=dΩ_solid/(4π) and its density M_r.  Colors here use the density
per solid angle p_r=M_r/(4π); p_0=1/(4π).  The fixed-radius sphere is the
*space of directions*, not a density-dependent radial surface.  Panel (c)
shows ∂α p_{r=3} for a rotation of the preferred direction, and is not
claimed to be an exact eigenfunction of the frozen kinetic operator.
"""

from __future__ import annotations

import json
from pathlib import Path

from output_paths import parse_output_args, output_tree

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap, Normalize, TwoSlopeNorm
from matplotlib.patches import Rectangle
import numpy as np


ROOT = Path(__file__).resolve().parents[1]
OUTPUT_ROOT = ROOT / "results"
OUT = OUTPUT_ROOT / "figures" / "orientation_sphere.pdf"
CHECK = OUTPUT_ROOT / "numerics" / "orientation_sphere_check.json"

NAVY = "#184a68"
TEAL = "#158477"
ORANGE = "#d46b38"
BLUE = "#31588a"
RED = "#bc4d34"


def c2(r: float) -> float:
    """The n=3 mean polar cosine (coth(r)-1/r)."""
    if abs(r) < 0.02:
        return r / 3 - r**3 / 45 + 2 * r**5 / 945 - r**7 / 4725
    return 1 / np.tanh(r) - 1 / r


def density(r: float, mu: np.ndarray) -> np.ndarray:
    """p_r per solid angle dΩ=dφ dμ; manuscript M_r=4π p_r per dσ₂."""
    if r == 0:
        return np.ones_like(mu) / (4 * np.pi)
    return r * np.exp(r * mu) / (4 * np.pi * np.sinh(r))


def verify() -> dict[str, float]:
    """Integrate p_r against solid angle dΩ; equivalently M_r against dσ₂."""
    mu, w = np.polynomial.legendre.leggauss(96)
    phi = 2 * np.pi * np.arange(192) / 192
    mm = mu[:, None]
    xx = np.sqrt(1 - mm**2) * np.cos(phi)[None, :]
    yy = np.sqrt(1 - mm**2) * np.sin(phi)[None, :]
    dphi = 2 * np.pi / len(phi)
    data: dict[str, float] = {}
    for r in (0.0, 3.0):
        p = density(r, mm)
        mass = float(np.sum(w[:, None] * p) * dphi * len(phi))
        mean_z = float(np.sum(w[:, None] * p * mm) * dphi * len(phi))
        key = f"r{int(r)}"
        data[f"{key}_mass_error"] = abs(mass - 1)
        data[f"{key}_mean_z_error"] = abs(mean_z - c2(r))
        assert data[f"{key}_mass_error"] < 2e-13
        assert data[f"{key}_mean_z_error"] < 2e-13
        if r == 3:
            # d/dalpha p_3(omega;Omega_alpha)|_{alpha=0}
            # = 3 p_3(omega;ez) omega_x.  The integral is zero;
            # the derivative of the mean direction is c_2(3) e_x.
            dp = r * p * xx
            signed_mass = float(np.sum(w[:, None] * dp) * dphi)
            mean_response_x = float(np.sum(w[:, None] * dp * xx) * dphi)
            mean_response_y = float(np.sum(w[:, None] * dp * yy) * dphi)
            data["tilt_signed_mass_error"] = abs(signed_mass)
            data["tilt_mean_x_error"] = abs(mean_response_x - c2(r))
            data["tilt_mean_y_error"] = abs(mean_response_y)
            assert data["tilt_signed_mass_error"] < 2e-13
            assert data["tilt_mean_x_error"] < 2e-13
            assert data["tilt_mean_y_error"] < 2e-13
    data["c2_r3"] = c2(3.0)
    return data


def lighten_colors(rgba: np.ndarray, normal: np.ndarray) -> np.ndarray:
    """Subtle 3D lighting without rasterization or fictitious density radius."""
    light = np.array([-0.15, -0.55, 0.82])
    light /= np.linalg.norm(light)
    intensity = np.maximum(np.einsum("ijk,k->ij", normal, light), 0)
    out = rgba.copy()
    out[..., :3] *= (0.73 + 0.27 * intensity)[..., None]
    return out


def sphere_panel(ax, scalar: np.ndarray, cmap, norm, *, title: str,
                 show_axis: bool = False, show_tilt: bool = False) -> None:
    theta = np.linspace(0, np.pi, 53)
    phi = np.linspace(0, 2 * np.pi, 105)
    th, ph = np.meshgrid(theta, phi, indexing="ij")
    x = np.sin(th) * np.cos(ph)
    y = np.sin(th) * np.sin(ph)
    z = np.cos(th)
    color = lighten_colors(cmap(norm(scalar(x, y, z))), np.stack([x, y, z], axis=-1))
    ax.plot_surface(x, y, z, facecolors=color, rstride=1, cstride=1,
                    linewidth=0, antialiased=False, shade=False)

    # Sparse visible latitude / longitude arcs make the object read as a
    # three-dimensional sphere.  Back-side arcs are explicitly omitted.
    eye = np.array([np.cos(np.deg2rad(22)) * np.cos(np.deg2rad(-61)),
                    np.cos(np.deg2rad(22)) * np.sin(np.deg2rad(-61)),
                    np.sin(np.deg2rad(22))])

    def visible_arc(cx, cy, cz):
        front = (cx * eye[0] + cy * eye[1] + cz * eye[2]) > 0.035
        ax.plot(1.008 * np.where(front, cx, np.nan),
                1.008 * np.where(front, cy, np.nan),
                1.008 * np.where(front, cz, np.nan),
                color="#243647", alpha=0.24, linewidth=0.72, zorder=100)

    arc_phi = np.linspace(0, 2 * np.pi, 360)
    for latitude in (-45, 0, 45):
        zz = np.sin(np.deg2rad(latitude)) * np.ones_like(arc_phi)
        rr = np.cos(np.deg2rad(latitude))
        visible_arc(rr * np.cos(arc_phi), rr * np.sin(arc_phi), zz)
    arc_theta = np.linspace(0, np.pi, 240)
    for longitude in (-106, -61, -16, 29, 74):
        angle = np.deg2rad(longitude)
        visible_arc(np.sin(arc_theta) * np.cos(angle),
                    np.sin(arc_theta) * np.sin(angle),
                    np.cos(arc_theta))

    # Small, external direction arrows remain legible when the figure is scaled.
    if show_axis:
        ax.quiver(0, 0, 1.02, 0, 0, 0.38, color=NAVY,
                  linewidth=1.65, arrow_length_ratio=0.24)
        ax.text(0.035, 0.035, 1.45, r"$\Omega$", fontsize=10,
                color=NAVY, ha="left", va="bottom")
    if show_tilt:
        alpha = np.deg2rad(18)
        ax.quiver(0, 0, 1.03, 0, 0, 0.32, color=BLUE,
                  linewidth=1.45, arrow_length_ratio=0.22)
        ax.quiver(1.02 * np.sin(alpha), 0, 1.02 * np.cos(alpha),
                  0.35 * np.sin(alpha), 0, 0.35 * np.cos(alpha),
                  color=ORANGE, linewidth=1.8, arrow_length_ratio=0.24)
        ax.text(0, 0.06, 1.43, r"$\Omega$", fontsize=10, color=BLUE,
                ha="right", va="bottom")
        ax.text(0.39, 0.02, 1.34, r"$\Omega_{\alpha}$", fontsize=10,
                color=ORANGE, ha="left", va="bottom")

    ax.set(xlim=(-1.24, 1.24), ylim=(-1.24, 1.24), zlim=(-1.14, 1.55))
    ax.set_box_aspect((1, 1, 1.03), zoom=1.15)
    ax.set_axis_off()
    ax.view_init(elev=22, azim=-61)
    ax.set_proj_type("ortho")
    ax.set_title(title, fontsize=10, color=NAVY, pad=0)


def make_figure() -> None:
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 9,
        "pdf.fonttype": 42,
        "savefig.facecolor": "white",
    })
    fig = plt.figure(figsize=(6.7, 2.86))
    axes = [fig.add_subplot(1, 3, i + 1, projection="3d") for i in range(3)]
    plt.subplots_adjust(left=0.015, right=0.985, bottom=0.11, top=0.93, wspace=-0.06)

    # The color on a *unit* sphere carries probability; all three radii are one.
    concentration_map = LinearSegmentedColormap.from_list(
        "orientation_density", [NAVY, TEAL, "#f0d49c", ORANGE], N=256)
    conc_norm = Normalize(vmin=-4.7, vmax=1.85)
    relative_log = lambda r: lambda x, y, z: (
        np.zeros_like(z) if r == 0 else r * z - np.log(np.sinh(r) / r))
    sphere_panel(axes[0], relative_log(0), concentration_map, conc_norm,
                 title=r"(a) Isotropic: $r=0$")
    sphere_panel(axes[1], relative_log(3), concentration_map, conc_norm,
                 title=r"(b) Polar order: $r=3$", show_axis=True)

    # Exact infinitesimal response of p_r to Omega_alpha=(sin alpha,0,cos alpha).
    # The display scale is a common signed density unit (sr^-1 rad^-1).
    def tilt_response(x, y, z):
        return 3 * density(3, z) * x

    signed = np.linspace(-1, 1, 601)
    response_max = float(np.max(np.abs(tilt_response(
        np.sqrt(np.maximum(0, 1 - signed**2)), np.zeros_like(signed), signed))))
    response_map = LinearSegmentedColormap.from_list(
        "tilt_response", [BLUE, "#e9edf0", RED], N=256)
    response_norm = TwoSlopeNorm(vmin=-response_max, vcenter=0, vmax=response_max)
    sphere_panel(axes[2], tilt_response, response_map, response_norm,
                 title=r"(c) Rotate $\Omega$: gain / loss", show_tilt=True)

    # Use explicit vector rectangles for the keys: the output PDF has no
    # raster image even in its color bars.
    def vector_color_key(ax, cmap, norm, ticks, ticklabels, label):
        edges = np.linspace(norm.vmin, norm.vmax, 81)
        for left, right in zip(edges[:-1], edges[1:]):
            middle = (left + right) / 2
            ax.add_patch(Rectangle((left, 0), right - left, 1,
                                   facecolor=cmap(norm(middle)), edgecolor="none"))
        ax.set(xlim=(norm.vmin, norm.vmax), ylim=(0, 1), yticks=[])
        ax.set_xticks(ticks, ticklabels)
        ax.tick_params(axis="x", labelsize=8, length=1.5, pad=1)
        ax.set_xlabel(label, fontsize=8, labelpad=1)
        for spine in ax.spines.values():
            spine.set_visible(False)

    # Two short horizontal keys fit beneath the panels at print scale.
    cax1 = fig.add_axes([0.145, 0.105, 0.30, 0.024])
    vector_color_key(cax1, concentration_map, conc_norm,
                     np.log([0.02, 0.1, 1, 6]), ["0.02", "0.1", "1", "6"],
                     r"density / isotropic density")

    cax2 = fig.add_axes([0.738, 0.105, 0.195, 0.024])
    vector_color_key(cax2, response_map, response_norm,
                     [-response_max, 0, response_max],
                     [f"{-response_max:.1f}", "0.0", f"{response_max:.1f}"],
                     r"$\partial_\alpha p_{r=3}$ (sr$^{-1}$ rad$^{-1}$)")

    OUT.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(OUT, format="pdf", metadata={"Creator": "orientation_sphere.py"})
    plt.close(fig)


def main() -> None:
    global OUTPUT_ROOT, OUT, CHECK
    args = parse_output_args(__doc__)
    OUTPUT_ROOT, REPORTS, _, FIGURES = output_tree(args.output_dir)
    OUT = FIGURES / "orientation_sphere.pdf"
    CHECK = REPORTS / "orientation_sphere_check.json"
    check = verify()
    make_figure()
    payload = {
        "measure_convention": "dOmega_solid = dphi dmu = 4*pi*d_sigma_2",
        "density_convention": "p_r = M_r/(4*pi), where integral M_r d_sigma_2 = integral p_r dOmega_solid = 1",
        "quadrature_checks": check,
    }
    CHECK.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"figure": str(OUT.relative_to(OUTPUT_ROOT)), "check": payload}, indent=2))


if __name__ == "__main__":
    main()
