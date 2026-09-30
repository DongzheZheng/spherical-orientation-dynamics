import DFLSphere433.RoundSphereCoordinates
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction
import DifferentialGeometry.Geometry.Operator.Laplacian.Pullback
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! The original round-sphere Schrödinger equation is preserved by genuine
ambient orthogonal symmetries of its potential. This uses the actual induced
metric and the actual scalar Laplacian, not an assumed symmetry of a spectrum. -/

noncomputable section
open Bundle Manifold Metric Module
open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator

namespace DFLGroundSymmetry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

def orthogonalPullback (e : E ≃ₗᵢ[ℝ] E)
    (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) :
    C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯ :=
  ⟨fun x => f (sphereDiffeo (n := n) e x),
    f.contMDiff.comp (sphereDiffeo (n := n) e).contMDiff⟩

/-- Naturality for the actual round-sphere scalar Laplacian. -/
theorem orthogonalPullback_laplacian (e : E ≃ₗᵢ[ℝ] E)
    (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) (x : sphere (0 : E) 1) :
    ΔG (roundMetric (E := E) (n := n)) (orthogonalPullback e f) x =
      ΔG (roundMetric (E := E) (n := n)) f (sphereDiffeo (n := n) e x) := by
  let g := roundMetric (E := E) (n := n)
  let Φ := sphereDiffeo (n := n) e
  have hp : Diffeomorph.pullbackMetricCross g Φ = g := by
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact pullbackMetric_round_eq e
  have hnat := laplacian_pullbackCross g Φ
    (f := (f : sphere (0 : E) 1 → ℝ))
    (f.contMDiff.contMDiffAt.of_le (by decide)) (x := x)
  rw [hp] at hnat
  have hleft := laplacian_levi_eq g (orthogonalPullback e f).contMDiff x
  have hright := laplacian_levi_eq g f.contMDiff (Φ x)
  exact hleft.symm.trans (hnat.trans hright)

/-- A symmetry preserving the actual potential preserves the original
pointwise Schrödinger eigen-equation. -/
theorem orthogonalPullback_schrodinger (e : E ≃ₗᵢ[ℝ] E)
    (V : sphere (0 : E) 1 → ℝ)
    (hV : ∀ x, V (sphereDiffeo (n := n) e x) = V x)
    (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) (lam : ℝ)
    (heig : ∀ x, -ΔG (roundMetric (E := E) (n := n)) f x + V x*f x = lam*f x)
    (x : sphere (0 : E) 1) :
    -ΔG (roundMetric (E := E) (n := n)) (orthogonalPullback e f) x +
      V x*orthogonalPullback e f x = lam*orthogonalPullback e f x := by
  rw [orthogonalPullback_laplacian]
  change -ΔG (roundMetric (E := E) (n := n)) f (sphereDiffeo (n := n) e x) +
    V x*f (sphereDiffeo (n := n) e x) = lam*f (sphereDiffeo (n := n) e x)
  rw [← hV x]
  exact heig (sphereDiffeo (n := n) e x)

/-- An orthogonal map fixing the field axis preserves every genuine
latitude potential, including the manuscript's half-density tilt. -/
theorem axis_potential_invariant (axis : E) (F : ℝ → ℝ)
    (e : E ≃ₗᵢ[ℝ] E) (he : e axis = axis) (x : sphere (0 : E) 1) :
    F ⟪axis, (sphereDiffeo (n := n) e x : E)⟫_ℝ = F ⟪axis, (x : E)⟫_ℝ := by
  rw [sphereDiffeo_coe]
  have hi := e.inner_map_map axis (x : E)
  rw [he] at hi
  rw [hi]

/-- Every two physical sphere points at the same latitude are related by
an actual ambient orthogonal symmetry fixing the field axis. -/
theorem same_latitude_orthogonal_symmetry (axis : E)
    (x y : sphere (0 : E) 1) (hxy : ⟪axis, (x : E)⟫_ℝ = ⟪axis, (y : E)⟫_ℝ) :
    ∃ e : E ≃ₗᵢ[ℝ] E, e axis = axis ∧ sphereDiffeo (n := n) e x = y := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let K : Submodule ℝ E := (ℝ ∙ ((x : E) - (y : E)))ᗮ
  let e : E ≃ₗᵢ[ℝ] E := K.reflection
  have ha : axis ∈ K := by
    change axis ∈ (ℝ ∙ ((x : E) - (y : E)))ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [inner_sub_right, hxy, sub_self]
  refine ⟨e, K.reflection_mem_subspace_eq_self ha, ?_⟩
  apply Subtype.ext
  change e (x : E) = (y : E)
  exact Submodule.reflection_sub
    ((norm_eq_of_mem_sphere x).trans (norm_eq_of_mem_sphere y).symm)

end DFLGroundSymmetry
