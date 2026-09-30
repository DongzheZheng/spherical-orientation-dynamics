import continuation.RoundSphereGroundSymmetry
import continuation.RoundSpherePositiveGround

/-! The original rotation-invariance argument for the positive auxiliary
sphere ground. Simplicity is the proved strong-maximum-principle theorem;
orthogonal invariance is the proved naturality of the actual Laplacian. -/

noncomputable section
open Bundle Manifold Metric Module MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Laplacian
open DFLGroundSymmetry DFLGroundPositivity

namespace DFLGroundAxisymmetry

section GeneralSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

private theorem sphereConnected (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    [NeZero n] : ConnectedSpace (sphere (0 : E) 1) := by
  apply Subtype.connectedSpace
  apply isConnected_sphere _ _ (by norm_num : (0 : ℝ) ≤ 1)
  rw [← Module.finrank_eq_rank, (Fact.out : finrank ℝ E = n + 1)]
  exact_mod_cast (show 1 < n + 1 by have := NeZero.pos n; omega)

/-- Every actual orthogonal symmetry fixing the field axis fixes the
positive sphere eigenfunction pointwise. The pole fixes the scalar factor. -/
theorem positive_latitude_eigenfunction_invariant
    (axis : E) (haxis : ‖axis‖ = 1) (F : ℝ → ℝ) (hF : Continuous F)
    (u : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) (hu : ∀ x, 0 < u x) (lam : ℝ)
    (heig : ∀ x, -ΔG (roundMetric (E := E) (n := n)) u x +
      F (⟪axis, (x : E)⟫_ℝ) * u x = lam * u x)
    (e : E ≃ₗᵢ[ℝ] E) (he : e axis = axis) :
    ∀ x, u (sphereDiffeo (n := n) e x) = u x := by
  let _ : ConnectedSpace (sphere (0 : E) 1) := sphereConnected (E := E) n
  let g := roundMetric (E := E) (n := n)
  let V : sphere (0 : E) 1 → ℝ := fun x => F ⟪axis, (x : E)⟫_ℝ
  have hV : Continuous V := hF.comp (innerCoordFun (n := n) axis).contMDiff.continuous
  have hVe : ∀ x, V (sphereDiffeo (n := n) e x) = V x :=
    axis_potential_invariant axis F e he
  have heu : ∀ x, ΔG g u x = (V x - lam) * u x := by
    intro x
    have hh := heig x
    change ΔG g u x = (F ⟪axis, (x : E)⟫_ℝ - lam) * u x
    linarith
  have hef : ∀ x, ΔG g (orthogonalPullback e u) x =
      (V x - lam) * orthogonalPullback e u x := by
    intro x
    have hh := orthogonalPullback_schrodinger e V hVe u lam heig x
    linarith
  obtain ⟨c, hc⟩ := smooth_schrodinger_positive_eigenspace_simple
    g V hV lam u (orthogonalPullback e u) hu heu hef
  let pole : sphere (0 : E) 1 := ⟨axis, by simpa only [mem_sphere_zero_iff_norm] using haxis⟩
  have hpole : sphereDiffeo (n := n) e pole = pole := by
    apply Subtype.ext
    exact he
  have hc1 : c = 1 := by
    have hh := hc pole
    change u (sphereDiffeo (n := n) e pole) = c * u pole at hh
    rw [hpole] at hh
    have hz : (c - 1) * u pole = 0 := by linarith
    have hz' := (mul_eq_zero.mp hz).resolve_right (hu pole).ne'
    linarith
  intro x
  change orthogonalPullback e u x = u x
  rw [hc x, hc1, one_mul]

/-- The actual positive eigenfunction is constant on every true latitude,
including both poles. No zonality assumption is supplied. -/
theorem positive_latitude_eigenfunction_same_latitude
    (axis : E) (haxis : ‖axis‖ = 1) (F : ℝ → ℝ) (hF : Continuous F)
    (u : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯) (hu : ∀ x, 0 < u x) (lam : ℝ)
    (heig : ∀ x, -ΔG (roundMetric (E := E) (n := n)) u x +
      F (⟪axis, (x : E)⟫_ℝ) * u x = lam * u x)
    (x y : sphere (0 : E) 1) (hxy : ⟪axis, (x : E)⟫_ℝ = ⟪axis, (y : E)⟫_ℝ) :
    u x = u y := by
  obtain ⟨e, he, hex⟩ := same_latitude_orthogonal_symmetry (n := n) axis x y hxy
  have hi := positive_latitude_eigenfunction_invariant axis haxis F hF u hu lam heig e he x
  rw [hex] at hi
  exact hi.symm

end GeneralSphere

end DFLGroundAxisymmetry
