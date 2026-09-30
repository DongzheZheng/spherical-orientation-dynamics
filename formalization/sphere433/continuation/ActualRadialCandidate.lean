import continuation.PhysicalSphereLatitudeProfileC3
import continuation.RadialEigenvalueLower

/-! Actual smooth zonal positive-eigenvalue candidates on every physical
S^(k+1), including S¹, satisfy the original radial equation and its actual
auxiliary-ground lower bound. Genuine pole regularity is proved upstream. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold Metric Module Set Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DFLSpectralCoordinates DFLLatitudeOperator DFL.Spectral DFLSphere
open DFLTransverseSphere DFLPhysicalLatitude
namespace DFLActualRadial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+1)] [NeZero n]

omit [FiniteDimensional ℝ E] in
/-- The true weighted round operator reduces to the original radial
expression by the actual scalar Laplacian and gradient chain rules. -/
theorem weightedRoundApply_latitude (p : E) (hp : ‖p‖ = 1) (r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (x : sphere (0 : E) 1) :
    weightedRoundApply (n := n) p r
      (fun y : sphere (0 : E) 1 => v ⟪p,(y : E)⟫_ℝ) x =
      radialApply n r v ⟪p,(x : E)⟫_ℝ := by
  let g := roundMetric (E := E) (n := n)
  let t := innerCoordFun (n := n) p
  let h := fun y : sphere (0 : E) 1 => v (t y)
  have hc := gradientFun_comp g (hv.differentiable (by norm_num) (t x))
    (t.contMDiff.mdifferentiable (by simp) x)
  change gradientFun g h x = deriv v (t x) • gradientFun g t x at hc
  have hd : g.inner x (gradientFun g t x) (gradientFun g h x) =
      deriv v (t x)*(1-(t x)^2) := by
    rw [hc]
    simp only [map_smul,smul_eq_mul]
    rw [latitude_gradient_norm_sq (n := n) p hp x]
    rfl
  have hl := latitude_laplacian (n := n) p hp v hv x
  change laplacian (LeviCivita g) g h x = _ at hl
  change -laplacian (LeviCivita g) g h x-
    r*g.inner x (gradientFun g t x) (gradientFun g h x) = _
  rw [hl,hd]
  unfold radialApply
  change -((1-⟪p,(x : E)⟫_ℝ^2)*deriv (deriv v) ⟪p,(x : E)⟫_ℝ-
    (n : ℝ)*⟪p,(x : E)⟫_ℝ *deriv v ⟪p,(x : E)⟫_ℝ)-
    r*(deriv v ⟪p,(x : E)⟫_ℝ *(1-⟪p,(x : E)⟫_ℝ^2)) = _
  ring

/-- Genuine physical sphere eigenfunctions produce an original C³
radial eigenprofile; no latitude profile regularity is supplied as input. -/
theorem actual_radial_candidate_C3_profile (k : ℕ) (r lam : ℝ)
    (u : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯)
    (hlat : PhysicalConstantOnLatitudes k u)
    (heig : ∀ x, weightedRoundApply (n := k+1)
      (EuclideanSpace.single 0 1 : PhysicalAmbient k) r u x = lam*u x) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 3 f ∧
      (∀ x, u x = f ((physicalCoordinate k).toFun x)) ∧
      RadialEigenEquation (k+1) r lam f := by
  obtain ⟨f,hf,hfu⟩ := physical_smooth_same_latitude_exists_C3_profile k u hlat
  refine ⟨f,hf,hfu,?_⟩
  have hufun : (u : PhysicalSphere k → ℝ) =
      fun y : PhysicalSphere k => f ⟪(EuclideanSpace.single 0 1 : PhysicalAmbient k),(y : PhysicalAmbient k)⟫_ℝ :=
    funext hfu
  intro t ht
  obtain ⟨x,hx⟩ := physicalCoordinate_surjective_Icc k t ⟨ht.1.le,ht.2.le⟩
  have hh := heig x
  rw [hufun,weightedRoundApply_latitude (n := k+1) _ (by simp) r f
    (hf.of_le (by decide : (2 : ℕ∞ω) ≤ 3)) x] at hh
  change radialApply (k+1) r f t = _
  change radialApply (k+1) r f ((physicalCoordinate k).toFun x) =
    lam*f ((physicalCoordinate k).toFun x) at hh
  rw [hx] at hh
  exact hh

/-- Every genuine nonzero smooth radial sphere candidate with λ≠0 obeys
the actual auxiliary-sphere minimum lower bound, in every dimension ≥1. -/
theorem actual_radial_eigenvalue_ge_actual_ground (k : ℕ) (r lam : ℝ)
    (hlam : lam ≠ 0) (u : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯)
    (hlat : PhysicalConstantOnLatitudes k u)
    (heig : ∀ x, weightedRoundApply (n := k+1)
      (EuclideanSpace.single 0 1 : PhysicalAmbient k) r u x = lam*u x)
    (hne : ∃ x, u x ≠ 0) :
    roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2-1) ≤ lam := by
  obtain ⟨f,hf,hfu,he⟩ := actual_radial_candidate_C3_profile k r lam u hlat heig
  have hfne : ∃ t ∈ Ioo (-1 : ℝ) 1, f t ≠ 0 := by
    by_contra h
    have hz : Ioo (-1 : ℝ) 1 ⊆ {t : ℝ | f t = 0} := by
      intro t ht
      by_contra hft
      exact h ⟨t,ht,hft⟩
    have hcl := closure_minimal hz (isClosed_eq hf.continuous continuous_const)
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] at hcl
    obtain ⟨x,hx⟩ := hne
    exact hx (by rw [hfu x]; exact hcl (physicalCoordinate_mem_Icc k x))
  simpa only [Nat.cast_add,Nat.cast_one] using
    radial_eigenvalue_ge_actual_ground (k+1) r lam hlam f hf he hfne

/-- The actual radial candidate cannot lie below the physical transverse
candidate in any dimension. The circle equality of partner minima is
proved rather than inferred from the higher-dimensional strict case. -/
theorem actual_radial_eigenvalue_ge_transverse_ground (k : ℕ) (r lam : ℝ)
    (hr : 0 < r) (hlam : lam ≠ 0)
    (u : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯)
    (hlat : PhysicalConstantOnLatitudes k u)
    (heig : ∀ x, weightedRoundApply (n := k+1)
      (EuclideanSpace.single 0 1 : PhysicalAmbient k) r u x = lam*u x)
    (hne : ∃ x, u x ≠ 0) :
    roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2) ≤ lam := by
  have hlow := actual_radial_eigenvalue_ge_actual_ground k r lam hlam u hlat heig hne
  have horder := radial_transverse_actual_ground_le (k+1) (by omega) r hr
  have ho : roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2) ≤
      roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2-1) := by
    simpa only [Nat.cast_add,Nat.cast_one] using horder
  exact ho.trans hlow

/-- In every physical dimension at least two, a nonzero radial candidate
lies strictly above the actual first-transverse candidate for positive r. -/
theorem actual_radial_eigenvalue_gt_transverse_ground (k : ℕ) (hk : 1 ≤ k)
    (r lam : ℝ) (hr : 0 < r) (hlam : lam ≠ 0)
    (u : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯)
    (hlat : PhysicalConstantOnLatitudes k u)
    (heig : ∀ x, weightedRoundApply (n := k+1)
      (EuclideanSpace.single 0 1 : PhysicalAmbient k) r u x = lam*u x)
    (hne : ∃ x, u x ≠ 0) :
    roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2) < lam := by
  have hlow := actual_radial_eigenvalue_ge_actual_ground k r lam hlam u hlat heig hne
  have horder := original_radial_transverse_actual_ground_ordering (k+1) (by omega) r hr
  have ha : (((k+1 : ℕ) : ℝ)-2)/2 = (k+1 : ℝ)/2-1 := by push_cast; ring
  rw [ha] at horder
  have ho : roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2) <
      roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2-1) := by
    simpa only [Nat.cast_add,Nat.cast_one] using horder
  exact ho.trans_le hlow

end DFLActualRadial
