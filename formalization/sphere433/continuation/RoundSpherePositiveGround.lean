import continuation.RoundSphereGroundDomain
import continuation.SmoothAbsoluteH1
import continuation.SmoothSchrodingerPositivity
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The original absolute-value minimum argument on the full weak H¹ domain:
absolute values contract the gradient energy, so a nonnegative minimizer exists;
elliptic regularity and the actual strong maximum principle make it positive.
The same strong maximum principle proves simplicity of its eigenspace. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator

namespace DFLSphere
section Critical
variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L]

/-- Any attained global Rayleigh lower bound satisfies the true weak Euler
identity. This follows from nonnegativity of its quadratic variation. -/
theorem potentialForm_minimizer_weak (J : H →L[ℝ] L) (P : L →L[ℝ] L)
    (hP : P.IsSymmetric) (lam : ℝ) (u : H)
    (he : potentialForm J P u u = lam*‖J u‖^2)
    (hmin : ∀ v : H, lam*‖J v‖^2 ≤ potentialForm J P v v) :
    ∀ v : H, potentialForm J P u v = lam*⟪J u,J v⟫_ℝ := by
  intro v
  let a := potentialForm J P v v-lam*‖J v‖^2
  let b := potentialForm J P u v-lam*⟪J u,J v⟫_ℝ
  have hp : ∀ t : ℝ, 0 ≤ a*t^2+2*b*t := by
    intro t
    have hh := sub_nonneg.mpr (hmin (u+t • v))
    have hexp : potentialForm J P (u+t • v) (u+t • v) =
        potentialForm J P u u+2*t*potentialForm J P u v+t^2*potentialForm J P v v := by
      unfold potentialForm
      simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
        real_inner_smul_right]
      have hs : ⟪P (J v),J u⟫_ℝ = ⟪P (J u),J v⟫_ℝ :=
        (hP (J v) (J u)).trans (real_inner_comm (J v) (P (J u))).symm
      rw [real_inner_comm v u,real_inner_comm (J v) (J u),hs]
      ring
    have hnorm : ‖J (u+t • v)‖^2 = ‖J u‖^2+2*t*⟪J u,J v⟫_ℝ+t^2*‖J v‖^2 := by
      rw [← real_inner_self_eq_norm_sq,map_add,map_smul]
      simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
      rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_comm (J v) (J u)]
      ring
    rw [hexp,hnorm,he] at hh
    dsimp [a,b]
    nlinarith [hh]
  have ha : 0 ≤ a := sub_nonneg.mpr (hmin v)
  have hb : b = 0 := by
    by_contra hbn
    have hbsq : 0 < b^2 := sq_pos_of_ne_zero hbn
    by_cases haz : a = 0
    · have hh := hp (-b)
      rw [haz] at hh
      nlinarith
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
      have hh := hp (-b/a)
      have hi : a*(-b/a)^2+2*b*(-b/a) = -(b^2)/a := by field_simp; ring
      rw [hi] at hh
      have hneg : -(b^2)/a < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hbsq) hap
      linarith
  dsimp [b] at hb
  linarith

end Critical

private local instance (k : ℕ) : MeasurableSpace (RoundSphere k) := borel (RoundSphere k)
private local instance (k : ℕ) : BorelSpace (RoundSphere k) := ⟨rfl⟩
private local instance (k : ℕ) : IsFiniteMeasure (roundVolume k) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (roundSphereMetric k)

private local instance (k : ℕ) : (roundVolume k).IsOpenPosMeasure :=
  riemannianVolumeMeasure_isOpenPosMeasure (roundSphereMetric k)

/-- Every original full-domain minimizer satisfies the actual weak potential
Schrödinger equation; no critical-point property is assumed. -/
theorem round_potential_minimizer_weak (k : ℕ) (V : RoundSphere k → ℝ)
    (hV : Continuous V) (lam : ℝ) (U : H1Compl (roundSphereMetric k))
    (he : roundPotentialEnergy k V U = lam*‖H1ComplToLp (roundSphereMetric k) U‖^2)
    (hmin : ∀ W : H1Compl (roundSphereMetric k),
      lam*‖H1ComplToLp (roundSphereMetric k) W‖^2 ≤ roundPotentialEnergy k V W) :
    IsRoundWeakPotentialEigenstate k V lam U := by
  let J := H1ComplToLp (roundSphereMetric k)
  have hVtop : MemLp V ∞ (roundVolume k) :=
    hV.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P := boundedPotentialMultiplication V hVtop
  have hform (W Z : H1Compl (roundSphereMetric k)) :
      potentialForm J P W Z = ⟪W,Z⟫_ℝ-⟪J W,J Z⟫_ℝ+
        ∫ x, V x*J W x*J Z x ∂roundVolume k := by
    unfold potentialForm
    rw [boundedPotentialMultiplication_inner]
  have hdiag (W : H1Compl (roundSphereMetric k)) :
      potentialForm J P W W = roundPotentialEnergy k V W := by
    rw [hform,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
    unfold roundPotentialEnergy
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hw := potentialForm_minimizer_weak J P (boundedPotentialMultiplication_symmetric V hVtop)
    lam U (by rw [hdiag]; exact he) (fun W => by rw [hdiag]; exact hmin W)
  intro W
  have hh := hw W
  rw [hform] at hh
  exact hh

/-- A normalized, strictly positive smooth lowest eigenfunction exists for
any actual smooth potential, with comparison against every true weak H¹ state. -/
theorem round_positive_smooth_potential_ground_exists (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) :
    ∃ (lam : ℝ) (u : SmoothScalar (roundSphereMetric k)),
      ‖smoothToLp (roundSphereMetric k) u‖ = 1 ∧
      (∀ x : RoundSphere k, 0 < u.toFun x) ∧
      roundPotentialEnergy k V (smoothToH1Compl (roundSphereMetric k) u) = lam ∧
      (∀ W : H1Compl (roundSphereMetric k),
        lam*‖H1ComplToLp (roundSphereMetric k) W‖^2 ≤ roundPotentialEnergy k V W) ∧
      ∀ x : RoundSphere k,
        -ΔG (roundSphereMetric k) u.toContMDiffMap x+V x*u.toFun x = lam*u.toFun x := by
  let g := roundSphereMetric k
  obtain ⟨lam,f,hfnorm,hfe,hmin,_⟩ := round_smooth_potential_ground_classical_exists k V
  obtain ⟨A,hA,hAnorm,hAE⟩ := DFLAbsoluteH1.smooth_absolute_exists_completion g f
  have hn : ‖H1ComplToLp g A‖ = 1 := hAnorm.trans hfnorm
  have hpot : (∫ x, V x*(H1ComplToLp g A x)^2 ∂roundVolume k) =
      ∫ x, V x*(H1ComplToLp g (smoothToH1Compl g f) x)^2 ∂roundVolume k := by
    apply integral_congr_ae
    filter_upwards [hA,f.memLp_two.coeFn_toLp] with x ha hf
    have hff : H1ComplToLp g (smoothToH1Compl g f) x = f.toFun x := by
      rw [H1ComplToLp_smoothToH1Compl]
      exact hf
    rw [ha,hff,sq_abs]
  have he_le : roundPotentialEnergy k V A ≤ lam := by
    unfold roundPotentialEnergy
    rw [hpot]
    have hfE := h1_smooth_energy g f
    have hh := hfe
    unfold roundPotentialEnergy at hh
    rw [hfE] at hh
    linarith
  have he : roundPotentialEnergy k V A = lam := by
    have hlo := hmin A
    rw [hn] at hlo
    norm_num at hlo
    exact le_antisymm he_le hlo
  have hweak := round_potential_minimizer_weak k V V.contMDiff.continuous lam A
    (by rw [he,hn]; ring) hmin
  obtain ⟨u,hAu,hpoint⟩ := round_weak_smooth_potential_eigen_pointwise k V lam A hweak
  have hau : (H1ComplToLp g A : RoundSphere k → ℝ) =ᵐ[roundVolume k] u.toFun := by
    rw [hAu,H1ComplToLp_smoothToH1Compl]
    exact u.memLp_two.coeFn_toLp
  have huf : u.toFun = fun x => |f.toFun x| :=
    MeasureTheory.Measure.eq_of_ae_eq (hau.symm.trans hA) u.smooth.continuous f.smooth.continuous.abs
  have hunn : ∀ x, 0 ≤ u.toFun x := by intro x; rw [huf]; exact abs_nonneg _
  have hun : ‖smoothToLp g u‖ = 1 := by rw [hAu,H1ComplToLp_smoothToH1Compl] at hn; exact hn
  have hunz : ∃ x, u.toFun x ≠ 0 := by
    by_contra h
    push Not at h
    have hz : smoothToLp g u = 0 := by
      apply Lp.ext
      filter_upwards [u.memLp_two.coeFn_toLp,Lp.coeFn_zero ℝ 2 (roundVolume k)] with x hx hzero
      have hxu : (smoothToLp g u : RoundSphere k → ℝ) x = u.toFun x := hx
      rw [hxu,h x,hzero]
      rfl
    rw [hz,norm_zero] at hun
    norm_num at hun
  have hu : ∀ x, 0 < u.toFun x :=
    DFLGroundPositivity.smooth_schrodinger_nonnegative_strict_positive g u.toContMDiffMap
      V V.contMDiff.continuous lam (fun x => by
        have hh := hpoint x
        change ΔG (roundSphereMetric k) u.toContMDiffMap x = (V x-lam)*u.toFun x
        nlinarith [hh])
      hunn hunz
  refine ⟨lam,u,hun,hu,?_,hmin,hpoint⟩
  rw [← hAu]
  exact he

/-- Any strictly positive actual smooth eigenfunction spans the complete
smooth eigenspace for the same potential and eigenvalue. -/
theorem round_positive_potential_eigenspace_simple (k : ℕ)
    (V : RoundSphere k → ℝ) (hV : Continuous V) (lam : ℝ)
    (u f : SmoothScalar (roundSphereMetric k))
    (hu : ∀ x, 0 < u.toFun x)
    (heigu : ∀ x, -ΔG (roundSphereMetric k) u.toContMDiffMap x+V x*u.toFun x = lam*u.toFun x)
    (heigf : ∀ x, -ΔG (roundSphereMetric k) f.toContMDiffMap x+V x*f.toFun x = lam*f.toFun x) :
    ∃ c : ℝ, ∀ x, f.toFun x = c*u.toFun x := by
  have heu : ∀ x, ΔG (roundSphereMetric k) u.toContMDiffMap x = (V x-lam)*u.toContMDiffMap x := by
    intro x
    change ΔG (roundSphereMetric k) u.toContMDiffMap x = (V x-lam)*u.toFun x
    nlinarith [heigu x]
  have hef : ∀ x, ΔG (roundSphereMetric k) f.toContMDiffMap x = (V x-lam)*f.toContMDiffMap x := by
    intro x
    change ΔG (roundSphereMetric k) f.toContMDiffMap x = (V x-lam)*f.toFun x
    nlinarith [heigf x]
  exact DFLGroundPositivity.smooth_schrodinger_positive_eigenspace_simple
    (roundSphereMetric k) V hV lam u.toContMDiffMap f.toContMDiffMap hu heu hef

/-- Simplicity covers the entire original distributional weak H¹ eigenspace:
regularity is a conclusion, and the state is a multiple of the positive ground. -/
theorem round_positive_potential_weak_eigenspace_simple (k : ℕ)
    (V : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (lam : ℝ)
    (u : SmoothScalar (roundSphereMetric k)) (hu : ∀ x, 0 < u.toFun x)
    (heigu : ∀ x, -ΔG (roundSphereMetric k) u.toContMDiffMap x+V x*u.toFun x = lam*u.toFun x)
    (U : H1Compl (roundSphereMetric k)) (hU : IsRoundWeakPotentialEigenstate k V lam U) :
    ∃ c : ℝ, U = c • smoothToH1Compl (roundSphereMetric k) u := by
  obtain ⟨f,hUf,hef⟩ := round_weak_smooth_potential_eigen_pointwise k V lam U hU
  obtain ⟨c,hf⟩ := round_positive_potential_eigenspace_simple k V V.contMDiff.continuous
    lam u f hu heigu hef
  have hfc : f = c • u := by
    apply SmoothScalar.ext
    funext x
    exact hf x
  refine ⟨c,?_⟩
  rw [hUf,hfc]
  exact (smoothToH1Compl (roundSphereMetric k)).map_smul c u

/-- The original polynomial latitude tilt admits an actual strictly positive
normalized smooth ground for every real parameter, in the full weak domain. -/
theorem round_tilt_positive_smooth_ground_exists (k : ℕ) (lam0 r a : ℝ) :
    ∃ (lam : ℝ) (u : SmoothScalar (roundSphereMetric k)),
      ‖smoothToLp (roundSphereMetric k) u‖ = 1 ∧
      (∀ x : RoundSphere k, 0 < u.toFun x) ∧
      roundPotentialEnergy k (roundTiltPotential k lam0 r a)
        (smoothToH1Compl (roundSphereMetric k) u) = lam ∧
      (∀ W : H1Compl (roundSphereMetric k),
        lam*‖H1ComplToLp (roundSphereMetric k) W‖^2 ≤
          roundPotentialEnergy k (roundTiltPotential k lam0 r a) W) ∧
      ∀ x : RoundSphere k,
        -ΔG (roundSphereMetric k) u.toContMDiffMap x+
          roundTiltPotential k lam0 r a x*u.toFun x = lam*u.toFun x :=
  round_positive_smooth_potential_ground_exists k (roundTiltSmoothPotential k lam0 r a)

end DFLSphere
