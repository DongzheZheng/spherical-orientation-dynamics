import continuation.GroundStateContinuity
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The Hellmann--Feynman formula for the actual full weak H¹ variational
minimum. Positive-ground continuity is derived from compactness and simplicity;
the derivative is obtained from the manuscript's two-sided Rayleigh comparison. -/
noncomputable section
set_option maxHeartbeats 1600000
open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator

namespace DFLHellmannFeynman
section Abstract
variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L]

private theorem polynomial_form_difference (J : H →L[ℝ] L) (A B C : L →L[ℝ] L)
    (r h : ℝ) (U : H) :
    DFLSphere.potentialForm J (A+(r+h) • B+(r+h)^2 • C) U U-
      DFLSphere.potentialForm J (A+r • B+r^2 • C) U U =
      h*⟪(B+(2*r) • C) (J U),J U⟫_ℝ+h^2*⟪C (J U),J U⟫_ℝ := by
  unfold DFLSphere.potentialForm
  simp only [add_apply,smul_apply,
    inner_add_left,real_inner_smul_left]
  ring

private theorem operator_energy_bound (C : L →L[ℝ] L) (u : L) (hu : ‖u‖ = 1) :
    |⟪C u,u⟫_ℝ| ≤ ‖C‖ := by
  calc
    _ ≤ ‖C u‖*‖u‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖C‖*‖u‖)*‖u‖ := mul_le_mul_of_nonneg_right (C.le_opNorm u) (norm_nonneg u)
    _ = ‖C‖ := by rw [hu]; ring

/-- Variational Hellmann--Feynman for a polynomial bounded perturbation.
Only continuity of the mass representative is required, and the sphere
application below proves that continuity from the original compact form. -/
theorem polynomial_rayleigh_hasDerivAt (J : H →L[ℝ] L) (A B C : L →L[ℝ] L)
    (lam : ℝ → ℝ) (U : ℝ → H) (r : ℝ)
    (hn : ∀ s, ‖J (U s)‖ = 1)
    (he : ∀ s, DFLSphere.potentialForm J (A+s • B+s^2 • C) (U s) (U s) = lam s)
    (hmin : ∀ s W, lam s*‖J W‖^2 ≤ DFLSphere.potentialForm J (A+s • B+s^2 • C) W W)
    (hU : ContinuousAt (fun s => J (U s)) r) :
    HasDerivAt lam ⟪(B+(2*r) • C) (J (U r)),J (U r)⟫_ℝ r := by
  let d := ⟪(B+(2*r) • C) (J (U r)),J (U r)⟫_ℝ
  let D := fun h => ⟪(B+(2*r) • C) (J (U (r+h))),J (U (r+h))⟫_ℝ
  have hbounds (h : ℝ) :
      h*D h+h^2*⟪C (J (U (r+h))),J (U (r+h))⟫_ℝ ≤ lam (r+h)-lam r ∧
      lam (r+h)-lam r ≤ h*d+h^2*⟪C (J (U r)),J (U r)⟫_ℝ := by
    have hlo := hmin r (U (r+h))
    have hhi := hmin (r+h) (U r)
    rw [hn] at hlo hhi
    norm_num at hlo hhi
    have hdiff₁ := polynomial_form_difference J A B C r h (U (r+h))
    have hdiff₂ := polynomial_form_difference J A B C r h (U r)
    rw [he (r+h)] at hdiff₁
    rw [he r] at hdiff₂
    dsimp only [D,d]
    constructor <;> linarith
  have herr (h : ℝ) :
      |lam (r+h)-lam r-h*d| ≤ |h| * |D h-d| +h^2*‖C‖ := by
    obtain ⟨hlo,hhi⟩ := hbounds h
    have hc₁ := abs_le.mp (operator_energy_bound C (J (U (r+h))) (hn (r+h)))
    have hc₀ := abs_le.mp (operator_energy_bound C (J (U r)) (hn r))
    have hm := (le_abs_self (h*(D h-d)))
    have hm' := (neg_abs_le (h*(D h-d)))
    rw [abs_mul] at hm hm'
    have hsq := sq_nonneg h
    have hpos := mul_nonneg (abs_nonneg h) (abs_nonneg (D h-d))
    have hmul₁ := mul_le_mul_of_nonneg_left hc₁.1 hsq
    have hmul₀ := mul_le_mul_of_nonneg_left hc₀.2 hsq
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  have hv : Tendsto (fun h => J (U (r+h))) (𝓝 (0 : ℝ)) (𝓝 (J (U r))) := by
    have hs : Tendsto (fun h : ℝ => r+h) (𝓝 0) (𝓝 r) := by
      have hi : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0) := tendsto_id
      simpa only [add_zero] using (tendsto_const_nhds (x := r)).add hi
    exact hU.tendsto.comp hs
  have hD : Tendsto D (𝓝 (0 : ℝ)) (𝓝 d) :=
    ((B+(2*r) • C).continuous.tendsto (J (U r)) |>.comp hv).inner (𝕜 := ℝ) hv
  have hq (h : ℝ) (hh : h ≠ 0) :
      |h⁻¹*(lam (r+h)-lam r)-d| ≤ |D h-d| +|h| *‖C‖ := by
    have ha : 0 < |h| := abs_pos.mpr hh
    have hid : h⁻¹*(lam (r+h)-lam r)-d = (lam (r+h)-lam r-h*d)/h := by field_simp
    rw [hid,abs_div]
    apply (div_le_iff₀ ha).mpr
    have hsq : h^2 = |h|^2 := (sq_abs h).symm
    have hherr := herr h
    rw [hsq] at hherr
    nlinarith [hherr]
  have hright : Tendsto (fun h => |D h-d| +|h| *‖C‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h₁ : Tendsto (fun h => |D h-d|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simpa only [sub_self,abs_zero] using
        ((hD.sub (tendsto_const_nhds (x := d))).abs).mono_left
          (nhdsWithin_le_nhds (s := {0}ᶜ))
    have hi : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0) := tendsto_id
    have h₂ : Tendsto (fun h : ℝ => |h| *‖C‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simpa only [abs_zero,zero_mul] using (hi.abs.mul_const ‖C‖).mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa only [zero_add] using h₁.add h₂
  have hzero : Tendsto (fun h => |h⁻¹*(lam (r+h)-lam r)-d|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hright
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact hq h hh
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs,smul_eq_mul] using hzero
end Abstract
end DFLHellmannFeynman

namespace DFLSphere
private local instance (k : ℕ) : MeasurableSpace (RoundSphere k) := borel (RoundSphere k)
private local instance (k : ℕ) : BorelSpace (RoundSphere k) := ⟨rfl⟩
private local instance (k : ℕ) : IsFiniteMeasure (roundVolume k) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (roundSphereMetric k)

theorem positiveGround_continuousAt_of_potential_continuousAt (k : ℕ)
    (V : ℝ → C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (r : ℝ)
    (hV : ContinuousAt (fun s => continuousOfSmoothPotential k (V s)) r) :
    ContinuousAt (fun s => smoothToH1Compl (roundSphereMetric k) (positiveGround k (V s))) r := by
  apply Filter.tendsto_of_seq_tendsto
  intro seq hseq
  exact positiveGround_tendsto_of_potential_tendsto k (V ∘ seq) (V r) (hV.tendsto.comp hseq)

/-- Linear and quadratic coefficients of the original r tilt. -/
def roundTiltLinearPotential (k : ℕ) (a : ℝ) : C(RoundSphere k,ℝ) :=
  ⟨fun x => -a*(roundCoordinate k).toFun x,
    continuous_const.mul (roundCoordinate k).smooth.continuous⟩

def roundTiltQuadraticPotential (k : ℕ) : C(RoundSphere k,ℝ) :=
  ⟨fun x => (1-((roundCoordinate k).toFun x)^2)/4,
    (continuous_const.sub ((roundCoordinate k).smooth.continuous.pow 2)).div_const 4⟩

theorem roundTiltContinuousPotential_polynomial (k : ℕ) (lam0 a r : ℝ) :
    roundTiltContinuousPotential k lam0 r a = ContinuousMap.const (RoundSphere k) lam0+
      r • roundTiltLinearPotential k a+r^2 • roundTiltQuadraticPotential k := by
  ext x
  change lam0+r^2/4*(1-((roundCoordinate k).toFun x)^2)-a*r*(roundCoordinate k).toFun x =
    lam0+r*(-a*(roundCoordinate k).toFun x)+r^2*((1-((roundCoordinate k).toFun x)^2)/4)
  ring

theorem roundTiltContinuousPotential_continuous_r (k : ℕ) (lam0 a : ℝ) :
    Continuous (fun r => roundTiltContinuousPotential k lam0 r a) := by
  simp only [roundTiltContinuousPotential_polynomial]
  fun_prop

/-- The actual positive normalized tilted ground has a continuous full
H¹ representative for every real external-field parameter. -/
theorem roundTiltPositiveGround_continuous_r (k : ℕ) (lam0 a : ℝ) :
    Continuous (fun r => smoothToH1Compl (roundSphereMetric k)
      (positiveGround k (roundTiltSmoothPotential k lam0 r a))) := by
  rw [continuous_iff_continuousAt]
  intro r
  apply positiveGround_continuousAt_of_potential_continuousAt
  exact (roundTiltContinuousPotential_continuous_r k lam0 a).continuousAt

private theorem potentialOperator_diag (k : ℕ) (V : C(RoundSphere k,ℝ))
    (U : H1Compl (roundSphereMetric k)) :
    potentialForm (H1ComplToLp (roundSphereMetric k)) (roundContinuousPotentialOperator k V) U U =
      roundPotentialEnergy k V U := by
  rw [roundContinuousPotentialOperator_form,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  unfold roundPotentialEnergy
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- Hellmann--Feynman for the original full-domain minimum:
no derivative, differentiable eigenbranch, or spectral-response premise is assumed. -/
theorem roundTiltMinimum_hasDerivAt_r (k : ℕ) (lam0 a r : ℝ) :
    HasDerivAt (fun s => roundTiltMinimum k lam0 s a)
      (∫ x, (r*(1-((roundCoordinate k).toFun x)^2)/2-a*(roundCoordinate k).toFun x)*
        ((positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x)^2 ∂roundVolume k) r := by
  let g := roundSphereMetric k
  let J := H1ComplToLp g
  let U := fun s => smoothToH1Compl g (positiveGround k (roundTiltSmoothPotential k lam0 s a))
  let A := roundContinuousPotentialOperator k (ContinuousMap.const (RoundSphere k) lam0)
  let B := roundContinuousPotentialOperator k (roundTiltLinearPotential k a)
  let C := roundContinuousPotentialOperator k (roundTiltQuadraticPotential k)
  have hP (s : ℝ) : roundContinuousPotentialOperator k (roundTiltContinuousPotential k lam0 s a) =
      A+s • B+s^2 • C := by
    rw [roundTiltContinuousPotential_polynomial,map_add,map_add,map_smul,map_smul]
  have hn : ∀ s, ‖J (U s)‖ = 1 := by
    intro s
    rw [H1ComplToLp_smoothToH1Compl]
    exact (positiveGround_spec k (roundTiltSmoothPotential k lam0 s a)).1
  have he : ∀ s, potentialForm J (A+s • B+s^2 • C) (U s) (U s) = roundTiltMinimum k lam0 s a := by
    intro s
    rw [← hP,potentialOperator_diag]
    exact (positiveGround_spec k (roundTiltSmoothPotential k lam0 s a)).2.2.1
  have hmin : ∀ s W, roundTiltMinimum k lam0 s a*‖J W‖^2 ≤
      potentialForm J (A+s • B+s^2 • C) W W := by
    intro s W
    rw [← hP,potentialOperator_diag]
    exact (positiveGround_spec k (roundTiltSmoothPotential k lam0 s a)).2.2.2.1 W
  have hu : ContinuousAt (fun s => J (U s)) r :=
    J.continuous.continuousAt.comp (roundTiltPositiveGround_continuous_r k lam0 a).continuousAt
  have hh := DFLHellmannFeynman.polynomial_rayleigh_hasDerivAt J A B C
    (fun s => roundTiltMinimum k lam0 s a) U r hn he hmin hu
  have hd : ⟪(B+(2*r) • C) (J (U r)),J (U r)⟫_ℝ =
      ∫ x, (r*(1-((roundCoordinate k).toFun x)^2)/2-a*(roundCoordinate k).toFun x)*
        ((positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x)^2 ∂roundVolume k := by
    let Vd := roundTiltLinearPotential k a+(2*r) • roundTiltQuadraticPotential k
    have hPd : B+(2*r) • C = roundContinuousPotentialOperator k Vd := by
      rw [map_add,map_smul]
    rw [hPd]
    have hVd : MemLp (Vd : RoundSphere k → ℝ) ∞ (roundVolume k) :=
      Vd.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [roundContinuousPotentialOperator_eq k Vd hVd,boundedPotentialMultiplication_inner]
    apply integral_congr_ae
    filter_upwards [(positiveGround k (roundTiltSmoothPotential k lam0 r a)).memLp_two.coeFn_toLp] with x hx
    have hxU : J (U r) x = (positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x := by
      rw [H1ComplToLp_smoothToH1Compl]
      exact hx
    rw [hxU]
    change (-a*(roundCoordinate k).toFun x+(2*r)*((1-((roundCoordinate k).toFun x)^2)/4))*
      (positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x*
      (positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x = _
    ring
  rw [hd] at hh
  exact hh

theorem roundTiltMinimum_deriv_r (k : ℕ) (lam0 a r : ℝ) :
    deriv (fun s => roundTiltMinimum k lam0 s a) r =
      ∫ x, (r*(1-((roundCoordinate k).toFun x)^2)/2-a*(roundCoordinate k).toFun x)*
        ((positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x)^2 ∂roundVolume k :=
  (roundTiltMinimum_hasDerivAt_r k lam0 a r).deriv

theorem roundTiltMinimum_differentiable_r (k : ℕ) (lam0 a : ℝ) :
    Differentiable ℝ (fun r => roundTiltMinimum k lam0 r a) :=
  fun r => (roundTiltMinimum_hasDerivAt_r k lam0 a r).differentiableAt

end DFLSphere
