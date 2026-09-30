import DFLSphere433.OriginalLatitude.GroundMoments

/-!
# The manuscript's fixed-domain Hellmann--Feynman step

For the exact half-density operator, a two-pole Green identity eliminates
the derivative of an eigenfunction from the differentiated eigen-equation.
Thus the Hellmann--Feynman equality is derived, rather than supplied as a
premise. The smooth eigenpair and its differentiated equation are explicit
inputs; their construction by the source's compact elliptic operator and
analytic perturbation theorems is not asserted here.
-/

namespace DFL.Spectral

open Set MeasureTheory
open scoped Interval

noncomputable section

def halfDensityPotential (M : ℕ) (b lam0 r t : ℝ) : ℝ :=
  lam0 + r ^ 2 * (1 - t ^ 2) / 4 + (b - (M : ℝ) / 2) * r * t

def halfDensityApply (M : ℕ) (b lam0 r : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(1 - t ^ 2) * deriv (deriv u) t + (M : ℝ) * t * deriv u t +
    halfDensityPotential M b lam0 r t * u t

def halfDensityPotentialPrime (M : ℕ) (b r t : ℝ) : ℝ :=
  r / 2 * (1 - t ^ 2) + (b - (M : ℝ) / 2) * t

theorem halfDensityApply_continuous (M : ℕ) (b lam0 r : ℝ)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) :
    Continuous (halfDensityApply M b lam0 r u) := by
  have hu1 : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hu2 : ContDiff ℝ 0 (deriv (deriv u)) := hu1.deriv'
  unfold halfDensityApply halfDensityPotential
  fun_prop

/-- Exact two-pole Green identity for the fixed half-density realization.
The potential cancels and the genuine flux coefficient vanishes at both
poles. This is a smooth-core identity, without an operator-domain claim. -/
theorem halfDensity_green_identity
    (M : ℕ) (hM : 2 ≤ M) (b lam0 r : ℝ)
    (u g : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hg : ContDiff ℝ 2 g) :
    (∫ t in (-1 : ℝ)..1, radialWeight M 0 t *
      (u t * halfDensityApply M b lam0 r g t -
        g t * halfDensityApply M b lam0 r u t)) = 0 := by
  have hm : 0 < M := by omega
  have hu1 : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hg1 : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hu2 : ContDiff ℝ 0 (deriv (deriv u)) := hu1.deriv'
  have hg2 : ContDiff ℝ 0 (deriv (deriv g)) := hg1.deriv'
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hud' : Differentiable ℝ (deriv u) := hu1.differentiable (by norm_num)
  have hgd' : Differentiable ℝ (deriv g) := hg1.differentiable (by norm_num)
  let F : ℝ → ℝ := fun t => latitudeFluxFactor M 0 t *
    (g t * deriv u t - u t * deriv g t)
  have hF : Continuous F := (latitudeFluxFactor_continuous M 0).mul
    ((hg.continuous.mul hu1.continuous).sub (hu.continuous.mul hg1.continuous))
  have hderiv : ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt F (radialWeight M 0 t *
        (u t * halfDensityApply M b lam0 r g t -
          g t * halfDensityApply M b lam0 r u t)) t := by
    intro t ht
    convert (latitudeFluxFactor_hasDerivAt M 0 ht).mul
      (((hgd t).hasDerivAt.mul (hud' t).hasDerivAt).sub
        ((hud t).hasDerivAt.mul (hgd' t).hasDerivAt)) using 1
    all_goals try rfl
    rw [latitudeFluxFactor_eq_weight M 0 ht]
    unfold halfDensityApply
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hint : IntervalIntegrable (fun t => radialWeight M 0 t *
      (u t * halfDensityApply M b lam0 r g t -
        g t * halfDensityApply M b lam0 r u t)) volume (-1 : ℝ) 1 :=
    ((radialWeight_continuous_ge_two M hM 0).mul
      ((hu.continuous.mul (halfDensityApply_continuous M b lam0 r g hg)).sub
        (hg.continuous.mul (halfDensityApply_continuous M b lam0 r u hu)))).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1 : ℝ) ≤ 1) hF.continuousOn hderiv hint
  simpa [F, latitudeFluxFactor_left M hm 0, latitudeFluxFactor_right M hm 0] using hFTC

/-- Source-aligned fixed-space eigen-equation and its actual parameter
derivative equation imply the unnormalized Hellmann--Feynman identity. -/
theorem halfDensity_HF_integral
    (M : ℕ) (hM : 2 ≤ M) (b lam0 r lam lamPrime : ℝ)
    (u g : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hg : ContDiff ℝ 2 g)
    (heigen : ∀ t ∈ Ioo (-1 : ℝ) 1,
      halfDensityApply M b lam0 r u t = lam * u t)
    (hparameter : ∀ t ∈ Ioo (-1 : ℝ) 1,
      halfDensityApply M b lam0 r g t +
        halfDensityPotentialPrime M b r t * u t =
      lamPrime * u t + lam * g t) :
    lamPrime * (∫ t in (-1 : ℝ)..1, radialWeight M 0 t * (u t) ^ 2) =
      ∫ t in (-1 : ℝ)..1,
        radialWeight M 0 t * halfDensityPotentialPrime M b r t * (u t) ^ 2 := by
  have hGreen := halfDensity_green_identity M hM b lam0 r u g hu hg
  have hcongr : (∫ t in (-1 : ℝ)..1, radialWeight M 0 t *
      (u t * halfDensityApply M b lam0 r g t -
        g t * halfDensityApply M b lam0 r u t)) =
      ∫ t in (-1 : ℝ)..1, lamPrime * (radialWeight M 0 t * (u t) ^ 2) -
        radialWeight M 0 t * halfDensityPotentialPrime M b r t * (u t) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    have hone : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
      rw [ae_iff]
      simp
    filter_upwards [hone] with t hne ht
    have hti : t ∈ Ioo (-1 : ℝ) 1 := by
      have htic : t ∈ Ioc (-1 : ℝ) 1 := by
        simpa only [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
      exact ⟨htic.1, lt_of_le_of_ne htic.2 hne⟩
    rw [heigen t hti]
    linear_combination radialWeight M 0 t * u t * hparameter t hti
  rw [hcongr] at hGreen
  have hnorm : Continuous (fun t => radialWeight M 0 t * (u t) ^ 2) :=
    (radialWeight_continuous_ge_two M hM 0).mul (hu.continuous.pow 2)
  have hpot : Continuous (fun t => radialWeight M 0 t *
      halfDensityPotentialPrime M b r t * (u t) ^ 2) := by
    have hp : Continuous (halfDensityPotentialPrime M b r) := by
      unfold halfDensityPotentialPrime
      fun_prop
    exact ((radialWeight_continuous_ge_two M hM 0).mul hp).mul (hu.continuous.pow 2)
  rw [intervalIntegral.integral_sub
    ((hnorm.intervalIntegrable (μ := volume) (-1 : ℝ) 1).const_mul lamPrime)
    (hpot.intervalIntegrable (μ := volume) (-1 : ℝ) 1),
    intervalIntegral.integral_const_mul] at hGreen
  exact sub_eq_zero.mp hGreen

def halfDensityLift (r : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp ((r / 2) * t) * v t

theorem halfDensityLift_smooth (r : ℝ) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 2 (halfDensityLift r v) := by
  have he : ContDiff ℝ 2 (fun t : ℝ => Real.exp ((r / 2) * t)) :=
    (contDiff_const.mul contDiff_id).exp
  exact he.mul hv

theorem halfDensityLift_deriv (r : ℝ) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (t : ℝ) :
    deriv (halfDensityLift r v) t =
      Real.exp ((r / 2) * t) * (deriv v t + r / 2 * v t) := by
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have he := ((hasDerivAt_id t).const_mul (r / 2)).exp
  have h := (he.mul (hvd t).hasDerivAt).deriv
  change deriv (halfDensityLift r v) t = _ at h
  rw [h]
  simp only [id_eq, mul_one]
  ring

theorem halfDensityLift_second_deriv (r : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (t : ℝ) :
    deriv (deriv (halfDensityLift r v)) t =
      Real.exp ((r / 2) * t) *
        (deriv (deriv v) t + r * deriv v t + r ^ 2 / 4 * v t) := by
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hvd' : Differentiable ℝ (deriv v) :=
    (hv.deriv' : ContDiff ℝ 1 (deriv v)).differentiable (by norm_num)
  have hfun : deriv (halfDensityLift r v) =
      (fun x => Real.exp ((r / 2) * x) * (deriv v x + r / 2 * v x)) :=
    funext (halfDensityLift_deriv r v hv)
  rw [hfun]
  have he := ((hasDerivAt_id t).const_mul (r / 2)).exp
  have h := (he.mul ((hvd' t).hasDerivAt.add
    ((hvd t).hasDerivAt.const_mul (r / 2)))).deriv
  change deriv (fun x => Real.exp ((r / 2) * x) *
    (deriv v x + r / 2 * v x)) t = _ at h
  rw [h]
  simp only [id_eq, mul_one, Pi.add_apply]
  ring

/-- Exact conjugation of the manuscript's original latitude expression.
It uses the same `M,b,lam0,r` and pole weight. -/
theorem halfDensityApply_lift (M : ℕ) (b lam0 r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (t : ℝ) :
    halfDensityApply M b lam0 r (halfDensityLift r v) t =
      Real.exp ((r / 2) * t) *
        (-(1 - t ^ 2) * deriv (deriv v) t +
          ((M : ℝ) * t - r * (1 - t ^ 2)) * deriv v t +
          (lam0 + b * r * t) * v t) := by
  unfold halfDensityApply
  rw [halfDensityLift_deriv r v hv, halfDensityLift_second_deriv r v hv]
  unfold halfDensityLift halfDensityPotential
  ring

theorem halfDensityLift_eigen (M : ℕ) (b lam0 r lam : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (heq : LatitudeEigenEquation M b lam0 r lam v)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    halfDensityApply M b lam0 r (halfDensityLift r v) t =
      lam * halfDensityLift r v t := by
  rw [halfDensityApply_lift M b lam0 r v hv t, heq t ht]
  unfold halfDensityLift
  ring

private theorem exp_half_sq (r t : ℝ) :
    (Real.exp ((r / 2) * t)) ^ 2 = Real.exp (r * t) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

private theorem weight_lift_sq (M : ℕ) (r : ℝ) (v : ℝ → ℝ) (t : ℝ) :
    radialWeight M 0 t * (halfDensityLift r v t) ^ 2 =
      radialWeight M r t * (v t) ^ 2 := by
  unfold halfDensityLift radialWeight
  rw [mul_pow, exp_half_sq]
  simp only [zero_mul, Real.exp_zero, one_mul]
  ring

private theorem flux_lift_sq (M : ℕ) (r : ℝ) (v : ℝ → ℝ) (t : ℝ) :
    latitudeFluxFactor M 0 t * (halfDensityLift r v t) ^ 2 =
      latitudeFluxFactor M r t * (v t) ^ 2 := by
  unfold halfDensityLift latitudeFluxFactor
  rw [mul_pow, exp_half_sq]
  simp only [zero_mul, Real.exp_zero, one_mul]
  ring

/-- The Hellmann--Feynman equality in the original weighted moments is
derived from the original ODE and its fixed-space parameter derivative
equation. The derivative eigenfunction is eliminated by the proved Green
identity, so the scalar derivative formula is not an input. -/
theorem latitude_HF_equality
    (M : ℕ) (hM : 2 ≤ M) (b lam0 r lam lamPrime : ℝ)
    (v g : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hg : ContDiff ℝ 2 g)
    (heq : LatitudeEigenEquation M b lam0 r lam v)
    (hden : latitudeNorm M r v ≠ 0)
    (hparameter : ∀ t ∈ Ioo (-1 : ℝ) 1,
      halfDensityApply M b lam0 r g t + halfDensityPotentialPrime M b r t *
        halfDensityLift r v t = lamPrime * halfDensityLift r v t + lam * g t) :
    lamPrime = r / 2 * latitudeW M r v +
      (b - (M : ℝ) / 2) * latitudeMean M r v := by
  have hm : 0 < M := by omega
  have hHF := halfDensity_HF_integral M hM b lam0 r lam lamPrime
    (halfDensityLift r v) g (halfDensityLift_smooth r v hv) hg
    (fun t ht => halfDensityLift_eigen M b lam0 r lam v hv heq ht) hparameter
  simp_rw [weight_lift_sq] at hHF
  have hsplit : (∫ t in (-1 : ℝ)..1,
      radialWeight M 0 t * halfDensityPotentialPrime M b r t *
        (halfDensityLift r v t) ^ 2) =
      r / 2 * (∫ t in (-1 : ℝ)..1, latitudeFluxFactor M r t * (v t) ^ 2) +
      (b - (M : ℝ) / 2) *
        (∫ t in (-1 : ℝ)..1, radialWeight M r t * t * (v t) ^ 2) := by
    have hcongr : (∫ t in (-1 : ℝ)..1,
        radialWeight M 0 t * halfDensityPotentialPrime M b r t *
          (halfDensityLift r v t) ^ 2) =
        ∫ t in (-1 : ℝ)..1, r / 2 * (latitudeFluxFactor M r t * (v t) ^ 2) +
          (b - (M : ℝ) / 2) * (radialWeight M r t * t * (v t) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htcc : t ∈ Icc (-1 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
      dsimp only [halfDensityPotentialPrime]
      rw [latitudeFluxFactor_eq_weight_Icc M hm r htcc]
      have hw := weight_lift_sq M r v t
      linear_combination (r / 2 * (1 - t ^ 2) + (b - (M : ℝ) / 2) * t) * hw
    rw [hcongr]
    have hA : IntervalIntegrable (fun t => latitudeFluxFactor M r t * (v t) ^ 2)
        volume (-1 : ℝ) 1 :=
      ((latitudeFluxFactor_continuous M r).mul (hv.continuous.pow 2)).intervalIntegrable _ _
    have hB : IntervalIntegrable (fun t => radialWeight M r t * t * (v t) ^ 2)
        volume (-1 : ℝ) 1 :=
      (((radialWeight_continuous_ge_two M hM r).mul continuous_id).mul
        (hv.continuous.pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (hA.const_mul (r / 2))
      (hB.const_mul (b - (M : ℝ) / 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit] at hHF
  unfold latitudeW latitudeMean
  field_simp [hden]
  unfold latitudeNorm
  linear_combination 2 * hHF

/-- For any source-aligned differentiable eigenpair, the actual scalar
derivative is positive. Existence and the full-sphere spectral identification
of that eigenpair are not hidden in this conditional theorem. -/
theorem latitude_eigenpair_parameter_derivative_pos
    (M : ℕ) (hM : 2 ≤ M) (b lam0 r lam lamPrime : ℝ)
    (hb : 0 < b) (hbhalf : 2 * b ≤ (M : ℝ)) (hr : 0 < r)
    (v g : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hg : ContDiff ℝ 2 g)
    (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t)
    (heq : LatitudeEigenEquation M b lam0 r lam v)
    (hparameter : ∀ t ∈ Ioo (-1 : ℝ) 1,
      halfDensityApply M b lam0 r g t + halfDensityPotentialPrime M b r t *
        halfDensityLift r v t = lamPrime * halfDensityLift r v t + lam * g t) :
    0 < lamPrime := by
  rw [latitude_HF_equality M hM b lam0 r lam lamPrime v g hv hg heq
    (ne_of_gt (latitudeNorm_pos M hM r v hv.continuous hpos)) hparameter]
  exact positive_eigenfunction_HF_rate_pos M hM b lam0 r lam hb hbhalf hr v hv hpos heq

end

end DFL.Spectral
