import DFL.Spectral.GroundFlux

/-!
# Exact positive-eigenfunction moments behind the spectral derivative

The moments are integrals of the manuscript's actual positive latitude
eigenfunction. Their signs and the pole-flux identity are proved rather
than imposed. The final Hellmann--Feynman rate is positive when `0<b≤M/2`.
Existence of the original full-sphere ground state and the theorem that
this rate is its spectral derivative remain independent obligations.
-/

namespace DFL.Spectral

open Set MeasureTheory
open scoped Interval

noncomputable section

theorem radialWeight_continuous_ge_two (M : ℕ) (hM : 2 ≤ M) (r : ℝ) :
    Continuous (radialWeight M r) := by
  have hm : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  unfold radialWeight
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    ((continuous_const.sub (continuous_id.pow 2)).rpow_const
      (fun _ => Or.inr (by linarith)))

theorem radialWeight_nonneg_Icc (M : ℕ) (r : ℝ) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : 0 ≤ radialWeight M r t := by
  have hw : 0 ≤ 1 - t ^ 2 := by
    rcases ht with ⟨hl, hr⟩
    nlinarith
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hw _)

def latitudeNorm (M : ℕ) (r : ℝ) (v : ℝ → ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, radialWeight M r t * (v t) ^ 2

def latitudeW (M : ℕ) (r : ℝ) (v : ℝ → ℝ) : ℝ :=
  (∫ t in (-1 : ℝ)..1, latitudeFluxFactor M r t * (v t) ^ 2) /
    latitudeNorm M r v

def latitudeMean (M : ℕ) (r : ℝ) (v : ℝ → ℝ) : ℝ :=
  (∫ t in (-1 : ℝ)..1, radialWeight M r t * t * (v t) ^ 2) /
    latitudeNorm M r v

def latitudeK (M : ℕ) (r : ℝ) (v : ℝ → ℝ) : ℝ :=
  (∫ t in (-1 : ℝ)..1, -latitudeFluxFactor M r t * v t * deriv v t) /
    latitudeNorm M r v

theorem latitudeNorm_pos (M : ℕ) (hM : 2 ≤ M) (r : ℝ) (v : ℝ → ℝ)
    (hv : Continuous v) (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t) :
    0 < latitudeNorm M r v := by
  apply intervalIntegral.integral_pos (by norm_num)
    ((radialWeight_continuous_ge_two M hM r).mul (hv.pow 2)).continuousOn
  · intro t ht
    exact mul_nonneg (radialWeight_nonneg_Icc M r ⟨ht.1.le, ht.2⟩) (sq_nonneg _)
  · refine ⟨0, by norm_num, ?_⟩
    exact mul_pos (radialWeight_pos M r (by norm_num))
      (sq_pos_of_pos (hpos 0 (by norm_num)))

theorem latitudeW_pos (M : ℕ) (hM : 2 ≤ M) (r : ℝ) (v : ℝ → ℝ)
    (hv : Continuous v) (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t) :
    0 < latitudeW M r v := by
  apply div_pos _ (latitudeNorm_pos M hM r v hv hpos)
  apply intervalIntegral.integral_pos (by norm_num)
    ((latitudeFluxFactor_continuous M r).mul (hv.pow 2)).continuousOn
  · intro t ht
    have hw : 0 ≤ 1 - t ^ 2 := by
      rcases ht with ⟨hl, hr⟩
      nlinarith
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hw _))
      (sq_nonneg _)
  · refine ⟨0, by norm_num, ?_⟩
    exact mul_pos (latitudeFluxFactor_pos M r (by norm_num))
      (sq_pos_of_pos (hpos 0 (by norm_num)))

theorem latitudeK_pos_of_positive_eigenfunction
    (M : ℕ) (hM : 2 ≤ M) (b lam0 r lam : ℝ) (hbr : 0 < b * r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t)
    (heq : LatitudeEigenEquation M b lam0 r lam v) :
    0 < latitudeK M r v := by
  have hm : 0 < M := by omega
  have hd : Continuous (deriv v) := (hv.deriv' : ContDiff ℝ 1 (deriv v)).continuous
  apply div_pos _ (latitudeNorm_pos M hM r v hv.continuous hpos)
  apply intervalIntegral.integral_pos (by norm_num)
    ((((latitudeFluxFactor_continuous M r).neg).mul hv.continuous).mul hd).continuousOn
  · intro t ht
    by_cases ht1 : t = 1
    · simp [ht1, latitudeFluxFactor_right M hm r]
    · have hti : t ∈ Ioo (-1 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
      exact (mul_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos (neg_neg_of_pos (latitudeFluxFactor_pos M r hti)) (hpos t hti))
        (positive_latitude_eigenfunction_deriv_neg M hm b lam0 r lam hbr v hv hpos heq hti)).le
  · refine ⟨0, by norm_num, ?_⟩
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos (neg_neg_of_pos (latitudeFluxFactor_pos M r (by norm_num)))
        (hpos 0 (by norm_num)))
      (positive_latitude_eigenfunction_deriv_neg M hm b lam0 r lam hbr v hv hpos heq (by norm_num))

/-- The exact both-pole moment identity, valid for every smooth latitude
function with nonzero normalization. -/
theorem latitude_weight_flux_identity
    (M : ℕ) (hM : 2 ≤ M) (r : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hden : latitudeNorm M r v ≠ 0) :
    r * latitudeW M r v - (M : ℝ) * latitudeMean M r v -
      2 * latitudeK M r v = 0 := by
  have hm : 0 < M := by omega
  have hd : Continuous (deriv v) := (hv.deriv' : ContDiff ℝ 1 (deriv v)).continuous
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  let A : ℝ → ℝ := fun t => latitudeFluxFactor M r t * (v t) ^ 2
  let B : ℝ → ℝ := fun t => radialWeight M r t * t * (v t) ^ 2
  let C : ℝ → ℝ := fun t => -latitudeFluxFactor M r t * v t * deriv v t
  have hA : Continuous A := (latitudeFluxFactor_continuous M r).mul (hv.continuous.pow 2)
  have hB : Continuous B := ((radialWeight_continuous_ge_two M hM r).mul
    continuous_id).mul (hv.continuous.pow 2)
  have hC : Continuous C := (((latitudeFluxFactor_continuous M r).neg).mul
    hv.continuous).mul hd
  have hderiv : ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt A (r * A t - (M : ℝ) * B t - 2 * C t) t := by
    intro t ht
    convert (latitudeFluxFactor_hasDerivAt M r ht).mul ((hvd t).hasDerivAt.pow 2) using 1
    dsimp [A, B, C]
    rw [latitudeFluxFactor_eq_weight M r ht]
    ring
  have hint : IntervalIntegrable
      (fun t => r * A t - (M : ℝ) * B t - 2 * C t) volume (-1 : ℝ) 1 :=
    (((continuous_const.mul hA).sub (continuous_const.mul hB)).sub
      (continuous_const.mul hC)).intervalIntegrable _ _
  have htotal := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1 : ℝ) ≤ 1) hA.continuousOn hderiv hint
  have haint := hA.intervalIntegrable (μ := volume) (-1 : ℝ) 1
  have hbint := hB.intervalIntegrable (μ := volume) (-1 : ℝ) 1
  have hcint := hC.intervalIntegrable (μ := volume) (-1 : ℝ) 1
  rw [intervalIntegral.integral_sub ((haint.const_mul r).sub (hbint.const_mul (M : ℝ)))
    (hcint.const_mul 2), intervalIntegral.integral_sub (haint.const_mul r)
    (hbint.const_mul (M : ℝ)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at htotal
  have hzero : r * (∫ t in (-1 : ℝ)..1, A t) -
      (M : ℝ) * (∫ t in (-1 : ℝ)..1, B t) - 2 * (∫ t in (-1 : ℝ)..1, C t) = 0 := by
    simpa [A, latitudeFluxFactor_left M hm r, latitudeFluxFactor_right M hm r] using htotal
  unfold latitudeW latitudeMean latitudeK
  dsimp [A, B, C] at hzero
  field_simp [hden]
  simpa only [neg_mul, mul_zero] using hzero

/-- The Hellmann--Feynman expression equals the positive flux expression
on these same normalized original-eigenfunction moments. -/
theorem latitude_HF_rate_eq_flux (M : ℕ) (hM : 2 ≤ M)
    (b r : ℝ) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hden : latitudeNorm M r v ≠ 0) :
    r / 2 * latitudeW M r v + (b - (M : ℝ) / 2) * latitudeMean M r v =
      (b * r * latitudeW M r v + ((M : ℝ) - 2 * b) * latitudeK M r v) / (M : ℝ) := by
  have hm : (M : ℝ) ≠ 0 := by
    have : 0 < M := by omega
    positivity
  have hflux := latitude_weight_flux_identity M hM r v hv hden
  apply (eq_div_iff hm).2
  linear_combination ((M : ℝ) / 2 - b) * hflux

/-- For the positive eigenfunction, the spectral derivative expression
is strictly positive in the parameter range covering all physical
angular modes and the radial partner for `d≥2`. -/
theorem positive_eigenfunction_HF_rate_pos
    (M : ℕ) (hM : 2 ≤ M) (b lam0 r lam : ℝ)
    (hb : 0 < b) (hbhalf : 2 * b ≤ (M : ℝ)) (hr : 0 < r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t)
    (heq : LatitudeEigenEquation M b lam0 r lam v) :
    0 < r / 2 * latitudeW M r v +
      (b - (M : ℝ) / 2) * latitudeMean M r v := by
  rw [latitude_HF_rate_eq_flux M hM b r v hv
    (ne_of_gt (latitudeNorm_pos M hM r v hv.continuous hpos))]
  have hW := latitudeW_pos M hM r v hv.continuous hpos
  have hK := latitudeK_pos_of_positive_eigenfunction M hM b lam0 r lam
    (mul_pos hb hr) v hv hpos heq
  apply div_pos
  · exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos hb hr) hW)
      (mul_nonneg (by linarith) hK.le)
  · have : 0 < M := by omega
    positivity

end

end DFL.Spectral
