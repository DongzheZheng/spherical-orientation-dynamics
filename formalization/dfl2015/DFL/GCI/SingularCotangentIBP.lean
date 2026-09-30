import DFL.GCI.AngularMomentAll

/-!
# Singular cotangent integration by parts on the represented angular domain

The singular multiplier is approached by `cos θ / (sin θ + ε)`.
The original extra domain condition supplies `(u / sin θ)² ∈ L¹`;
the derivative condition supplies `(u')² ∈ L¹`. Together they dominate
every regularized boundary calculation, so no endpoint smoothness or
pointwise trace rate is imposed on the weak representative.
-/

namespace DFL.GCI

open MeasureTheory Filter
open scoped Interval Topology

noncomputable section

def regularizedCotangent (ε θ : ℝ) : ℝ :=
  Real.cos θ / (Real.sin θ + ε)

def weightedCotangentDerivative (r ε θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) *
    (-r * Real.sin θ * Real.cos θ / (Real.sin θ + ε) -
      (1 + ε * Real.sin θ) / (Real.sin θ + ε) ^ 2)

private theorem regularizedCotangent_hasDerivAt
    (ε θ : ℝ) (hne : Real.sin θ + ε ≠ 0) :
    HasDerivAt (regularizedCotangent ε)
      (-(1 + ε * Real.sin θ) / (Real.sin θ + ε) ^ 2) θ := by
  have h := (Real.hasDerivAt_cos θ).div
    ((Real.hasDerivAt_sin θ).add_const ε) hne
  convert h using 1
  field_simp [hne]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem weighted_regularizedCotangent_hasDerivAt
    (r ε θ : ℝ) (hne : Real.sin θ + ε ≠ 0) :
    HasDerivAt
      (fun x => Real.exp (r * Real.cos x) * regularizedCotangent ε x)
      (weightedCotangentDerivative r ε θ) θ := by
  have he : HasDerivAt (fun x => Real.exp (r * Real.cos x))
      (-r * Real.sin θ * Real.exp (r * Real.cos θ)) θ := by
    convert ((Real.hasDerivAt_cos θ).const_mul r).exp using 1
    ring
  convert he.mul (regularizedCotangent_hasDerivAt ε θ hne) using 1
  unfold weightedCotangentDerivative regularizedCotangent
  ring

theorem weighted_regularizedCotangent_AC (r ε : ℝ) (hε : 0 < ε) :
    AbsolutelyContinuousOnInterval
      (fun x => Real.exp (r * Real.cos x) * regularizedCotangent ε x)
      (0 : ℝ) Real.pi := by
  have hne (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
      Real.sin θ + ε ≠ 0 := by
    have hs := Real.sin_nonneg_of_mem_Icc hθ
    positivity
  have hc : ContDiffOn ℝ 1
      (fun x => Real.exp (r * Real.cos x) * regularizedCotangent ε x)
      (Set.Icc (0 : ℝ) Real.pi) := by
    unfold regularizedCotangent
    apply ContDiffOn.mul (by fun_prop)
    exact Real.contDiff_cos.contDiffOn.div
      (by fun_prop) hne
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith (by norm_num)
    (convex_Icc (0 : ℝ) Real.pi) isCompact_Icc
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [Set.uIcc_of_le Real.pi_pos.le] using hK

theorem regularized_cotangent_ibp
    (r ε : ℝ) (hε : 0 < ε) (u : ℝ → ℝ)
    (hu : AbsolutelyContinuousOnInterval u (0 : ℝ) Real.pi)
    (hu0 : u 0 = 0) (huπ : u Real.pi = 0) :
    (∫ θ in (0 : ℝ)..Real.pi,
      (Real.exp (r * Real.cos θ) * regularizedCotangent ε θ) *
        deriv (fun x => u x ^ 2) θ) =
      -(∫ θ in (0 : ℝ)..Real.pi,
        weightedCotangentDerivative r ε θ * u θ ^ 2) := by
  have hu2 : AbsolutelyContinuousOnInterval (fun x => u x ^ 2)
      (0 : ℝ) Real.pi := by
    simpa only [pow_two] using hu.mul hu
  have hAC := weighted_regularizedCotangent_AC r ε hε
  have hIBP := hAC.integral_mul_deriv_eq_deriv_mul hu2
  simp only [hu0, huπ, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    sub_zero, zero_sub] at hIBP
  rw [hIBP]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [moment_ae_interior] with θ hθ
  have hne : Real.sin θ + ε ≠ 0 := by
    have hs := Real.sin_pos_of_mem_Ioo hθ
    positivity
  rw [(weighted_regularizedCotangent_hasDerivAt r ε θ hne).deriv]

private theorem cotangent_density_bound
    (r ε θ u v : ℝ) (hε : 0 ≤ ε)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    |2 * (Real.exp (r * Real.cos θ) * regularizedCotangent ε θ) * u * v +
      weightedCotangentDerivative r ε θ * u ^ 2| ≤
      Real.exp |r| * (v ^ 2 + (|r| + 3) * (u / Real.sin θ) ^ 2) := by
  let s := Real.sin θ
  let c := Real.cos θ
  let z := u / s
  let a := c * s / (s + ε)
  let b := s ^ 2 * (1 + ε * s) / (s + ε) ^ 2
  have hs : 0 < s := Real.sin_pos_of_mem_Ioo hθ
  have hs1 : s ≤ 1 := Real.sin_le_one θ
  have hc : |c| ≤ 1 := Real.abs_cos_le_one θ
  have hden : 0 < s + ε := by positivity
  have ha : |a| ≤ 1 := by
    dsimp [a]
    rw [abs_div, abs_mul, abs_of_pos hs, abs_of_pos hden]
    apply (div_le_one hden).2
    nlinarith [mul_le_mul_of_nonneg_right hc hs.le]
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]
    apply (div_le_one (sq_pos_of_pos hden)).2
    have hss : s ^ 2 ≤ 1 := by nlinarith
    have hs3 : s ^ 3 ≤ s := by nlinarith [mul_le_mul_of_nonneg_right hss hs.le]
    have he : ε * s ^ 3 ≤ ε * s := mul_le_mul_of_nonneg_left hs3 hε
    nlinarith [sq_nonneg ε]
  have huz : u = s * z := by dsimp [z]; field_simp
  have hp : 0 ≤ Real.exp (r * c) := Real.exp_nonneg _
  have hP : Real.exp (r * c) ≤ Real.exp |r| := by
    apply Real.exp_le_exp.mpr
    calc
      r * c ≤ |r * c| := le_abs_self _
      _ = |r| * |c| := abs_mul _ _
      _ ≤ |r| := by nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg r)]
  have hcross : |2 * a * z * v| ≤ z ^ 2 + v ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hav : |a| * |z| * |v| ≤ |z| * |v| := by
      nlinarith [mul_le_mul_of_nonneg_right ha (mul_nonneg (abs_nonneg z) (abs_nonneg v))]
    have hz2 := sq_abs z
    have hv2 := sq_abs v
    nlinarith [sq_nonneg (|z| - |v|)]
  have hpot : |(-r * a * s ^ 2 - b) * z ^ 2| ≤ (|r| + 1) * z ^ 2 := by
    have hars : |-r * a * s ^ 2| ≤ |r| := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg s)]
      have has : |a| * s ^ 2 ≤ 1 := by
        nlinarith [mul_le_mul_of_nonneg_right ha (sq_nonneg s)]
      nlinarith [mul_le_mul_of_nonneg_left has (abs_nonneg r)]
    rw [abs_mul, abs_of_nonneg (sq_nonneg z)]
    have hsub := abs_sub (-r * a * s ^ 2) b
    rw [abs_of_nonneg hb0] at hsub
    have hcoef : |-r * a * s ^ 2 - b| ≤ |r| + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg z)
  have halgebra :
      2 * (Real.exp (r * Real.cos θ) * regularizedCotangent ε θ) * u * v +
        weightedCotangentDerivative r ε θ * u ^ 2 =
      Real.exp (r * c) * (2 * a * z * v + (-r * a * s ^ 2 - b) * z ^ 2) := by
    rw [huz]
    dsimp [regularizedCotangent, weightedCotangentDerivative, a, b, s, c]
    field_simp
  rw [halgebra, abs_mul, abs_of_nonneg hp]
  have hsum := abs_add_le (2 * a * z * v) ((-r * a * s ^ 2 - b) * z ^ 2)
  have hsum' : |2 * a * z * v + (-r * a * s ^ 2 - b) * z ^ 2| ≤
      v ^ 2 + (|r| + 3) * z ^ 2 := by nlinarith [sq_nonneg z]
  exact (mul_le_mul_of_nonneg_left hsum' hp).trans
    (mul_le_mul_of_nonneg_right hP (by positivity))

def singularCotangentDensity (r : ℝ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) *
    (2 * (Real.cos θ / Real.sin θ) * u θ * deriv u θ -
      (r * Real.cos θ + 1 / (Real.sin θ) ^ 2) * (u θ) ^ 2)

/-- The singular cotangent boundary cancellation holds on the full
represented energy domain. The proof regularizes both endpoints and
uses precisely the original two square integrability conditions. -/
theorem singular_cotangent_ibp
    (r : ℝ) (u : ℝ → ℝ)
    (hu : AbsolutelyContinuousOnInterval u (0 : ℝ) Real.pi)
    (hu0 : u 0 = 0) (huπ : u Real.pi = 0)
    (hdu2 : IntervalIntegrable (fun θ => (deriv u θ) ^ 2)
      volume (0 : ℝ) Real.pi)
    (husing2 : IntervalIntegrable (fun θ => (u θ / Real.sin θ) ^ 2)
      volume (0 : ℝ) Real.pi) :
    IntervalIntegrable (singularCotangentDensity r u)
      volume (0 : ℝ) Real.pi ∧
      (∫ θ in (0 : ℝ)..Real.pi, singularCotangentDensity r u θ) = 0 := by
  let F (ε θ : ℝ) :=
    2 * (Real.exp (r * Real.cos θ) * regularizedCotangent ε θ) *
      u θ * deriv u θ + weightedCotangentDerivative r ε θ * (u θ) ^ 2
  let bound (θ : ℝ) := Real.exp |r| *
    ((deriv u θ) ^ 2 + (|r| + 3) * (u θ / Real.sin θ) ^ 2)
  have hbound : IntervalIntegrable bound volume (0 : ℝ) Real.pi :=
    (hdu2.add (husing2.const_mul (|r| + 3))).const_mul (Real.exp |r|)
  have hucont : ContinuousOn u (Set.Icc (0 : ℝ) Real.pi) := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hu.continuousOn
  have huMeas : AEStronglyMeasurable u
      (volume.restrict (Set.uIoc (0 : ℝ) Real.pi)) := by
    rw [Set.uIoc_of_le Real.pi_pos.le]
    exact (hucont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hduMeas := aestronglyMeasurable_deriv u
    (volume.restrict (Set.uIoc (0 : ℝ) Real.pi))
  have hFMeas (ε : ℝ) : AEStronglyMeasurable (F ε)
      (volume.restrict (Set.uIoc (0 : ℝ) Real.pi)) := by
    have hp : AEStronglyMeasurable (fun θ : ℝ => Real.exp (r * Real.cos θ))
        (volume.restrict (Set.uIoc (0 : ℝ) Real.pi)) :=
      (by fun_prop : Continuous (fun θ : ℝ => Real.exp (r * Real.cos θ))).aestronglyMeasurable
    have hs := Real.continuous_sin.aestronglyMeasurable
      (μ := volume.restrict (Set.uIoc (0 : ℝ) Real.pi))
    have hc := Real.continuous_cos.aestronglyMeasurable
      (μ := volume.restrict (Set.uIoc (0 : ℝ) Real.pi))
    dsimp [F, regularizedCotangent, weightedCotangentDerivative]
    fun_prop
  have hF0Bound : ∀ᵐ θ ∂volume.restrict (Set.uIoc (0 : ℝ) Real.pi),
      ‖F 0 θ‖ ≤ bound θ := by
    filter_upwards [moment_ae_interior] with θ hθ
    simpa only [F, bound, Real.norm_eq_abs] using
      cotangent_density_bound r 0 θ (u θ) (deriv u θ) (by norm_num) hθ
  have hF0Int : IntervalIntegrable (F 0) volume (0 : ℝ) Real.pi :=
    hbound.mono_fun' (hFMeas 0) hF0Bound
  have hregInt (ε : ℝ) (hε : 0 < ε) :
      IntervalIntegrable (F ε) volume (0 : ℝ) Real.pi := by
    apply hbound.mono_fun' (hFMeas ε)
    filter_upwards [moment_ae_interior] with θ hθ
    simpa only [F, bound, Real.norm_eq_abs] using
      cotangent_density_bound r ε θ (u θ) (deriv u θ) hε.le hθ
  have hregZero (ε : ℝ) (hε : 0 < ε) :
      (∫ θ in (0 : ℝ)..Real.pi, F ε θ) = 0 := by
    have hWcont : ContinuousOn
        (fun θ => Real.exp (r * Real.cos θ) * regularizedCotangent ε θ)
        (Set.Icc (0 : ℝ) Real.pi) := by
      simpa only [Set.uIcc_of_le Real.pi_pos.le] using
        (weighted_regularizedCotangent_AC r ε hε).continuousOn
    have hDcont : ContinuousOn (weightedCotangentDerivative r ε)
        (Set.Icc (0 : ℝ) Real.pi) := by
      have hne (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
          Real.sin θ + ε ≠ 0 := by
        have := Real.sin_nonneg_of_mem_Icc hθ
        positivity
      unfold weightedCotangentDerivative
      apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.sub
      · exact (by fun_prop : ContinuousOn
          (fun θ : ℝ => -r * Real.sin θ * Real.cos θ)
          (Set.Icc (0 : ℝ) Real.pi)).div (by fun_prop) hne
      · exact (by fun_prop : ContinuousOn (fun θ : ℝ => 1 + ε * Real.sin θ)
          (Set.Icc (0 : ℝ) Real.pi)).div (by fun_prop)
            (fun θ hθ => pow_ne_zero 2 (hne θ hθ))
    have hL : IntervalIntegrable
        (fun θ => 2 * (Real.exp (r * Real.cos θ) * regularizedCotangent ε θ) *
          u θ * deriv u θ) volume (0 : ℝ) Real.pi := by
      have hc : ContinuousOn
          (fun θ => 2 * (Real.exp (r * Real.cos θ) * regularizedCotangent ε θ) * u θ)
          (Set.uIcc (0 : ℝ) Real.pi) := by
        rw [Set.uIcc_of_le Real.pi_pos.le]
        exact (hWcont.const_mul 2).mul hucont
      simpa only [mul_comm] using hu.intervalIntegrable_deriv.continuousOn_mul hc
    have hR : IntervalIntegrable
        (fun θ => weightedCotangentDerivative r ε θ * (u θ) ^ 2)
        volume (0 : ℝ) Real.pi :=
      (hDcont.mul (hucont.pow 2)).intervalIntegrable_of_Icc Real.pi_pos.le
    have hIBP := regularized_cotangent_ibp r ε hε u hu hu0 huπ
    have hconvert :
        (∫ θ in (0 : ℝ)..Real.pi,
          (Real.exp (r * Real.cos θ) * regularizedCotangent ε θ) *
            deriv (fun x => u x ^ 2) θ) =
        ∫ θ in (0 : ℝ)..Real.pi,
          2 * (Real.exp (r * Real.cos θ) * regularizedCotangent ε θ) *
            u θ * deriv u θ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hu.ae_differentiableAt] with θ hθ hx
      have hx' : θ ∈ Set.uIcc (0 : ℝ) Real.pi := Set.uIoc_subset_uIcc hx
      have hpow : HasDerivAt (fun x => u x ^ 2)
          (2 * u θ * deriv u θ) θ := by
        convert (hθ hx').hasDerivAt.pow 2 using 1
        ring
      rw [hpow.deriv]
      ring
    rw [hconvert] at hIBP
    dsimp [F]
    rw [intervalIntegral.integral_add hL hR]
    linarith
  let eps (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have heps (k : ℕ) : 0 < eps k := by dsimp [eps]; positivity
  have hepslim : Tendsto eps atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hboundInt : Integrable bound
      (volume.restrict (Set.uIoc (0 : ℝ) Real.pi)) := by
    simpa only [Set.uIoc_of_le Real.pi_pos.le] using hbound.1
  have hdom := tendsto_integral_of_dominated_convergence bound
    (fun k => hFMeas (eps k)) hboundInt
    (fun k => by
      filter_upwards [moment_ae_interior] with θ hθ
      simpa only [F, bound, Real.norm_eq_abs] using
        cotangent_density_bound r (eps k) θ (u θ) (deriv u θ) (heps k).le hθ)
    (by
      filter_upwards [moment_ae_interior] with θ hθ
      have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_mem_Ioo hθ).ne'
      have hc : ContinuousAt (fun ε : ℝ => F ε θ) 0 := by
        dsimp [F, regularizedCotangent, weightedCotangentDerivative]
        fun_prop (disch := simpa using hs)
      exact hc.tendsto.comp hepslim)
  have hzero : (∫ θ in (0 : ℝ)..Real.pi, F 0 θ) = 0 := by
    have hz (k : ℕ) : (∫ θ in Set.uIoc (0 : ℝ) Real.pi, F (eps k) θ) = 0 := by
      rw [Set.uIoc_of_le Real.pi_pos.le]
      rw [← intervalIntegral.integral_of_le Real.pi_pos.le]
      exact hregZero (eps k) (heps k)
    have heq := tendsto_nhds_unique hdom
      (show Tendsto (fun k => ∫ θ in Set.uIoc (0 : ℝ) Real.pi, F (eps k) θ)
        atTop (𝓝 (0 : ℝ)) by simpa only [hz] using tendsto_const_nhds)
    simpa only [Set.uIoc_of_le Real.pi_pos.le,
      intervalIntegral.integral_of_le Real.pi_pos.le] using heq
  have heq : F 0 =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) Real.pi)]
      singularCotangentDensity r u := by
    filter_upwards [moment_ae_interior] with θ hθ
    have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_mem_Ioo hθ).ne'
    dsimp [F, regularizedCotangent, weightedCotangentDerivative, singularCotangentDensity]
    simp only [add_zero, zero_mul, add_zero]
    field_simp [hs]
    ring
  exact ⟨hF0Int.congr_ae heq,
    (intervalIntegral.integral_congr_ae_restrict heq).symm.trans hzero⟩

def smoothSineDensity (r : ℝ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) *
    (2 * Real.sin θ * u θ * deriv u θ +
      (Real.cos θ - r * (Real.sin θ) ^ 2) * (u θ) ^ 2)

theorem smooth_sine_ibp
    (r : ℝ) (u : ℝ → ℝ)
    (hu : AbsolutelyContinuousOnInterval u (0 : ℝ) Real.pi)
    (hu0 : u 0 = 0) (huπ : u Real.pi = 0) :
    IntervalIntegrable (smoothSineDensity r u)
      volume (0 : ℝ) Real.pi ∧
      (∫ θ in (0 : ℝ)..Real.pi, smoothSineDensity r u θ) = 0 := by
  let W (θ : ℝ) := Real.exp (r * Real.cos θ) * Real.sin θ
  have hW : ContDiff ℝ 1 W := by dsimp [W]; fun_prop
  obtain ⟨K, hK⟩ := hW.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_Icc (0 : ℝ) Real.pi) isCompact_Icc
  have hWAC : AbsolutelyContinuousOnInterval W (0 : ℝ) Real.pi := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hK
  have hu2 : AbsolutelyContinuousOnInterval (fun x => u x ^ 2)
      (0 : ℝ) Real.pi := by simpa only [pow_two] using hu.mul hu
  have hprod : AbsolutelyContinuousOnInterval
      (fun θ => W θ * u θ ^ 2) (0 : ℝ) Real.pi := hWAC.mul hu2
  have heq : deriv (fun θ => W θ * u θ ^ 2) =ᵐ[
      volume.restrict (Set.uIoc (0 : ℝ) Real.pi)] smoothSineDensity r u := by
    filter_upwards [ae_restrict_of_ae hu.ae_differentiableAt, moment_ae_interior]
      with θ hθ hx
    have hx' : θ ∈ Set.uIcc (0 : ℝ) Real.pi := by
      rw [Set.uIcc_of_le Real.pi_pos.le]
      exact ⟨hx.1.le, hx.2.le⟩
    have hwder : HasDerivAt W
        (Real.exp (r * Real.cos θ) * (Real.cos θ - r * (Real.sin θ) ^ 2)) θ := by
      dsimp [W]
      convert (((Real.hasDerivAt_cos θ).const_mul r).exp).mul
        (Real.hasDerivAt_sin θ) using 1
      ring
    have hu2der : HasDerivAt (fun x => u x ^ 2)
        (2 * u θ * deriv u θ) θ := by
      convert (hθ hx').hasDerivAt.pow 2 using 1
      ring
    have hd : deriv (fun θ => W θ * u θ ^ 2) θ =
        (Real.exp (r * Real.cos θ) * (Real.cos θ - r * (Real.sin θ) ^ 2)) *
          (u θ) ^ 2 + W θ * (2 * u θ * deriv u θ) :=
      (hwder.mul hu2der).deriv
    rw [hd]
    dsimp [W, smoothSineDensity]
    ring
  have hi := hprod.intervalIntegrable_deriv.congr_ae heq
  have he : (∫ θ in (0 : ℝ)..Real.pi,
      deriv (fun x => W x * u x ^ 2) θ) = 0 := by
    rw [hprod.integral_deriv_eq_sub, hu0, huπ]
    ring
  exact ⟨hi, (intervalIntegral.integral_congr_ae_restrict heq).symm.trans he⟩

end

end DFL.GCI
