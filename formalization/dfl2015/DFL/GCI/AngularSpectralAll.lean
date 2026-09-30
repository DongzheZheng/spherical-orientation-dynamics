import DFL.GCI.SingularCotangentIBP
import DFL.GCI.EnergyDomainIntegrability
import DFL.GCI.AngularMassCauchyAll

/-!
# Strict original angular form comparison in ambient dimensions at least three

The represented source domain has both `u'` and `u / sin` in `L²`,
where `u = sin^((n-2)/2) g`. The positive angular ground profile
`sin θ exp[-r cos θ/(n+1)]` gives a square completion. Singular endpoint
cancellation is proved in `SingularCotangentIBP`, rather than assumed.

This is the manuscript's existing positive-function transform:
`spectral.tex`, equation `spec:ground-transform-identity`, with
`M = n + 1`, `b = 1`, `λ₀ = n - 1`; equivalently
`gci_applications.tex`, equation `gci:first-positive-function`, with the
manuscript sphere dimension `d = n - 1`. The two elementary weak
integration-by-parts identities supply the original-domain endpoint
justification for that same transform. Numerator positivity at the end
is an algebraic consequence of this form comparison, the original weak
moment, and forcing Cauchy; it does not formalize the manuscript's
separate half-sphere reflection proof of the same sign.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def groundSquareDensity (n : ℕ) (r : ℝ) (s : AngularState) (θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) *
    (s.scaledDerivative θ - ((n : ℝ) / 2) * Real.cos θ * singularRepresentative s θ -
      (r / ((n : ℝ) + 1)) * Real.sin θ * momentPrimitive s θ) ^ 2

theorem momentPrimitive_deriv_ae
    (n : ℕ) (s : AngularState) (hs : AngularEnergyDomain n s) :
    deriv (momentPrimitive s) =ᵐ[angularIntervalMeasure] s.scaledDerivative := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) Real.pi := by simp [Real.pi_pos.le]
  filter_upwards [ae_restrict_of_ae hs.1.ae_hasDerivAt_integral,
    moment_ae_interior] with θ hd hθ
  have hθ' : θ ∈ Set.uIcc (0 : ℝ) Real.pi := by
    rw [Set.uIcc_of_le Real.pi_pos.le]
    exact ⟨hθ.1.le, hθ.2.le⟩
  exact (hd hθ' 0 h0).deriv

theorem momentPrimitive_deriv_sq_integrable
    (n : ℕ) (s : AngularState) (hs : AngularEnergyDomain n s) :
    IntervalIntegrable (fun θ => (deriv (momentPrimitive s) θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
  apply hs.2.1.congr_ae
  filter_upwards [momentPrimitive_deriv_ae n s hs] with θ hd
  rw [hd]

theorem singularRepresentative_sq_integrable
    (n : ℕ) (hn : 3 ≤ n) (s : AngularState) (hs : AngularEnergyDomain n s) :
    IntervalIntegrable (fun θ => (singularRepresentative s θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
  have hm := singularRepresentative_memLp_two n hn s hs
  exact intervalIntegrable_iff.mpr ((memLp_two_iff_integrable_sq hm.1).1 hm)

theorem groundSquareDensity_integrable
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    IntervalIntegrable (groundSquareDensity n r s) volume (0 : ℝ) Real.pi := by
  let a : ℝ := (n : ℝ) / 2
  let k : ℝ := r / ((n : ℝ) + 1)
  have hucont := momentPrimitive_continuousOn n s hs
  have hu2 : IntervalIntegrable (fun θ => (momentPrimitive s θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    (hucont.pow 2).intervalIntegrable_of_Icc Real.pi_pos.le
  have hy2 := singularRepresentative_sq_integrable n hn s hs
  have hbase := ((hs.2.1.add (hy2.const_mul (a ^ 2))).add
    (hu2.const_mul (k ^ 2))).const_mul 3
  have hw : Continuous (fun θ : ℝ => Real.exp (r * Real.cos θ)) := by fun_prop
  have hbound := hbase.continuousOn_mul hw.continuousOn
  have hq := scaledDerivative_memLp_two n s hs
  have hy := singularRepresentative_memLp_two n hn s hs
  have hqMeas := hq.1
  have hyMeas := hy.1
  have hcosMeas := Real.continuous_cos.aestronglyMeasurable
    (μ := angularIntervalMeasure)
  have hsinMeas := Real.continuous_sin.aestronglyMeasurable
    (μ := angularIntervalMeasure)
  have hexpMeas := hw.aestronglyMeasurable (μ := angularIntervalMeasure)
  have huMeas : AEStronglyMeasurable (momentPrimitive s) angularIntervalMeasure :=
    (hucont.mono (by
      intro θ hθ
      rw [Set.uIoc_of_le Real.pi_pos.le] at hθ
      exact ⟨hθ.1.le, hθ.2⟩)).aestronglyMeasurable measurableSet_uIoc
  have hMeas : AEStronglyMeasurable (groundSquareDensity n r s) angularIntervalMeasure := by
    unfold groundSquareDensity
    fun_prop
  apply hbound.mono_fun' hMeas
  filter_upwards [moment_ae_interior] with θ _
  have hc : (Real.cos θ) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hsin : (Real.sin θ) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  let q := s.scaledDerivative θ
  let y := singularRepresentative s θ
  let u := momentPrimitive s θ
  let A := a * Real.cos θ * y
  let B := k * Real.sin θ * u
  have hA : A ^ 2 ≤ a ^ 2 * y ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg a) (sq_nonneg y))
    dsimp [A]
    nlinarith
  have hB : B ^ 2 ≤ k ^ 2 * u ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hsin (mul_nonneg (sq_nonneg k) (sq_nonneg u))
    dsimp [B]
    nlinarith
  have hsq : (q - A - B) ^ 2 ≤ 3 * ((q ^ 2 + a ^ 2 * y ^ 2) + k ^ 2 * u ^ 2) := by
    nlinarith [sq_nonneg (q + A), sq_nonneg (q + B), sq_nonneg (A - B)]
  have hp := Real.exp_nonneg (r * Real.cos θ)
  have hmul := mul_le_mul_of_nonneg_left hsq hp
  dsimp [groundSquareDensity]
  rw [abs_of_nonneg (mul_nonneg hp (sq_nonneg _))]
  simpa only [q, A, B, a, k, y, u, mul_comm] using hmul

/-- The source quadratic form equals a nonnegative square, its zero-field
baseline, and a strictly positive field correction. Every term is finite
on the original represented domain, including both singular endpoints. -/
theorem original_form_ground_square_identity
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    originalWeakForm n r s s =
      (∫ θ in (0 : ℝ)..Real.pi, groundSquareDensity n r s θ) +
      ((n : ℝ) - 1) * (∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) * (momentPrimitive s θ) ^ 2) +
      ((n : ℝ) * r ^ 2 / ((n : ℝ) + 1) ^ 2) *
        (∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2 * (momentPrimitive s θ) ^ 2) := by
  let u := momentPrimitive s
  let k : ℝ := r / ((n : ℝ) + 1)
  let γ : ℝ := (n : ℝ) * r ^ 2 / ((n : ℝ) + 1) ^ 2
  have huAC := momentPrimitive_AC n s hs
  have hu0 : u 0 = 0 := by simp [u, momentPrimitive]
  have huπ : u Real.pi = 0 := hs.2.2.2.1
  have hc := singular_cotangent_ibp r u huAC hu0 huπ
    (momentPrimitive_deriv_sq_integrable n s hs)
    (singularRepresentative_sq_integrable n hn s hs)
  have ht := smooth_sine_ibp r u huAC hu0 huπ
  have hQ := groundSquareDensity_integrable n hn r s hs
  have hucont := momentPrimitive_continuousOn n s hs
  have hM : IntervalIntegrable (fun θ => Real.exp (r * Real.cos θ) * (u θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    ((by fun_prop : Continuous (fun θ : ℝ => Real.exp (r * Real.cos θ))).continuousOn.mul
      (hucont.pow 2)).intervalIntegrable_of_Icc Real.pi_pos.le
  have hR : IntervalIntegrable
      (fun θ => Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2 * (u θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    ((by fun_prop : Continuous
      (fun θ : ℝ => Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2)).continuousOn.mul
      (hucont.pow 2)).intervalIntegrable_of_Icc Real.pi_pos.le
  have hd : formIntegrand n r s s =ᵐ[angularIntervalMeasure]
      (fun θ => ((groundSquareDensity n r s θ +
        ((n : ℝ) - 1) * (Real.exp (r * Real.cos θ) * (u θ) ^ 2)) +
        γ * (Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2 * (u θ) ^ 2)) +
        singularCotangentDensity r u θ + k * smoothSineDensity r u θ) := by
    filter_upwards [moment_ae_interior, momentPrimitive_deriv_ae n s hs] with θ hθ hdu
    rw [formIntegrand_scaled_density n s s hs hs r θ hθ]
    have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_mem_Ioo hθ).ne'
    have hnr : (n : ℝ) + 1 ≠ 0 := by positivity
    dsimp [groundSquareDensity, singularCotangentDensity, smoothSineDensity, γ, k, u]
    rw [hdu]
    unfold singularRepresentative halfPower
    field_simp [hsin, hnr]
    linear_combination
      -4 * ((n : ℝ) - 1) * (momentPrimitive s θ) ^ 2 *
        ((n : ℝ) + 1) ^ 2 * (Real.sin_sq_add_cos_sq θ)
  calc
    originalWeakForm n r s s =
        ∫ θ in (0 : ℝ)..Real.pi,
          (((groundSquareDensity n r s θ +
            ((n : ℝ) - 1) * (Real.exp (r * Real.cos θ) * (u θ) ^ 2)) +
            γ * (Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2 * (u θ) ^ 2)) +
            singularCotangentDensity r u θ) + k * smoothSineDensity r u θ := by
      exact intervalIntegral.integral_congr_ae_restrict hd
    _ = _ := by
      rw [intervalIntegral.integral_add
        (((hQ.add (hM.const_mul ((n : ℝ) - 1))).add (hR.const_mul γ)).add hc.1)
        (ht.1.const_mul k),
        intervalIntegral.integral_add
          ((hQ.add (hM.const_mul ((n : ℝ) - 1))).add (hR.const_mul γ)) hc.1,
        intervalIntegral.integral_add
          (hQ.add (hM.const_mul ((n : ℝ) - 1))) (hR.const_mul γ),
        intervalIntegral.integral_add hQ (hM.const_mul ((n : ℝ) - 1)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hc.2, ht.2]
      simp only [mul_zero, add_zero]
      rfl

/-- The strict form comparison holds for every nonzero representative in
the full original represented domain. Nonzero is stated on the interior,
where the original angular function is determined by its representative. -/
theorem energyDomain_strict_spectral_gap_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : AngularEnergyDomain n s)
    (hne : ∃ θ ∈ Set.Ioo (0 : ℝ) Real.pi, momentPrimitive s θ ≠ 0) :
    ((n : ℝ) - 1) * originalWeightedMass r s < originalWeakForm n r s s := by
  have hidentity := original_form_ground_square_identity n hn r s hs
  have hQnonneg : 0 ≤ ∫ θ in (0 : ℝ)..Real.pi, groundSquareDensity n r s θ := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro θ _
    unfold groundSquareDensity
    positivity
  have hRcont : ContinuousOn
      (fun θ => Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2 *
        (momentPrimitive s θ) ^ 2) (Set.Icc (0 : ℝ) Real.pi) :=
    (by fun_prop : Continuous
      (fun θ : ℝ => Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2)).continuousOn.mul
        ((momentPrimitive_continuousOn n s hs).pow 2)
  have hRpos : 0 < ∫ θ in (0 : ℝ)..Real.pi,
      Real.exp (r * Real.cos θ) * (Real.sin θ) ^ 2 *
        (momentPrimitive s θ) ^ 2 := by
    apply intervalIntegral.integral_pos Real.pi_pos hRcont
    · intro θ _
      positivity
    · obtain ⟨θ, hθ, hu⟩ := hne
      refine ⟨θ, ⟨hθ.1.le, hθ.2.le⟩, ?_⟩
      have hsine := Real.sin_pos_of_mem_Ioo hθ
      exact mul_pos (mul_pos (Real.exp_pos _) (sq_pos_of_pos hsine)) (sq_pos_of_ne_zero hu)
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : 0 < (n : ℝ) * r ^ 2 / ((n : ℝ) + 1) ^ 2 := by positivity
  have hcorrection := mul_pos hγ hRpos
  unfold originalWeightedMass
  linarith

/-- Every original represented weak GCI solution has a strict first-mode
form gap at positive field, in every ambient dimension at least three. -/
theorem weak_solution_strict_spectral_gap_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    ((n : ℝ) - 1) * originalWeightedMass r s < originalWeakForm n r s s :=
  energyDomain_strict_spectral_gap_ge_three n hn r hr s hs.1
    (weak_solution_primitive_nonzero_interior n (by omega) r s hs)

/-- The strictly positive original hydrodynamic numerator, without a
spectral premise or an assumed sign of the weak solution. -/
theorem weak_solution_numerator_pos_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    0 < originalGCINumerator n r s :=
  weak_solution_numerator_pos_of_strict_spectral_gap n (by omega) r hr s hs
    (weak_solution_strict_spectral_gap_ge_three n hn r hr s hs)

/-- The positive lower half of the original comparison for every
represented source weak solution in every ambient dimension at least three. -/
theorem original_GCI_positive_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    0 < originalGCICoefficient n r s :=
  div_pos (weak_solution_numerator_pos_ge_three n hn r hr s hs)
    (weak_solution_denominator_pos n (by omega) r s hs)

theorem original_GCI_positive_strict_upper_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (hr : 0 < r) (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    0 < originalGCICoefficient n r s ∧
      originalGCICoefficient n r s < DFL.orientationMean n r :=
  ⟨original_GCI_positive_ge_three n hn r hr s hs,
    original_GCI_strict_upper_all n (by omega) r hr s hs⟩

end

end DFL.GCI
