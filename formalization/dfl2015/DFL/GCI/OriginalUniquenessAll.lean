import DFL.GCI.AngularSpectralAll

/-!
# Uniqueness in the original represented weak angular space

This follows the manuscript's uniqueness paragraph immediately after
`gci:first-positive-function`: subtract two original weak solutions and
test the homogeneous equation with their difference. The original
quadratic form controls the same Dirichlet representative, including
both singular endpoints. Equality concerns the original angular `g`
on `(0,π)` and its reconstructed scaled derivative almost everywhere;
arbitrary endpoint values of `g` are not identified.
-/

namespace DFL.GCI

open MeasureTheory Filter
open scoped Interval Topology

noncomputable section

private theorem originalWeakForm_stateSub_left
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (s v t : AngularState)
    (hs : AngularEnergyDomain n s) (hv : AngularEnergyDomain n v)
    (ht : AngularEnergyDomain n t) :
    originalWeakForm n r (stateSub s v) t =
      originalWeakForm n r s t - originalWeakForm n r v t := by
  unfold stateSub
  rw [originalWeakForm_stateAdd_left n hn r s (stateSMul (-1) v) t hs
      (stateSMul_mem_energy n v hv (-1)) ht,
    originalWeakForm_stateSMul_left]
  ring

theorem weak_solution_difference_self_energy_zero
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (s v : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (hv : OriginalWeakGCISolution n r v) :
    originalWeakForm n r (stateSub s v) (stateSub s v) = 0 := by
  have hz := stateSub_mem_energy n hn s v hs.1 hv.1
  rw [originalWeakForm_stateSub_left n hn r s v (stateSub s v) hs.1 hv.1 hz]
  rw [(hs.2 (stateSub s v) hz).2.2, (hv.2 (stateSub s v) hz).2.2]
  ring

/-- Vanishing original energy forces the original Dirichlet
representative to vanish pointwise in the open angular interval.
This holds at every real field, including zero. -/
theorem energyDomain_self_energy_zero_primitive_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (s : AngularState)
    (hs : AngularEnergyDomain n s) (hE : originalWeakForm n r s s = 0) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, momentPrimitive s θ = 0 := by
  intro θ hθ
  by_contra hu
  have hidentity := original_form_ground_square_identity n hn r s hs
  have hQnonneg : 0 ≤ ∫ x in (0 : ℝ)..Real.pi, groundSquareDensity n r s x := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro x _
    unfold groundSquareDensity
    positivity
  have hRnonneg : 0 ≤ ∫ x in (0 : ℝ)..Real.pi,
      Real.exp (r * Real.cos x) * (Real.sin x) ^ 2 * (momentPrimitive s x) ^ 2 := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro x _
    positivity
  have hMcont : ContinuousOn
      (fun x => Real.exp (r * Real.cos x) * (momentPrimitive s x) ^ 2)
      (Set.Icc (0 : ℝ) Real.pi) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (r * Real.cos x))).continuousOn.mul
      ((momentPrimitive_continuousOn n s hs).pow 2)
  have hMpos : 0 < ∫ x in (0 : ℝ)..Real.pi,
      Real.exp (r * Real.cos x) * (momentPrimitive s x) ^ 2 := by
    apply intervalIntegral.integral_pos Real.pi_pos hMcont
    · intro x _
      positivity
    · exact ⟨θ, ⟨hθ.1.le, hθ.2.le⟩,
        mul_pos (Real.exp_pos _) (sq_pos_of_ne_zero hu)⟩
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : 0 < ((n : ℝ) - 1) *
      (∫ x in (0 : ℝ)..Real.pi, Real.exp (r * Real.cos x) * (momentPrimitive s x) ^ 2) :=
    mul_pos (by linarith) hMpos
  have hγ : 0 ≤ (n : ℝ) * r ^ 2 / ((n : ℝ) + 1) ^ 2 := by positivity
  have hcorrection := mul_nonneg hγ hRnonneg
  rw [hE] at hidentity
  linarith

theorem weak_solution_difference_primitive_zero_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (s v : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (hv : OriginalWeakGCISolution n r v) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi,
      momentPrimitive (stateSub s v) θ = 0 :=
  energyDomain_self_energy_zero_primitive_ge_three n hn r (stateSub s v)
    (stateSub_mem_energy n (by omega) s v hs.1 hv.1)
    (weak_solution_difference_self_energy_zero n (by omega) r s v hs hv)

/-- Original angular uniqueness on the interior, with no concentration
sign restriction, regularity premise, or assumed solution sign. -/
theorem weak_solution_g_unique_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (s v : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (hv : OriginalWeakGCISolution n r v) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, s.g θ = v.g θ := by
  have hz := stateSub_mem_energy n (by omega) s v hs.1 hv.1
  have hzero := weak_solution_difference_primitive_zero_ge_three n hn r s v hs hv
  intro θ hθ
  have hrec := moment_reconstruction n (stateSub s v) hz θ ⟨hθ.1.le, hθ.2.le⟩
  rw [hzero θ hθ] at hrec
  have hp : Real.rpow (Real.sin θ) (halfPower n) ≠ 0 :=
    (Real.rpow_pos_of_pos (Real.sin_pos_of_mem_Ioo hθ) _).ne'
  have hm : Real.rpow (Real.sin θ) (halfPower n) * (s.g θ - v.g θ) = 0 := by
    simpa only [scaledFunction, stateSub, stateAdd, stateSMul, neg_one_mul,
      ← sub_eq_add_neg] using hrec
  have he : s.g θ - v.g θ = 0 := (mul_eq_zero.mp hm).resolve_left hp
  linarith

/-- The derivative field is also determined almost everywhere by the
original weak solution; it is not an independent unspecified variable. -/
theorem weak_solution_scaledDerivative_unique_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (s v : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (hv : OriginalWeakGCISolution n r v) :
    s.scaledDerivative =ᵐ[angularIntervalMeasure] v.scaledDerivative := by
  have hz := stateSub_mem_energy n (by omega) s v hs.1 hv.1
  have hzero := weak_solution_difference_primitive_zero_ge_three n hn r s v hs hv
  filter_upwards [moment_ae_interior, momentPrimitive_deriv_ae n (stateSub s v) hz]
    with θ hθ hdu
  have hlocal : momentPrimitive (stateSub s v) =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact hzero x hx
  have hder : deriv (momentPrimitive (stateSub s v)) θ = 0 :=
    ((hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq hlocal).deriv
  rw [hdu] at hder
  dsimp [stateSub, stateAdd, stateSMul] at hder
  linarith

theorem weak_solution_denominator_unique_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (s v : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (hv : OriginalWeakGCISolution n r v) :
    originalGCIDenominator n r s = originalGCIDenominator n r v := by
  unfold originalGCIDenominator
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [moment_ae_interior] with θ hθ
  rw [weak_solution_g_unique_ge_three n hn r s v hs hv θ hθ]

theorem weak_solution_numerator_unique_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (s v : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (hv : OriginalWeakGCISolution n r v) :
    originalGCINumerator n r s = originalGCINumerator n r v := by
  unfold originalGCINumerator
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [moment_ae_interior] with θ hθ
  rw [weak_solution_g_unique_ge_three n hn r s v hs hv θ hθ]

theorem weak_solution_coefficient_unique_ge_three
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) (s v : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (hv : OriginalWeakGCISolution n r v) :
    originalGCICoefficient n r s = originalGCICoefficient n r v := by
  unfold originalGCICoefficient
  rw [weak_solution_numerator_unique_ge_three n hn r s v hs hv,
    weak_solution_denominator_unique_ge_three n hn r s v hs hv]

end

end DFL.GCI
