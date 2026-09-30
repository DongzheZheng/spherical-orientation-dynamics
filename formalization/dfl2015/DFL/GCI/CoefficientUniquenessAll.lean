import DFL.GCI.AngularMomentAll

/-!
# Coefficient uniqueness for represented original GCI weak solutions

This uses only symmetry of the original angular bilinear form and the
already proved exact weak moment identity.  It does not assert existence of
a solution or positivity of its numerator in dimensions above two.
-/

namespace DFL.GCI

noncomputable section

theorem originalWeakForm_symm
    (n : ℕ) (r : ℝ) (s t : AngularState) :
    originalWeakForm n r s t = originalWeakForm n r t s := by
  unfold originalWeakForm
  apply intervalIntegral.integral_congr
  intro θ _
  ring

/-- Any two original represented weak solutions have the same physical
coefficient denominator.  Each weak solution is tested against the other;
no function-level uniqueness or coercivity theorem is needed. -/
theorem weak_solution_denominator_unique_all
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ)
    (s t : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (ht : OriginalWeakGCISolution n r t) :
    originalGCIDenominator n r s = originalGCIDenominator n r t := by
  calc
    originalGCIDenominator n r s = originalSourcePairing n r s :=
      (originalSourcePairing_eq_denominator n hn r s).symm
    _ = originalWeakForm n r t s := (ht.2 s hs.1).2.2.symm
    _ = originalWeakForm n r s t := originalWeakForm_symm n r t s
    _ = originalSourcePairing n r t := (hs.2 t ht.1).2.2
    _ = originalGCIDenominator n r t :=
      originalSourcePairing_eq_denominator n hn r t

/-- At nonzero field, the exact original sine-test moment then forces
equality of the physical coefficient numerators. -/
theorem weak_solution_numerator_unique_all
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : r ≠ 0)
    (s t : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (ht : OriginalWeakGCISolution n r t) :
    originalGCINumerator n r s = originalGCINumerator n r t := by
  have hD := weak_solution_denominator_unique_all n hn r s t hs ht
  have hMs := weak_solution_moment_identity_all n hn r s hs
  have hMt := weak_solution_moment_identity_all n hn r t ht
  have hmul : r * originalGCINumerator n r s =
      r * originalGCINumerator n r t := by
    rw [hD] at hMs
    linarith
  exact (mul_left_cancel₀ hr hmul)

/-- The original represented weak GCI coefficient is independent of
which weak solution is chosen in every ambient dimension `n≥2` at
positive concentration. -/
theorem weak_solution_coefficient_unique_all
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r)
    (s t : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (ht : OriginalWeakGCISolution n r t) :
    originalGCICoefficient n r s = originalGCICoefficient n r t := by
  unfold originalGCICoefficient
  rw [weak_solution_numerator_unique_all n hn r hr.ne' s t hs ht,
    weak_solution_denominator_unique_all n hn r s t hs ht]

end

end DFL.GCI
