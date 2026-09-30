import Mathlib

/-!
# Strict response from a nonnegative quadratic energy

This elementary polarization lemma isolates the strictness step in a weak
Poisson problem: if the energy is nonnegative for every perturbation and
the forcing detects one test state, the solution's energy cannot vanish.
An application to the original DFL GCI weak space must still prove that its
test space is linear and that its form has the displayed expansion.
-/

namespace DFL.Probability

private theorem linear_coefficient_zero_of_nonnegative_quadratic
    (b c : ℝ) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * c) : b = 0 := by
  have hc1 : 0 < c + 1 := by linarith
  have hc1ne : c + 1 ≠ 0 := ne_of_gt hc1
  have htest := h (-2 * b / (c + 1))
  have hident :
      2 * (-2 * b / (c + 1)) * b +
        (-2 * b / (c + 1)) ^ 2 * c =
      -(4 * b ^ 2) / (c + 1) ^ 2 := by
    field_simp
    ring
  rw [hident] at htest
  have hden : 0 < (c + 1) ^ 2 := sq_pos_of_pos hc1
  have hnum : 0 ≤ -(4 * b ^ 2) := by
    have hscaled := (le_div_iff₀ hden).1 htest
    simpa using hscaled
  nlinarith [sq_nonneg b]

/-- A zero diagonal energy would make every forcing pairing vanish. Hence
any nonzero positive source pairing makes the response energy strictly
positive. -/
theorem energy_response_pos_of_positive_test
    {V : Type*} (energy : ℝ) (forcing testEnergy : V → ℝ)
    (henergy : 0 ≤ energy)
    (htestEnergy : ∀ v : V, 0 ≤ testEnergy v)
    (hperturb : ∀ v : V, ∀ t : ℝ,
      0 ≤ energy + 2 * t * forcing v + t ^ 2 * testEnergy v)
    (hsource : ∃ v : V, 0 < forcing v) :
    0 < energy := by
  by_contra hnot
  have hzero : energy = 0 := le_antisymm (le_of_not_gt hnot) henergy
  obtain ⟨v, hv⟩ := hsource
  have hquad : ∀ t : ℝ,
      0 ≤ 2 * t * forcing v + t ^ 2 * testEnergy v := by
    intro t
    simpa only [hzero, zero_add] using hperturb v t
  have hFzero := linear_coefficient_zero_of_nonnegative_quadratic
    (forcing v) (testEnergy v) (htestEnergy v) hquad
  linarith

end DFL.Probability
