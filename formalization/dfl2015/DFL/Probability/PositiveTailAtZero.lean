import Mathlib

/-!
# The zero-threshold tail from strictly positive tails

For any two Borel measures on the real line, agreement of all strictly
positive upper tails implies agreement of the upper tail at zero.  This
is the monotone-union step needed for the genuine sphere coordinate law.
-/

namespace DFL.Probability

open MeasureTheory

private def positiveTailApproximants (n : ℕ) : Set ℝ :=
  Set.Ioi (1 / ((n : ℝ) + 2))

private theorem positiveTailApproximants_mono :
    Monotone positiveTailApproximants := by
  intro n m hnm
  apply Set.Ioi_subset_Ioi
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hnm 2

private theorem positiveTailApproximants_iUnion :
    (⋃ n : ℕ, positiveTailApproximants n) = Set.Ioi (0 : ℝ) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioi, positiveTailApproximants]
  constructor
  · rintro ⟨n, hn⟩
    have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 2) := by positivity
    exact lt_trans hpos hn
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
    refine ⟨n, ?_⟩
    have hle : (1 : ℝ) / ((n : ℝ) + 2) ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact lt_of_le_of_lt hle hn

/-- Agreement on upper tails at every `0 < t < 1` also gives agreement
at the previously missing threshold `t = 0`. No density, atomlessness,
or finite-mass hypothesis is required. -/
theorem Ioi_zero_eq_of_positive_tails (μ ν : Measure ℝ)
    (htail : ∀ t : ℝ, 0 < t → t < 1 →
      μ (Set.Ioi t) = ν (Set.Ioi t)) :
    μ (Set.Ioi (0 : ℝ)) = ν (Set.Ioi (0 : ℝ)) := by
  let s : ℕ → Set ℝ := positiveTailApproximants
  have hs : Monotone s := positiveTailApproximants_mono
  have hss : (⋃ n, s n) = Set.Ioi (0 : ℝ) :=
    positiveTailApproximants_iUnion
  have hterms (n : ℕ) : μ (s n) = ν (s n) := by
    apply htail
    · positivity
    · change (1 : ℝ) / ((n : ℝ) + 2) < 1
      apply (div_lt_iff₀ (by positivity)).2
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith
  calc
    μ (Set.Ioi (0 : ℝ)) = μ (⋃ n, s n) := by rw [hss]
    _ = ⨆ n, μ (s n) := hs.measure_iUnion
    _ = ⨆ n, ν (s n) := by simp only [hterms]
    _ = ν (⋃ n, s n) := (hs.measure_iUnion).symm
    _ = ν (Set.Ioi (0 : ℝ)) := by rw [hss]

end DFL.Probability
