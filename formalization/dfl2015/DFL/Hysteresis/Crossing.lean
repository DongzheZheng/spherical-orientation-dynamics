import Mathlib

/-!
# The integrating-factor crossing in the DFL single-fold proof

This is the calculus step after the original spherical mean has produced
`K' = positive_factor * F(r, 0)`.  Its hypotheses state the derivative signs
and the two endpoint signs explicitly.  It does not assert those inputs for
the von Mises--Fisher mean; that is a separate target-facing obligation.
-/

namespace DFL.Hysteresis.Crossing

open Set

/-- A negative derivative on the open interval gives strict decrease on its
closed interval, including the endpoints. -/
theorem strictAntiOn_left {K : ℝ → ℝ} {δ r₀ : ℝ}
    (hcont : Continuous K)
    (hneg : ∀ x, δ < x → x < r₀ → deriv K x < 0) :
    StrictAntiOn K (Icc δ r₀) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc δ r₀) hcont.continuousOn
  intro x hx
  have hx' : x ∈ Ioo δ r₀ := by simpa using hx
  exact hneg x hx'.1 hx'.2

/-- A positive derivative to the right of `r₀` gives strict increase on the
entire closed ray, including `r₀`. -/
theorem strictMonoOn_right {K : ℝ → ℝ} {r₀ : ℝ}
    (hcont : Continuous K)
    (hpos : ∀ x, r₀ < x → 0 < deriv K x) :
    StrictMonoOn K (Ici r₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici r₀) hcont.continuousOn
  intro x hx
  have hx' : x ∈ Ioi r₀ := by simpa using hx
  exact hpos x hx'

/-- The one-crossing conclusion used in the DFL single-fold argument.  The
last two fields give the positive derivative at the crossing and uniqueness
among all points at or to the right of `δ`, not just between `r₀` and `L`. -/
theorem crossing_from_derivative_signs {K : ℝ → ℝ} {δ r₀ L : ℝ}
    (hδr₀ : δ < r₀) (hr₀L : r₀ < L)
    (hcont : Continuous K)
    (hneg : ∀ x, δ < x → x < r₀ → deriv K x < 0)
    (hpos : ∀ x, r₀ < x → 0 < deriv K x)
    (hKδ : K δ < 0) (hKL : 0 < K L) :
    ∃ r : ℝ, r₀ < r ∧ r < L ∧ K r = 0 ∧
      (∀ x, δ ≤ x → x < r → K x < 0) ∧
      (∀ x, r < x → 0 < K x) ∧
      0 < deriv K r ∧
      (∀ x, δ ≤ x → K x = 0 → x = r) := by
  have hleft := strictAntiOn_left hcont hneg
  have hright := strictMonoOn_right hcont hpos
  have hKr₀δ : K r₀ < K δ :=
    hleft (left_mem_Icc.mpr (le_of_lt hδr₀))
      (right_mem_Icc.mpr (le_of_lt hδr₀)) hδr₀
  have hKr₀ : K r₀ < 0 := lt_trans hKr₀δ hKδ
  have hzero : (0 : ℝ) ∈ Icc (K r₀) (K L) :=
    ⟨le_of_lt hKr₀, le_of_lt hKL⟩
  obtain ⟨r, hrI, hrzero⟩ :=
    (intermediate_value_Icc (le_of_lt hr₀L) hcont.continuousOn) hzero
  have hr₀r : r₀ < r := by
    rcases lt_or_eq_of_le hrI.1 with h | h
    · exact h
    · subst r
      exact False.elim ((ne_of_lt hKr₀) hrzero)
  have hrL : r < L := by
    rcases lt_or_eq_of_le hrI.2 with h | h
    · exact h
    · subst r
      exact False.elim ((ne_of_gt hKL) hrzero)
  have hnegative : ∀ x, δ ≤ x → x < r → K x < 0 := by
    intro x hδx hxr
    by_cases hxr₀ : x < r₀
    · rcases eq_or_lt_of_le hδx with heq | hδx'
      · simpa [heq] using hKδ
      · have hKxδ : K x < K δ :=
          hleft (left_mem_Icc.mpr (le_of_lt hδr₀))
            ⟨le_of_lt hδx', le_of_lt hxr₀⟩ hδx'
        exact lt_trans hKxδ hKδ
    · have hKxr : K x < K r :=
        hright (le_of_not_gt hxr₀) (le_of_lt hr₀r) hxr
      simpa [hrzero] using hKxr
  have hpositive : ∀ x, r < x → 0 < K x := by
    intro x hrx
    have hKrx : K r < K x :=
      hright (le_of_lt hr₀r) (le_trans (le_of_lt hr₀r) (le_of_lt hrx)) hrx
    simpa [hrzero] using hKrx
  have hunique : ∀ x, δ ≤ x → K x = 0 → x = r := by
    intro x hδx hxzero
    rcases lt_trichotomy x r with hxr | heq | hrx
    · have h := hnegative x hδx hxr
      rw [hxzero] at h
      exact False.elim (lt_irrefl 0 h)
    · exact heq
    · have h := hpositive x hrx
      rw [hxzero] at h
      exact False.elim (lt_irrefl 0 h)
  exact ⟨r, hr₀r, hrL, hrzero, hnegative, hpositive,
    hpos r hr₀r, hunique⟩

end DFL.Hysteresis.Crossing
