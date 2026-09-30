import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# Distribution function of the Chebyshev comparison measure

The arcsine measure in mathlib is the comparison measure for the actual
circle coordinate pushforward.  Its upper tail follows directly from its
cosine integration formula.  This file proves the distribution function
of that genuine measure, rather than assuming a density transformation.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped Interval

noncomputable section

private theorem cos_ge_iff_le_arccos {t θ : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    t ≤ Real.cos θ ↔ θ ≤ Real.arccos t := by
  have ha : Real.arccos t ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg t, Real.arccos_le_pi t⟩
  have hcos : Real.cos (Real.arccos t) = t :=
    Real.cos_arccos ht.1 ht.2
  constructor
  · intro hc
    by_contra h
    have hlt : Real.arccos t < θ := lt_of_not_ge h
    have hdec := Real.strictAntiOn_cos ha hθ hlt
    rw [hcos] at hdec
    linarith
  · intro hle
    have hanti := Real.antitoneOn_cos hθ ha hle
    rw [hcos] at hanti
    exact hanti

/-- For every threshold in the closed support, the upper closed tail of the Chebyshev
arcsine measure has length `arccos t`. -/
theorem chebyshev_measureT_Ici_real (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    Polynomial.Chebyshev.measureT.real (Set.Ici t) =
      Real.arccos t := by
  let a := Real.arccos t
  have ha : a ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg t, Real.arccos_le_pi t⟩
  calc
    Polynomial.Chebyshev.measureT.real (Set.Ici t) =
        ∫ x, (Set.Ici t).indicator (fun _ : ℝ => (1 : ℝ)) x
          ∂Polynomial.Chebyshev.measureT :=
      (integral_indicator_one measurableSet_Ici).symm
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          (Set.Ici t).indicator (fun _ : ℝ => (1 : ℝ)) (Real.cos θ) :=
      Polynomial.Chebyshev.integral_measureT_eq_integral_cos
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          (Set.Iic a).indicator (fun _ : ℝ => (1 : ℝ)) θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
      have hiff := cos_ge_iff_le_arccos ht hθ'
      change (Set.Ici t).indicator (fun _ : ℝ => (1 : ℝ))
          (Real.cos θ) =
        (Set.Iic a).indicator (fun _ : ℝ => (1 : ℝ)) θ
      by_cases hle : θ ≤ a
      · have hc : t ≤ Real.cos θ := hiff.mpr hle
        simp [Set.indicator, hc, hle]
      · have hc : ¬ t ≤ Real.cos θ := fun h => hle (hiff.mp h)
        simp [Set.indicator, hc, hle]
    _ = ∫ θ in (0 : ℝ)..a, (1 : ℝ) := by
      simpa only [Set.indicator] using
        (intervalIntegral.integral_indicator (f := fun _ : ℝ => (1 : ℝ)) ha)
    _ = Real.arccos t := by simp [a]

end

end DFL.Geometry
