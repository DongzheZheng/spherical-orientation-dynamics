import DFL.Geometry.CircleCDFSource
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# Mass and support of the Chebyshev arcsine measure

These facts concern Mathlib's independent arcsine measure. They do not
identify it with the original sphere-coordinate pushforward.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

instance : IsFiniteMeasure Polynomial.Chebyshev.measureT := by
  have hi : Integrable (fun _ : ℝ => (1 : ℝ))
      Polynomial.Chebyshev.measureT :=
    Polynomial.Chebyshev.integrable_measureT (by fun_prop)
  exact (integrable_const_iff.mp hi).resolve_left (by norm_num)

theorem measureT_univ_real :
    Polynomial.Chebyshev.measureT.real Set.univ = Real.pi := by
  have h := Polynomial.Chebyshev.integral_measureT_eq_integral_cos
    (f := fun _ : ℝ => (1 : ℝ))
  simpa [integral_const] using h

theorem measureT_outside_Icc :
    Polynomial.Chebyshev.measureT (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  rw [Polynomial.Chebyshev.measureT, Measure.restrict_apply measurableSet_Icc.compl]
  have hdisj : (Set.Icc (-1 : ℝ) 1)ᶜ ∩ Set.Ioc (-1) 1 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Icc,
      Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx, hlow, hhigh⟩
    exact hx ⟨hlow.le, hhigh⟩
  rw [hdisj]
  simp

theorem measureT_Iic_low_real (t : ℝ) (ht : t ≤ -1) :
    Polynomial.Chebyshev.measureT.real (Set.Iic t) = 0 := by
  have hsub : Set.Iic t ⊆ (Set.Ioc (-1 : ℝ) 1)ᶜ := by
    intro x hx
    change x ≤ t at hx
    simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and]
    intro hlow
    linarith
  have hnull : Polynomial.Chebyshev.measureT
      (Set.Ioc (-1 : ℝ) 1)ᶜ = 0 := by
    rw [Polynomial.Chebyshev.measureT, Measure.restrict_apply measurableSet_Ioc.compl]
    simp
  exact measureReal_mono_null hsub ((measureReal_eq_zero_iff).2 hnull)

theorem measureT_Iic_high_real (t : ℝ) (ht : 1 ≤ t) :
    Polynomial.Chebyshev.measureT.real (Set.Iic t) = Real.pi := by
  have hsub : (Set.Ioi t) ⊆ (Set.Icc (-1 : ℝ) 1)ᶜ := by
    intro x hx
    change t < x at hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and]
    intro hlow
    linarith
  have htail : Polynomial.Chebyshev.measureT.real (Set.Ioi t) = 0 :=
    measureReal_mono_null hsub ((measureReal_eq_zero_iff).2 measureT_outside_Icc)
  have hcompl := measureReal_compl (μ := Polynomial.Chebyshev.measureT)
    (s := Set.Ioi t) measurableSet_Ioi
  simpa only [Set.compl_Ioi, measureT_univ_real, htail, sub_zero] using hcompl

end

end DFL.Geometry
