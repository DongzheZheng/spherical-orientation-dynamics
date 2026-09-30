import DFL.Geometry.CircleMeasureTBasic
import DFL.Geometry.CircleTargetCDF

/-!
# Lower rays of the independent Chebyshev arcsine measure

The density measure is atomless, so Mathlib's closed upper-tail formula
also determines closed lower rays, the determining class used for the
original circle-coordinate law.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

private instance : NoAtoms Polynomial.Chebyshev.measureT := by
  unfold Polynomial.Chebyshev.measureT
  infer_instance

theorem measureT_Iic_internal_real (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    Polynomial.Chebyshev.measureT.real (Set.Iic t) =
      Real.pi - Real.arccos t := by
  let μ := Polynomial.Chebyshev.measureT
  have hatom : μ ({t} : Set ℝ) = 0 := measure_singleton t
  have hset : Set.Iic t = Set.Iio t ∪ {t} := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
    exact le_iff_lt_or_eq
  have hd : Disjoint (Set.Iio t) ({t} : Set ℝ) := by
    apply Set.disjoint_left.mpr
    intro x hx heq
    change x < t at hx
    change x = t at heq
    subst x
    exact (lt_irrefl t) hx
  have hmeasure : μ (Set.Iic t) = μ (Set.Iio t) := by
    rw [hset, measure_union hd (measurableSet_singleton t), hatom, add_zero]
  have hcompl := measureReal_compl (μ := μ)
    (s := Set.Ici t) measurableSet_Ici
  have hIio : μ.real (Set.Iio t) = Real.pi - Real.arccos t := by
    simpa [μ, measureT_univ_real,
      chebyshev_measureT_Ici_real t ht] using hcompl
  change (μ (Set.Iic t)).toReal = Real.pi - Real.arccos t
  rw [hmeasure]
  exact hIio

end

end DFL.Geometry
