import DFL.Geometry.ThreeSplit

/-!
# Exact Fubini reduction of a three-dimensional spherical cap cone

The remaining task is evaluation of the two-dimensional sections; this file
does not assume any spherical marginal density.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

theorem coneCapThree_isOpen (t : ℝ) : IsOpen (coneCapThree t) := by
  have heq : coneCapThree t =
      {x : Ambient 3 | (0 : ℝ) < ‖x‖} ∩
      {x : Ambient 3 | ‖x‖ < (1 : ℝ)} ∩
      {x : Ambient 3 | t * ‖x‖ < x ⟨0, by decide⟩} := by
    ext x
    simpa only [Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc] using
      mem_coneCapThree_iff t x
  rw [heq]
  exact ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).inter
    (isOpen_lt (continuous_const.mul continuous_norm) (by fun_prop))

theorem coneCapThree_volume_fubini (t : ℝ) :
    volume (coneCapThree t) =
      ∫⁻ s : ℝ, volume {y : Ambient 2 |
        splitThree.symm (s, y) ∈ coneCapThree t} := by
  have hs : MeasurableSet (coneCapThree t) := (coneCapThree_isOpen t).measurableSet
  have hmp : MeasurePreserving splitThree.symm :=
    splitThree_measurePreserving.symm splitThree
  have hs' : MeasurableSet (splitThree.symm ⁻¹' coneCapThree t) :=
    hs.preimage splitThree.symm.measurable
  calc
    volume (coneCapThree t) =
        (volume : Measure (ℝ × Ambient 2)).map splitThree.symm (coneCapThree t) := by
          rw [hmp.map_eq]
    _ = (volume : Measure (ℝ × Ambient 2))
        (splitThree.symm ⁻¹' coneCapThree t) :=
          Measure.map_apply splitThree.symm.measurable hs
    _ = ∫⁻ s : ℝ, volume {y : Ambient 2 |
        splitThree.symm (s, y) ∈ coneCapThree t} := by
          rw [Measure.volume_eq_prod, Measure.prod_apply hs']
          rfl

end

end DFL.Geometry
