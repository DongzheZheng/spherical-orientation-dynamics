import DFL.Geometry.ConeCapThree

/-!
# A volume-preserving split of three Euclidean coordinates

This is the coordinate change needed for Fubini in the n = 3 cap cone.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

def splitThree : Ambient 3 ≃ᵐ ℝ × Ambient 2 :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

theorem splitThree_measurePreserving : MeasurePreserving splitThree := by
  unfold splitThree
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

theorem splitThree_fst (x : Ambient 3) :
    (splitThree x).1 = x ⟨0, by decide⟩ := by
  rfl

theorem splitThree_norm_sq (x : Ambient 3) :
    ‖x‖ ^ 2 = (splitThree x).1 ^ 2 + ‖(splitThree x).2‖ ^ 2 := by
  simp [splitThree, MeasurableEquiv.prodCongr, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  rfl

theorem splitThree_symm_norm_sq (s : ℝ) (y : Ambient 2) :
    ‖splitThree.symm (s, y)‖ ^ 2 = s ^ 2 + ‖y‖ ^ 2 := by
  simpa using splitThree_norm_sq (splitThree.symm (s, y))

theorem splitThree_symm_fst (s : ℝ) (y : Ambient 2) :
    (splitThree.symm (s, y)) ⟨0, by decide⟩ = s := by
  simpa using (splitThree_fst (splitThree.symm (s, y))).symm

end

end DFL.Geometry
