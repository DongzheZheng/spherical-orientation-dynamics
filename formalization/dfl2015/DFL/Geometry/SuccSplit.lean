import DFL.Geometry.SphereMeasure

/-!
# Dimension-independent distinguished-coordinate Fubini split

The split is a measurable equivalence from the original Euclidean space,
not a definition of a one-dimensional spherical marginal.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

def splitSucc (m : ℕ) : Ambient (m + 1) ≃ᵐ ℝ × Ambient m :=
  ((MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin m → ℝ))))

theorem splitSucc_measurePreserving (m : ℕ) :
    MeasurePreserving (splitSucc m) := by
  unfold splitSucc
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (PiLp.volume_preserving_toLp (Fin m))).comp
    ((volume_preserving_piFinSuccAbove
      (fun _ : Fin (m + 1) => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin (m + 1))))

theorem splitSucc_fst (m : ℕ) (x : Ambient (m + 1)) :
    (splitSucc m x).1 = x ⟨0, by omega⟩ := by
  rfl

theorem splitSucc_norm_sq (m : ℕ) (x : Ambient (m + 1)) :
    ‖x‖ ^ 2 = (splitSucc m x).1 ^ 2 + ‖(splitSucc m x).2‖ ^ 2 := by
  simp [splitSucc, MeasurableEquiv.prodCongr, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  rfl

theorem splitSucc_symm_norm_sq (m : ℕ) (s : ℝ) (y : Ambient m) :
    ‖(splitSucc m).symm (s, y)‖ ^ 2 = s ^ 2 + ‖y‖ ^ 2 := by
  simpa using splitSucc_norm_sq m ((splitSucc m).symm (s, y))

theorem splitSucc_symm_fst (m : ℕ) (s : ℝ) (y : Ambient m) :
    ((splitSucc m).symm (s, y)) ⟨0, by omega⟩ = s := by
  simpa using (splitSucc_fst m ((splitSucc m).symm (s, y))).symm

end

end DFL.Geometry
