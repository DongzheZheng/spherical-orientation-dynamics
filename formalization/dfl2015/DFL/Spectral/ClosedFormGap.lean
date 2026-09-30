import DFL.Spectral.ClosedFormGraph

/-!
# The Rayleigh infimum survives completion of the physical smooth graph

This file proves equality of two exact variational numbers: the infimum over
the ambient `C¹` sphere core and the infimum over its complete `L²` graph
closure. It does not identify that graph closure with the independently
defined classical Sobolev `H¹(Sᵈ)` in the 2013 source.
-/

namespace DFL.Spectral

open MeasureTheory

noncomputable section

private abbrev FormPair (d : ℕ) (r : ℝ) :=
  Lp ℝ 2 (alignedMeasure d r) × Lp (Ambient d) 2 (alignedMeasure d r)

/-- A smooth core test belongs to its graph completion. -/
def coreToClosed (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    ClosedFormSpace d r :=
  ⟨coreGraph d r f, subset_closure ⟨f, rfl⟩⟩

/-- The Rayleigh ratio of a completed value/gradient pair. -/
def closedFormRayleigh (d : ℕ) (r : ℝ)
    (p : ClosedFormSpace d r) : ℝ :=
  ‖p.1.2‖ ^ 2 / ‖p.1.1‖ ^ 2

def closedFormRayleighValues (d : ℕ) (r : ℝ) : Set ℝ :=
  {q | ∃ p : ClosedFormSpace d r,
    0 < ‖p.1.1‖ ^ 2 ∧ q = closedFormRayleigh d r p}

/-- Spectral variational number of the completed physical graph form. -/
def closedFormGap (d : ℕ) (r : ℝ) : ℝ :=
  sInf (closedFormRayleighValues d r)

theorem coreToClosed_value_norm_sq (d : ℕ) (r : ℝ)
    (f : SphereC1Core d) :
    ‖(coreToClosed d r f).1.1‖ ^ 2 =
      sphereVariance d r (coreValue d f) :=
  coreGraph_value_norm_sq d r f

theorem coreToClosed_gradient_norm_sq (d : ℕ) (r : ℝ)
    (f : SphereC1Core d) :
    ‖(coreToClosed d r f).1.2‖ ^ 2 = coreEnergy d r f :=
  coreGraph_gradient_norm_sq d r f

theorem coreToClosed_rayleigh (d : ℕ) (r : ℝ)
    (f : SphereC1Core d) :
    closedFormRayleigh d r (coreToClosed d r f) = coreRayleigh d r f := by
  rw [closedFormRayleigh, coreRayleigh,
    coreToClosed_value_norm_sq, coreToClosed_gradient_norm_sq]

theorem closedFormRayleighValues_nonempty (d : ℕ) (r : ℝ) :
    (closedFormRayleighValues d r).Nonempty := by
  refine ⟨closedFormRayleigh d r (coreToClosed d r (coordinateCore d 0)),
    coreToClosed d r (coordinateCore d 0), ?_, rfl⟩
  rw [coreToClosed_value_norm_sq]
  exact coordinateCore_variance_pos d r 0

theorem closedFormRayleighValues_bddBelow (d : ℕ) (r : ℝ) :
    BddBelow (closedFormRayleighValues d r) := by
  refine ⟨0, ?_⟩
  intro q hq
  rcases hq with ⟨p, hpos, rfl⟩
  exact div_nonneg (sq_nonneg _) hpos.le

/-- Restricting the completed variational problem to smooth core points
shows its infimum is no larger than the smooth-core infimum. -/
theorem closedFormGap_le_coreGap (d : ℕ) (r : ℝ) :
    closedFormGap d r ≤ coreGap d r := by
  unfold coreGap
  apply le_csInf (coreRayleighValues_nonempty d r)
  intro q hq
  rcases hq with ⟨f, hvar, rfl⟩
  have hmem : closedFormRayleigh d r (coreToClosed d r f) ∈
      closedFormRayleighValues d r := by
    refine ⟨coreToClosed d r f, ?_, rfl⟩
    rw [coreToClosed_value_norm_sq]
    exact hvar
  have hle := csInf_le (closedFormRayleighValues_bddBelow d r) hmem
  simpa only [closedFormGap, coreToClosed_rayleigh] using hle

private theorem coreGap_form_inequality (d : ℕ) (r : ℝ)
    (f : SphereC1Core d) :
    coreGap d r * ‖(coreGraph d r f).1‖ ^ 2 ≤
      ‖(coreGraph d r f).2‖ ^ 2 := by
  rw [coreGraph_value_norm_sq, coreGraph_gradient_norm_sq]
  by_cases hv : 0 < sphereVariance d r (coreValue d f)
  · have hmem : coreRayleigh d r f ∈ coreRayleighValues d r :=
      ⟨f, hv, rfl⟩
    have hle : coreGap d r ≤ coreRayleigh d r f :=
      csInf_le (coreRayleighValues_bddBelow d r) hmem
    exact (le_div_iff₀ hv).mp hle
  · have hv0 : sphereVariance d r (coreValue d f) = 0 :=
      le_antisymm (le_of_not_gt hv) (sphereVariance_nonneg d r (coreValue d f))
    rw [hv0, mul_zero]
    exact coreEnergy_nonneg d r f

private theorem coreGap_form_inequality_closed (d : ℕ) (r : ℝ)
    (p : FormPair d r) (hp : p ∈ closedFormGraph d r) :
    coreGap d r * ‖p.1‖ ^ 2 ≤ ‖p.2‖ ^ 2 := by
  let S : Set (FormPair d r) :=
    {q | coreGap d r * ‖q.1‖ ^ 2 ≤ ‖q.2‖ ^ 2}
  have hclosed : IsClosed S := by
    apply isClosed_le
    · exact continuous_const.mul ((continuous_norm.comp continuous_fst).pow 2)
    · exact (continuous_norm.comp continuous_snd).pow 2
  have hsubset : Set.range (coreGraph d r) ⊆ S := by
    rintro q ⟨f, rfl⟩
    exact coreGap_form_inequality d r f
  have hclosure : closedFormGraph d r ⊆ S :=
    closure_minimal hsubset hclosed
  exact hclosure hp

/-- The global smooth-core Poincaré inequality extends to every point of
the complete original-sphere graph by closedness of the quadratic
inequality. -/
theorem coreGap_le_closedFormGap (d : ℕ) (r : ℝ) :
    coreGap d r ≤ closedFormGap d r := by
  unfold closedFormGap
  apply le_csInf (closedFormRayleighValues_nonempty d r)
  intro q hq
  rcases hq with ⟨p, hvar, rfl⟩
  have hineq := coreGap_form_inequality_closed d r p.1 p.2
  exact (le_div_iff₀ hvar).2 hineq

/-- Completing the exact physical smooth graph does not change its
Rayleigh infimum. The separate identification of this completion with
the source paper's classical `H¹(Sᵈ)` remains unproved. -/
theorem closedFormGap_eq_coreGap (d : ℕ) (r : ℝ) :
    closedFormGap d r = coreGap d r :=
  le_antisymm (closedFormGap_le_coreGap d r)
    (coreGap_le_closedFormGap d r)

end

end DFL.Spectral
