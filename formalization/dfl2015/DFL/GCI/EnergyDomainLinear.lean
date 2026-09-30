import DFL.GCI.EnergyDomainIntegrability

/-! Linear operations on the represented original energy domain. -/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def stateAdd (s v : AngularState) : AngularState :=
  ⟨fun θ => s.g θ + v.g θ,
   fun θ => s.scaledDerivative θ + v.scaledDerivative θ⟩

def stateSMul (a : ℝ) (s : AngularState) : AngularState :=
  ⟨fun θ => a * s.g θ, fun θ => a * s.scaledDerivative θ⟩

def stateSub (s v : AngularState) : AngularState :=
  stateAdd s (stateSMul (-1) v)

private theorem square_sum_intervalIntegrable
    {f g : ℝ → ℝ}
    (hf : MemLp f 2 angularIntervalMeasure)
    (hg : MemLp g 2 angularIntervalMeasure) :
    IntervalIntegrable (fun θ => (f θ + g θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
  exact intervalIntegrable_iff.mpr ((hf.add hg).integrable_sq)

theorem stateSMul_mem_energy (n : ℕ) (s : AngularState)
    (hs : AngularEnergyDomain n s) (a : ℝ) :
    AngularEnergyDomain n (stateSMul a s) := by
  refine ⟨hs.1.const_mul a, ?_, ?_, ?_, ?_⟩
  · have hi := hs.2.1.const_mul (a ^ 2)
    apply hi.congr
    intro θ _
    dsimp [stateSMul]
    ring
  · intro θ hθ
    change (Real.sin θ) ^ (halfPower n) * (a * s.g θ) =
      ∫ u in (0 : ℝ)..θ, a * s.scaledDerivative u
    rw [intervalIntegral.integral_const_mul]
    have hrec := hs.2.2.1 θ hθ
    dsimp [scaledFunction] at hrec
    rw [← hrec]
    ring
  · change (∫ u in (0 : ℝ)..Real.pi, a * s.scaledDerivative u) = 0
    rw [intervalIntegral.integral_const_mul, hs.2.2.2.1, mul_zero]
  · have hi := hs.2.2.2.2.const_mul (a ^ 2)
    apply hi.congr
    intro θ _
    dsimp [stateSMul]
    ring

theorem stateAdd_mem_energy (n : ℕ) (hn : 2 ≤ n) (s v : AngularState)
    (hs : AngularEnergyDomain n s) (hv : AngularEnergyDomain n v) :
    AngularEnergyDomain n (stateAdd s v) := by
  refine ⟨hs.1.add hv.1, ?_, ?_, ?_, ?_⟩
  · exact square_sum_intervalIntegrable (scaledDerivative_memLp_two n s hs)
      (scaledDerivative_memLp_two n v hv)
  · intro θ hθ
    change (Real.sin θ) ^ (halfPower n) * (s.g θ + v.g θ) =
      ∫ u in (0 : ℝ)..θ, s.scaledDerivative u + v.scaledDerivative u
    have hsint := hs.1.mono_set (by
      rw [Set.uIcc_of_le hθ.1, Set.uIcc_of_le Real.pi_pos.le]
      exact Set.Icc_subset_Icc le_rfl hθ.2)
    have hvint := hv.1.mono_set (by
      rw [Set.uIcc_of_le hθ.1, Set.uIcc_of_le Real.pi_pos.le]
      exact Set.Icc_subset_Icc le_rfl hθ.2)
    rw [intervalIntegral.integral_add hsint hvint]
    have hsr := hs.2.2.1 θ hθ
    have hvr := hv.2.2.1 θ hθ
    dsimp [scaledFunction] at hsr hvr
    rw [← hsr, ← hvr]
    ring
  · change (∫ u in (0 : ℝ)..Real.pi,
      s.scaledDerivative u + v.scaledDerivative u) = 0
    rw [intervalIntegral.integral_add hs.1 hv.1,
      hs.2.2.2.1, hv.2.2.2.1, add_zero]
  · by_cases hn2 : n = 2
    · subst n
      simp [stateAdd]
    · have hn3 : 3 ≤ n := by omega
      have hsum := square_sum_intervalIntegrable
        (singularRepresentative_memLp_two n hn3 s hs)
        (singularRepresentative_memLp_two n hn3 v hv)
      have hi := hsum.const_mul (((n : ℝ) - 2) ^ 2)
      apply hi.congr_ae
      filter_upwards [moment_ae_interior] with θ hθ
      rw [singularRepresentative_eq n s hs θ hθ,
        singularRepresentative_eq n v hv θ hθ]
      have he : ((n : ℝ) - 4) / 2 = halfPower n - 1 := by
        unfold halfPower
        ring
      dsimp [stateAdd]
      rw [he]
      ring

theorem stateSub_mem_energy (n : ℕ) (hn : 2 ≤ n) (s v : AngularState)
    (hs : AngularEnergyDomain n s) (hv : AngularEnergyDomain n v) :
    AngularEnergyDomain n (stateSub s v) :=
  stateAdd_mem_energy n hn s (stateSMul (-1) v) hs (stateSMul_mem_energy n v hv (-1))

theorem angularDerivative_stateAdd (n : ℕ) (s v : AngularState) (θ : ℝ) :
    angularDerivative n (stateAdd s v) θ =
      angularDerivative n s θ + angularDerivative n v θ := by
  unfold angularDerivative stateAdd
  ring

theorem angularDerivative_stateSMul (n : ℕ) (s : AngularState) (a θ : ℝ) :
    angularDerivative n (stateSMul a s) θ = a * angularDerivative n s θ := by
  unfold angularDerivative stateSMul
  ring

theorem originalWeakForm_stateAdd_left
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (s v t : AngularState)
    (hs : AngularEnergyDomain n s) (hv : AngularEnergyDomain n v)
    (ht : AngularEnergyDomain n t) :
    originalWeakForm n r (stateAdd s v) t =
      originalWeakForm n r s t + originalWeakForm n r v t := by
  have hsi := formIntegrand_intervalIntegrable_of_energyDomain n hn r s t hs ht
  have hvi := formIntegrand_intervalIntegrable_of_energyDomain n hn r v t hv ht
  change (∫ θ in (0 : ℝ)..Real.pi, formIntegrand n r (stateAdd s v) t θ) =
    (∫ θ in (0 : ℝ)..Real.pi, formIntegrand n r s t θ) +
    (∫ θ in (0 : ℝ)..Real.pi, formIntegrand n r v t θ)
  rw [← intervalIntegral.integral_add hsi hvi]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only [formIntegrand]
  rw [angularDerivative_stateAdd]
  dsimp [stateAdd, formIntegrand]
  ring

theorem originalWeakForm_stateSMul_left
    (n : ℕ) (r : ℝ) (s t : AngularState) (a : ℝ) :
    originalWeakForm n r (stateSMul a s) t =
      a * originalWeakForm n r s t := by
  unfold originalWeakForm
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [angularDerivative_stateSMul]
  dsimp [stateSMul]
  ring

end

end DFL.GCI
