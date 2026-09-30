import DFL.GCI.OriginalTarget

/-!
# Positivity supplied directly by the original angular form

These statements use the original `θ` weight and potential from DFL 2015.
They are unconditional algebraic/measure-theoretic inputs to a future
coercivity and uniqueness proof.  They do not assume or prove the GCI
coefficient comparison.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

theorem angularWeight_nonneg (n : ℕ) (r θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    0 ≤ angularWeight n r θ := by
  unfold angularWeight
  exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc hθ) _)
    (Real.exp_nonneg _)

theorem angularPotential_nonneg (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) :
    0 ≤ angularPotential n θ := by
  unfold angularPotential
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact div_nonneg (by linarith) (sq_nonneg _)

theorem original_energy_density_nonneg (n : ℕ) (hn : 2 ≤ n)
    (r θ : ℝ) (s : AngularState)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    0 ≤ angularWeight n r θ *
      (angularDerivative n s θ * angularDerivative n s θ +
        angularPotential n θ * s.g θ * s.g θ) := by
  have hw := angularWeight_nonneg n r θ hθ
  have hp := angularPotential_nonneg n hn θ
  have hs : 0 ≤ angularDerivative n s θ * angularDerivative n s θ := mul_self_nonneg _
  have ht : 0 ≤ angularPotential n θ * s.g θ * s.g θ := by
    rw [show angularPotential n θ * s.g θ * s.g θ =
      angularPotential n θ * (s.g θ) ^ 2 by ring]
    exact mul_nonneg hp (sq_nonneg _)
  exact mul_nonneg hw (add_nonneg hs ht)

/-- The original weak-form energy cannot be negative.  Integrability for a
weak solution is specified in `OriginalWeakGCISolution`.  This uses no
auxiliary amplitude, and holds including `n=2`. -/
theorem originalWeakForm_self_nonneg (n : ℕ) (hn : 2 ≤ n)
    (r : ℝ) (s : AngularState) :
    0 ≤ originalWeakForm n r s s := by
  unfold originalWeakForm
  apply intervalIntegral.integral_nonneg Real.pi_pos.le
  intro θ hθ
  exact original_energy_density_nonneg n hn r θ s
    ⟨hθ.1, hθ.2⟩

/-- The weak forcing paired with `g` is exactly the denominator of the
original hydrodynamic coefficient.  This is an angular identity on the
physical interval, not a change of measure to a free amplitude. -/
theorem originalSourcePairing_eq_denominator (n : ℕ) (hn : 2 ≤ n)
    (r : ℝ) (s : AngularState) :
    originalSourcePairing n r s = originalGCIDenominator n r s := by
  unfold originalSourcePairing originalGCIDenominator
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hθ' : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ'
  have hnr : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have hnr' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpow : Real.rpow (Real.sin θ) ((n : ℝ) - 1) =
      Real.rpow (Real.sin θ) ((n : ℝ) - 2) * Real.sin θ := by
    calc
      Real.rpow (Real.sin θ) ((n : ℝ) - 1) =
          Real.rpow (Real.sin θ) (((n : ℝ) - 2) + 1) := by congr 1; ring
      _ = Real.rpow (Real.sin θ) ((n : ℝ) - 2) *
          Real.rpow (Real.sin θ) 1 := by
        exact Real.rpow_add_of_nonneg hs hnr (by norm_num)
      _ = Real.rpow (Real.sin θ) ((n : ℝ) - 2) * Real.sin θ := by
        simp
  change Real.rpow (Real.sin θ) ((n : ℝ) - 2) *
      Real.exp (r * Real.cos θ) * Real.sin θ * s.g θ =
    s.g θ * Real.exp (r * Real.cos θ) *
      Real.rpow (Real.sin θ) ((n : ℝ) - 1)
  rw [hpow]
  ring

/-- A consequence of the *original weak equation*: its source pairing,
which is precisely the GCI denominator, is nonnegative.  Strict positivity
requires coercivity/nontriviality and remains a separate obligation. -/
theorem weak_solution_denominator_nonneg (n : ℕ) (hn : 2 ≤ n)
    (r : ℝ) (s : AngularState) (hs : OriginalWeakGCISolution n r s) :
    0 ≤ originalGCIDenominator n r s := by
  rw [← originalSourcePairing_eq_denominator n hn r s]
  have heq := (hs.2 s hs.1).2.2
  rw [← heq]
  exact originalWeakForm_self_nonneg n hn r s

end

end DFL.GCI
