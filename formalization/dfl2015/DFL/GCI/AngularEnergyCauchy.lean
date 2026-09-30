import DFL.GCI.AngularSineTest

/-!
# The original forcing-energy Cauchy inequality in every dimension

The physical test `sin θ` is handled within the original angular energy
space.  Its self-energy is shown integrable without endpoint conventions
entering the interval integral, and the weak equation supplies the cross
term.  This is an unconditional ingredient for a general-dimensional GCI
upper comparison, not the comparison itself.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

private theorem ae_angular_interior :
    ∀ᵐ θ ∂volume.restrict (Set.uIoc (0 : ℝ) Real.pi),
      θ ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have hmem :
      ∀ᵐ θ ∂volume.restrict (Set.uIoc (0 : ℝ) Real.pi),
        θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
    simpa only [Set.uIoc_of_le Real.pi_pos.le] using
      (ae_restrict_mem (μ := volume) measurableSet_Ioc)
  have hne :
      ∀ᵐ θ ∂volume.restrict (Set.uIoc (0 : ℝ) Real.pi),
        θ ≠ Real.pi :=
    ae_restrict_of_ae ((volume : Measure ℝ).ae_ne Real.pi)
  filter_upwards [hmem, hne] with θ hθ hθne
  exact ⟨hθ.1, lt_of_le_of_ne hθ.2 hθne⟩

theorem sineTest_angularDerivative_interior
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    angularDerivative n (sineTestState n) θ = Real.cos θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have ha : (n : ℝ) / 2 - 1 = halfPower n := by
    unfold halfPower
    ring
  have hprod :
      Real.rpow (Real.sin θ) (halfPower n - 1) * Real.sin θ =
        Real.rpow (Real.sin θ) (halfPower n) := by
    calc
      _ = Real.rpow (Real.sin θ) (halfPower n - 1) *
            Real.rpow (Real.sin θ) 1 := by simp
      _ = Real.rpow (Real.sin θ) ((halfPower n - 1) + 1) :=
        (Real.rpow_add hs _ _).symm
      _ = Real.rpow (Real.sin θ) (halfPower n) := by
        congr 1
        ring
  have hpne : Real.rpow (Real.sin θ) (halfPower n) ≠ 0 :=
    (Real.rpow_pos_of_pos hs _).ne'
  change
    (((n : ℝ) / 2 *
        Real.rpow (Real.sin θ) ((n : ℝ) / 2 - 1) * Real.cos θ -
      halfPower n * Real.cos θ *
        Real.rpow (Real.sin θ) (halfPower n - 1) * Real.sin θ) /
      Real.rpow (Real.sin θ) (halfPower n)) = Real.cos θ
  have hsub :
      halfPower n * Real.cos θ *
          Real.rpow (Real.sin θ) (halfPower n - 1) * Real.sin θ =
        halfPower n * Real.cos θ *
          Real.rpow (Real.sin θ) (halfPower n) := by
    calc
      _ = (halfPower n * Real.cos θ) *
            (Real.rpow (Real.sin θ) (halfPower n - 1) * Real.sin θ) := by
        ring
      _ = _ := by rw [hprod]
  rw [ha, hsub]
  field_simp [hpne]
  unfold halfPower
  ring

private theorem sineTest_potential_interior
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    angularPotential n θ * (sineTestState n).g θ *
      (sineTestState n).g θ = (n : ℝ) - 2 := by
  have hs : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_mem_Ioo hθ).ne'
  change (((n : ℝ) - 2) / (Real.sin θ) ^ 2) *
    Real.sin θ * Real.sin θ = (n : ℝ) - 2
  field_simp [hs]

theorem sineTest_self_energy_density_interior
    (n : ℕ) (r θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    formIntegrand n r (sineTestState n) (sineTestState n) θ =
      angularWeight n r θ *
        ((Real.cos θ) ^ 2 + ((n : ℝ) - 2)) := by
  unfold formIntegrand
  rw [sineTest_angularDerivative_interior n θ hθ,
    sineTest_potential_interior n θ hθ]
  ring

private theorem sineTest_self_energy_proxy_integrable
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ => angularWeight n r θ *
        ((Real.cos θ) ^ 2 + ((n : ℝ) - 2)))
      volume (0 : ℝ) Real.pi := by
  have hnr : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have hnr' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hw : Continuous (angularWeight n r) := by
    unfold angularWeight
    exact ((Real.continuous_rpow_const hnr).comp Real.continuous_sin).mul
      (Real.continuous_exp.comp
        ((continuous_const.mul Real.continuous_cos)))
  exact (hw.mul (by fun_prop : Continuous (fun θ : ℝ =>
    (Real.cos θ) ^ 2 + ((n : ℝ) - 2)))).intervalIntegrable _ _

/-- The physical sine test has finite original weighted self-energy for
every ambient dimension `n≥2`. -/
theorem sineTest_self_energy_integrable
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    IntervalIntegrable
      (formIntegrand n r (sineTestState n) (sineTestState n))
      volume (0 : ℝ) Real.pi := by
  apply (sineTest_self_energy_proxy_integrable n hn r).congr_ae
  filter_upwards [ae_angular_interior] with θ hθ
  exact (sineTest_self_energy_density_interior n r θ hθ).symm

/-- The sine-test energy is the explicit smooth angular integral almost
everywhere, so endpoint totalization has no effect on the value. -/
theorem sineTest_self_energy_formula
    (n : ℕ) (r : ℝ) :
    originalWeakForm n r (sineTestState n) (sineTestState n) =
      ∫ θ in (0 : ℝ)..Real.pi,
        angularWeight n r θ *
          ((Real.cos θ) ^ 2 + ((n : ℝ) - 2)) := by
  unfold originalWeakForm
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [ae_angular_interior] with θ hθ
  exact sineTest_self_energy_density_interior n r θ hθ

/-- A dimension-independent Cauchy inequality for the *original* weak
solution, with its original denominator and the physical forcing norm. -/
theorem weak_solution_forcing_energy_cauchy
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ)
    (s : AngularState)
    (hs : OriginalWeakGCISolution n r s) :
    (originalForcingNorm n r) ^ 2 ≤
      originalGCIDenominator n r s *
        originalWeakForm n r (sineTestState n) (sineTestState n) := by
  rw [← sourcePairing_sine_eq_forcingNorm]
  exact weak_solution_energy_cauchy n hn r s (sineTestState n)
    hs (sineTestState_mem_energy n hn)
    (sineTest_self_energy_integrable n hn r)

end

end DFL.GCI
