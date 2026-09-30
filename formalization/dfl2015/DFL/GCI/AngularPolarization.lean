import DFL.GCI.AngularTest
import DFL.Probability.EnergyResponse

/-!
# Polarizing the original GCI angular form

This file combines the original weak equation, its nonnegative energy,
and the explicitly constructed positive test to derive strict positivity
of the *actual denominator*.  No sign of the numerator is assumed.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def formIntegrand (n : ℕ) (r : ℝ)
    (s v : AngularState) (θ : ℝ) : ℝ :=
  angularWeight n r θ *
    (angularDerivative n s θ * angularDerivative n v θ +
      angularPotential n θ * s.g θ * v.g θ)

private def perturbState (s v : AngularState) (a : ℝ) : AngularState :=
  ⟨fun θ => s.g θ + a * v.g θ,
   fun θ => s.scaledDerivative θ + a * v.scaledDerivative θ⟩

private theorem angularDerivative_perturb (n : ℕ)
    (s v : AngularState) (a θ : ℝ) :
    angularDerivative n (perturbState s v a) θ =
      angularDerivative n s θ + a * angularDerivative n v θ := by
  unfold angularDerivative perturbState
  ring

private theorem formIntegrand_perturb (n : ℕ) (r : ℝ)
    (s v : AngularState) (a θ : ℝ) :
    formIntegrand n r (perturbState s v a) (perturbState s v a) θ =
      formIntegrand n r s s θ +
        (2 * a) * formIntegrand n r s v θ +
        a ^ 2 * formIntegrand n r v v θ := by
  unfold formIntegrand
  rw [angularDerivative_perturb]
  dsimp [perturbState]
  ring

private theorem originalWeakForm_perturb_expansion
    (n : ℕ) (r : ℝ) (s v : AngularState) (a : ℝ)
    (hs : IntervalIntegrable (formIntegrand n r s s)
      volume (0 : ℝ) Real.pi)
    (hsv : IntervalIntegrable (formIntegrand n r s v)
      volume (0 : ℝ) Real.pi)
    (hv : IntervalIntegrable (formIntegrand n r v v)
      volume (0 : ℝ) Real.pi) :
    originalWeakForm n r (perturbState s v a) (perturbState s v a) =
      originalWeakForm n r s s +
        (2 * a) * originalWeakForm n r s v +
        a ^ 2 * originalWeakForm n r v v := by
  change (∫ θ in (0 : ℝ)..Real.pi,
      formIntegrand n r (perturbState s v a) (perturbState s v a) θ) =
    (∫ θ in (0 : ℝ)..Real.pi, formIntegrand n r s s θ) +
      (2 * a) * (∫ θ in (0 : ℝ)..Real.pi, formIntegrand n r s v θ) +
      a ^ 2 * (∫ θ in (0 : ℝ)..Real.pi, formIntegrand n r v v θ)
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi,
        (formIntegrand n r s s θ +
          (2 * a) * formIntegrand n r s v θ) +
          a ^ 2 * formIntegrand n r v v θ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact formIntegrand_perturb n r s v a θ
    _ = (∫ θ in (0 : ℝ)..Real.pi, formIntegrand n r s s θ) +
          (2 * a) * (∫ θ in (0 : ℝ)..Real.pi, formIntegrand n r s v θ) +
          a ^ 2 * (∫ θ in (0 : ℝ)..Real.pi, formIntegrand n r v v θ) := by
      rw [intervalIntegral.integral_add (hs.add (hsv.const_mul (2 * a)))
          (hv.const_mul (a ^ 2)),
        intervalIntegral.integral_add hs (hsv.const_mul (2 * a)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

/-- The denominator in the original weak GCI definition is strictly
positive for every ambient `n ≥ 2` and every real field `r` for which an
original weak solution exists.  In particular this covers `r > 0`.

This does not assert positivity of the numerator or the conjectured upper
bound. -/
theorem weak_solution_denominator_pos
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ)
    (s : AngularState) (hs : OriginalWeakGCISolution n r s) :
    0 < originalGCIDenominator n r s := by
  let v := positiveTestState n
  have hv : AngularEnergyDomain n v := positiveTestState_mem_energy n hn
  have hq : 0 ≤ originalWeakForm n r s s :=
    originalWeakForm_self_nonneg n hn r s
  have hqv : 0 ≤ originalWeakForm n r v v :=
    originalWeakForm_self_nonneg n hn r v
  have hforcing : 0 < originalWeakForm n r s v := by
    have heq := (hs.2 v hv).2.2
    rw [heq]
    exact positiveTest_source_pos_of_weak_solution n hn r s hs
  have hsint : IntervalIntegrable (formIntegrand n r s s)
      volume (0 : ℝ) Real.pi := (hs.2 s hs.1).1
  have hsvint : IntervalIntegrable (formIntegrand n r s v)
      volume (0 : ℝ) Real.pi := (hs.2 v hv).1
  have hvint : IntervalIntegrable (formIntegrand n r v v)
      volume (0 : ℝ) Real.pi := positiveTest_self_energy_integrable n hn r
  have hperturb : ∀ a : ℝ,
      0 ≤ originalWeakForm n r s s +
        2 * a * originalWeakForm n r s v +
        a ^ 2 * originalWeakForm n r v v := by
    intro a
    rw [← originalWeakForm_perturb_expansion n r s v a hsint hsvint hvint]
    exact originalWeakForm_self_nonneg n hn r (perturbState s v a)
  have hpositive : 0 < originalWeakForm n r s s :=
    DFL.Probability.energy_response_pos_of_positive_test
      (V := Unit)
      (originalWeakForm n r s s)
      (fun _ => originalWeakForm n r s v)
      (fun _ => originalWeakForm n r v v)
      hq
      (fun _ => hqv)
      (fun _ a => hperturb a)
      ⟨(), hforcing⟩
  have heqSelf := (hs.2 s hs.1).2.2
  rw [← originalSourcePairing_eq_denominator n hn r s]
  rw [← heqSelf]
  exact hpositive

/-- Energy Cauchy for the original weighted angular form, evaluated on
an actual weak solution and any admissible test whose self-energy is
integrable.  The conclusion concerns the original source pairing and
the original coefficient denominator, with no sign assumption on `g`. -/
theorem weak_solution_energy_cauchy
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ)
    (s v : AngularState)
    (hs : OriginalWeakGCISolution n r s)
    (hv : AngularEnergyDomain n v)
    (hvint : IntervalIntegrable (formIntegrand n r v v)
      volume (0 : ℝ) Real.pi) :
    (originalSourcePairing n r v) ^ 2 ≤
      originalGCIDenominator n r s * originalWeakForm n r v v := by
  let E := originalWeakForm n r s s
  let F := originalWeakForm n r s v
  let T := originalWeakForm n r v v
  have hE : 0 ≤ E := originalWeakForm_self_nonneg n hn r s
  have hT : 0 ≤ T := originalWeakForm_self_nonneg n hn r v
  have hsint : IntervalIntegrable (formIntegrand n r s s)
      volume (0 : ℝ) Real.pi := (hs.2 s hs.1).1
  have hsvint : IntervalIntegrable (formIntegrand n r s v)
      volume (0 : ℝ) Real.pi := (hs.2 v hv).1
  have hquad (a : ℝ) : 0 ≤ E + 2 * a * F + a ^ 2 * T := by
    rw [← originalWeakForm_perturb_expansion n r s v a
      hsint hsvint hvint]
    exact originalWeakForm_self_nonneg n hn r (perturbState s v a)
  have hEF : F ^ 2 ≤ E * T := by
    rcases lt_or_eq_of_le hT with hTpos | hTzero
    · let t := F / T
      have ht : t * T = F := by
        dsimp [t]
        exact div_mul_cancel₀ _ hTpos.ne'
      have hq := hquad (-t)
      have ht2 : t ^ 2 * T = t * F := by
        calc
          _ = t * (t * T) := by ring
          _ = t * F := by rw [ht]
      have hFE : t * F ≤ E := by
        nlinarith
      have hmul := mul_le_mul_of_nonneg_right hFE hTpos.le
      have hprod : t * F * T = F ^ 2 := by
        calc
          _ = (t * T) * F := by ring
          _ = F ^ 2 := by rw [ht]; ring
      nlinarith
    · have hFzero : F = 0 := by
        by_contra hFne
        let a := -(E + 1) / F
        have ha : a * F = -(E + 1) := by
          dsimp [a]
          exact div_mul_cancel₀ _ hFne
        have hq := hquad a
        rw [← hTzero] at hq
        have hcross : 2 * a * F = 2 * (a * F) := by ring
        rw [hcross, ha] at hq
        nlinarith
      rw [hFzero, ← hTzero]
      simp
  have hself : E = originalGCIDenominator n r s := by
    calc
      E = originalSourcePairing n r s := (hs.2 s hs.1).2.2
      _ = originalGCIDenominator n r s :=
        originalSourcePairing_eq_denominator n hn r s
  have hforcing : F = originalSourcePairing n r v :=
    (hs.2 v hv).2.2
  simpa only [hself, hforcing, T] using hEF

end

end DFL.GCI
