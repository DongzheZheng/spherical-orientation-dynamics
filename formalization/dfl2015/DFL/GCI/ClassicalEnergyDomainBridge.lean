import DFL.GCI.ClassicalH10Closure
import DFL.GCI.DirichletWeakDerivative
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Exact correspondence with the original angular energy domain.
The classical `H¹₀` condition is the genuine smooth function/derivative
closure. A continuous representative with both zero traces is retained
when returning a pointwise angular state; the extra singular `L²`
condition remains an explicit condition on the original `g`. -/

namespace DFL.GCI
open MeasureTheory Set
open scoped Interval Topology ContDiff
noncomputable section

def angularPotentialRepresentative (n : ℕ) (s : AngularState) (θ : ℝ) : ℝ :=
  ((n : ℝ) - 2) * Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) * s.g θ

/-- The actual scaled function, rather than an unrelated `L²` class. -/
def scaledSingularRepresentative (n : ℕ) (s : AngularState) (θ : ℝ) : ℝ :=
  scaledFunction n s θ / Real.sin θ

/-- The conventional Dirichlet completion paired with its continuous
zero-trace representative and actual derivative. -/
def ClassicalDirichletRepresentative (n : ℕ) (s : AngularState) : Prop :=
  ∃ u q : AngularL2,
    (u, q) ∈ classicalH10Graph ∧
    (u : ℝ → ℝ) =ᵐ[angularLebesgue] scaledFunction n s ∧
    (q : ℝ → ℝ) =ᵐ[angularLebesgue] s.scaledDerivative ∧
    ContinuousOn (scaledFunction n s) (Icc 0 Real.pi) ∧
    scaledFunction n s 0 = 0 ∧ scaledFunction n s Real.pi = 0

theorem energyDomain_classicalDirichletRepresentative (n : ℕ) (s : AngularState)
    (hs : AngularEnergyDomain n s) : ClassicalDirichletRepresentative n s := by
  let q := stateDerivativeL2 n s hs
  let u := (energyDomain_scaledFunction_memLp_two n s hs).toLp (scaledFunction n s)
  have hq : (q : ℝ → ℝ) =ᵐ[angularLebesgue] s.scaledDerivative :=
    stateDerivativeL2_ae n s hs
  have hu : (u : ℝ → ℝ) =ᵐ[angularLebesgue] scaledFunction n s := MemLp.coeFn_toLp _
  have hup : u = l2PrimitiveCLM q := by
    apply Lp.ext
    filter_upwards [hu, l2PrimitiveCLM_ae q, angularLebesgue_ae_interior] with θ huθ hpθ hθ
    rw [huθ, hpθ, stateDerivativeL2_primitive n s hs θ ⟨hθ.1.le, hθ.2.le⟩]
    exact moment_reconstruction n s hs θ ⟨hθ.1.le, hθ.2.le⟩
  have hqm : l2Mean q = 0 := by
    rw [l2Mean_eq_integral, integral_congr_ae hq]
    simpa only [angularLebesgue, ← intervalIntegral.integral_of_le Real.pi_pos.le] using
      hs.2.2.2.1
  exact ⟨u, q, (mem_classicalH10Graph_iff u q).mpr ⟨hup, hqm⟩, hu, hq,
    energyDomain_scaledFunction_continuousOn n s hs,
    (energyDomain_scaledFunction_zero_traces n s hs).1,
    (energyDomain_scaledFunction_zero_traces n s hs).2⟩

/-- Passing from `L²` classes back to a pointwise state uses the continuous
representative; changing isolated values of `g` is not silently accepted. -/
theorem classicalDirichletRepresentative_reconstruction (n : ℕ) (s : AngularState)
    (hs : ClassicalDirichletRepresentative n s) :
    ∀ θ ∈ Icc 0 Real.pi,
      scaledFunction n s θ = ∫ x in (0 : ℝ)..θ, s.scaledDerivative x := by
  rcases hs with ⟨u, q, hgraph, hu, hq, hc, _, _⟩
  rcases (mem_classicalH10Graph_iff u q).mp hgraph with ⟨hup, _⟩
  have hae : scaledFunction n s =ᵐ[angularLebesgue] l2Primitive q := by
    exact hu.symm.trans (hup ▸ l2PrimitiveCLM_ae q)
  have hae' : scaledFunction n s =ᵐ[volume.restrict (Icc 0 Real.pi)] l2Primitive q := by
    simpa only [angularLebesgue, restrict_Ioc_eq_restrict_Icc] using hae
  have hpoint := Measure.eqOn_of_ae_eq hae' hc (l2Primitive_continuousOn q) (by
    simp [interior_Icc, closure_Ioo Real.pi_pos.ne])
  intro θ hθ
  rw [hpoint hθ]
  exact l2Primitive_congr_test q s.scaledDerivative hq hθ

theorem angularPotentialRepresentative_eq_scaledSingular (n : ℕ) (s : AngularState) :
    angularPotentialRepresentative n s =ᵐ[angularLebesgue]
      fun θ => ((n : ℝ) - 2) * scaledSingularRepresentative n s θ := by
  filter_upwards [angularLebesgue_ae_interior] with θ hθ
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have he : ((n : ℝ) - 4) / 2 + 1 = halfPower n := by unfold halfPower; ring
  have hp : Real.rpow (Real.sin θ) (halfPower n) =
      Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) * Real.sin θ := by
    rw [← he]
    exact Real.rpow_add_one hsin.ne' _
  unfold angularPotentialRepresentative scaledSingularRepresentative scaledFunction
  rw [hp]
  field_simp [hsin.ne']

/-- Exact all-dimensional correspondence with the original potential
integrability condition left in its original scaled form. -/
theorem angularEnergyDomain_iff_classicalH10_potential (n : ℕ) (s : AngularState) :
    AngularEnergyDomain n s ↔
      ClassicalDirichletRepresentative n s ∧
      MemLp (angularPotentialRepresentative n s) 2 angularLebesgue := by
  constructor
  · intro hs
    refine ⟨energyDomain_classicalDirichletRepresentative n s hs, ?_⟩
    have hu := (energyDomain_scaledFunction_memLp_two n s hs).aestronglyMeasurable
    have hsin := Real.continuous_sin.aestronglyMeasurable (μ := angularLebesgue)
    have hsing : AEStronglyMeasurable (scaledSingularRepresentative n s) angularLebesgue :=
      hu.div₀ hsin
    have hpot : AEStronglyMeasurable (angularPotentialRepresentative n s) angularLebesgue :=
      (aestronglyMeasurable_congr (angularPotentialRepresentative_eq_scaledSingular n s)).mpr
        (hsing.const_mul ((n : ℝ) - 2))
    apply (memLp_two_iff_integrable_sq hpot).mpr
    simpa only [angularPotentialRepresentative, angularLebesgue,
      Set.uIoc_of_le Real.pi_pos.le] using hs.2.2.2.2.1
  · rintro ⟨hrep, hpot⟩
    rcases hrep with ⟨u, q, hg, hu, hq, hc, hzero, hpi⟩
    have hrep : ClassicalDirichletRepresentative n s := ⟨u, q, hg, hu, hq, hc, hzero, hpi⟩
    have hsq : MemLp s.scaledDerivative 2 angularLebesgue := (memLp_congr_ae hq).mp (Lp.memLp q)
    have hqint : IntervalIntegrable s.scaledDerivative volume (0 : ℝ) Real.pi := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr
      exact hsq.integrable (by norm_num)
    have hq2 : IntervalIntegrable (fun θ => (s.scaledDerivative θ) ^ 2)
        volume (0 : ℝ) Real.pi := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr
      exact hsq.integrable_sq
    refine ⟨hqint, hq2, classicalDirichletRepresentative_reconstruction n s hrep, ?_, ?_⟩
    · have hqm := ((mem_classicalH10Graph_iff u q).mp hg).2
      rw [l2Mean_eq_integral, integral_congr_ae hq] at hqm
      simpa only [angularLebesgue, ← intervalIntegral.integral_of_le Real.pi_pos.le] using hqm
    · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr
      exact hpot.integrable_sq

/-- For `n≥3`, the additional original energy condition is precisely the
singular `L²` condition on the same scaled Dirichlet representative. -/
theorem angularEnergyDomain_iff_classicalH10_singular (n : ℕ) (hn : 3 ≤ n) (s : AngularState) :
    AngularEnergyDomain n s ↔
      ClassicalDirichletRepresentative n s ∧
      MemLp (scaledSingularRepresentative n s) 2 angularLebesgue := by
  rw [angularEnergyDomain_iff_classicalH10_potential]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnz : (n : ℝ) - 2 ≠ 0 := by linarith
  have he := angularPotentialRepresentative_eq_scaledSingular n s
  constructor
  · rintro ⟨hrep, hp⟩
    have hp' := (memLp_congr_ae he).mp hp
    refine ⟨hrep, ?_⟩
    have hsm := hp'.const_mul (((n : ℝ) - 2)⁻¹)
    simpa [← mul_assoc, hnz] using hsm
  · rintro ⟨hrep, hs⟩
    exact ⟨hrep, (memLp_congr_ae he).mpr (hs.const_mul ((n : ℝ) - 2))⟩

end
end DFL.GCI
