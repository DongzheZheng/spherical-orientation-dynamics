import DFL.GCI.GraphDomainBridge

/-! The conventional distributional derivative identity satisfied by the
source's scaled Dirichlet representative. This file proves the actual
`L²` function/derivative pair and zero traces. It does not assert an
equivalence to a Sobolev space absent from the pinned mathlib version. -/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

theorem energyDomain_scaledFunction_continuousOn
    (n : ℕ) (s : AngularState) (hs : AngularEnergyDomain n s) :
    ContinuousOn (scaledFunction n s) (Set.Icc (0 : ℝ) Real.pi) := by
  apply (momentPrimitive_continuousOn n s hs).congr
  intro θ hθ
  exact moment_reconstruction n s hs θ hθ

theorem energyDomain_scaledFunction_memLp_two
    (n : ℕ) (s : AngularState) (hs : AngularEnergyDomain n s) :
    MemLp (scaledFunction n s) 2 angularLebesgue := by
  have hu := energyDomain_scaledFunction_continuousOn n s hs
  have has : AEStronglyMeasurable (scaledFunction n s) angularLebesgue :=
    (hu.mono (by intro θ hθ; exact ⟨hθ.1.le, hθ.2⟩)).aestronglyMeasurable measurableSet_Ioc
  apply (memLp_two_iff_integrable_sq has).2
  exact ((hu.pow 2).intervalIntegrable_of_Icc Real.pi_pos.le).1

theorem energyDomain_scaledFunction_zero_traces
    (n : ℕ) (s : AngularState) (hs : AngularEnergyDomain n s) :
    scaledFunction n s 0 = 0 ∧ scaledFunction n s Real.pi = 0 := by
  constructor
  · unfold scaledFunction
    rw [moment_reconstruction n s hs 0 ⟨le_rfl, Real.pi_pos.le⟩]
    simp [momentPrimitive]
  · unfold scaledFunction
    rw [moment_reconstruction n s hs Real.pi ⟨Real.pi_pos.le, le_rfl⟩]
    exact hs.2.2.2.1

/-- The original source representative's `q` is its distributional weak
derivative. The zero Dirichlet traces remove the boundary terms even for
tests whose support reaches either endpoint. In particular this applies
to every conventional compactly supported smooth test on `(0,π)`. -/
theorem energyDomain_distributional_derivative
    (n : ℕ) (s : AngularState) (hs : AngularEnergyDomain n s)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) :
    (∫ θ in (0 : ℝ)..Real.pi, scaledFunction n s θ * deriv φ θ) =
      -(∫ θ in (0 : ℝ)..Real.pi, s.scaledDerivative θ * φ θ) := by
  have hφAC : AbsolutelyContinuousOnInterval φ 0 Real.pi := by
    obtain ⟨K, hK⟩ := hφ.contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc (0 : ℝ) Real.pi) isCompact_Icc
    apply (show LipschitzOnWith K φ (Set.uIcc (0 : ℝ) Real.pi) from ?_).absolutelyContinuousOnInterval
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hK
  have hqae := hs.1.ae_hasDerivAt_integral
  have hpair :
      (∫ θ in (0 : ℝ)..Real.pi, φ θ * deriv (momentPrimitive s) θ) =
      ∫ θ in (0 : ℝ)..Real.pi, s.scaledDerivative θ * φ θ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hqae] with θ hq hθ
    have hθIoc : θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
      simpa only [Set.uIoc_of_le Real.pi_pos.le] using hθ
    have hθ' : θ ∈ Set.uIcc (0 : ℝ) Real.pi := by
      rw [Set.uIcc_of_le Real.pi_pos.le]
      exact ⟨hθIoc.1.le, hθIoc.2⟩
    have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) Real.pi := by
      simp [Real.pi_pos.le]
    have hderiv : deriv (momentPrimitive s) θ = s.scaledDerivative θ :=
      (hq hθ' 0 h0).deriv
    rw [hderiv]
    ring
  have hu0 : momentPrimitive s 0 = 0 := by simp [momentPrimitive]
  have huπ : momentPrimitive s Real.pi = 0 := hs.2.2.2.1
  have hibp := hφAC.integral_mul_deriv_eq_deriv_mul (momentPrimitive_AC n s hs)
  have hibp' :
      (∫ θ in (0 : ℝ)..Real.pi, φ θ * deriv (momentPrimitive s) θ) =
        -(∫ θ in (0 : ℝ)..Real.pi, deriv φ θ * momentPrimitive s θ) := by
    simpa only [hu0, huπ, mul_zero, sub_zero, zero_sub] using hibp
  have hrec :
      (∫ θ in (0 : ℝ)..Real.pi, scaledFunction n s θ * deriv φ θ) =
        ∫ θ in (0 : ℝ)..Real.pi, deriv φ θ * momentPrimitive s θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ' : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
      simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
    dsimp only
    unfold scaledFunction
    rw [moment_reconstruction n s hs θ hθ']
    ring
  rw [hrec]
  rw [hpair] at hibp'
  linarith

end
end DFL.GCI
