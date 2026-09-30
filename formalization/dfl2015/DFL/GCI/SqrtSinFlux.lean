import DFL.GCI.AngularMomentThree

/-!
# Absolute continuity of the ambient-three angular flux

The source `H¹₀` representative is multiplied by a flux containing
`(sin θ)^(1/2)`.  The flux is not `C¹` at `0` or `π`, but its interior
derivative has an integrable square-root singularity.  This file supplies
the absolute continuity needed for the exact weak integration by parts.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

private def sqrtSin (θ : ℝ) : ℝ :=
  Real.sin θ ^ (1 / 2 : ℝ)

private def sqrtSinDerivative (θ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.sin θ ^ (-(1 / 2 : ℝ)) * Real.cos θ)

private theorem sqrtSinDerivative_integrable :
    IntervalIntegrable sqrtSinDerivative volume (0 : ℝ) Real.pi := by
  simpa only [sqrtSinDerivative] using
    threeD_singular_derivative_integrable.const_mul (1 / 2 : ℝ)

private theorem sqrtSin_hasDerivAt (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    HasDerivAt sqrtSin (sqrtSinDerivative θ) θ := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have h := (Real.hasDerivAt_sin θ).rpow_const
    (p := (1 / 2 : ℝ)) (Or.inl hsin.ne')
  convert h using 1
  simp only [sqrtSinDerivative]
  have hp : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by ring
  rw [hp]
  ring

private theorem sqrtSin_eq_integral (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    sqrtSin θ = ∫ t in (0 : ℝ)..θ, sqrtSinDerivative t := by
  have hcont : Continuous sqrtSin := by
    unfold sqrtSin
    exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).comp
      Real.continuous_sin
  have hsub : Set.uIcc (0 : ℝ) θ ⊆ Set.uIcc (0 : ℝ) Real.pi := by
    rw [Set.uIcc_of_le hθ.1, Set.uIcc_of_le Real.pi_pos.le]
    intro x hx
    exact ⟨hx.1, hx.2.trans hθ.2⟩
  have hint : IntervalIntegrable sqrtSinDerivative volume (0 : ℝ) θ :=
    sqrtSinDerivative_integrable.mono_set hsub
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1
    hcont.continuousOn
    (fun x hx => sqrtSin_hasDerivAt x
      ⟨hx.1, hx.2.trans_le hθ.2⟩) hint
  have hzero : sqrtSin 0 = 0 := by simp [sqrtSin, Real.sin_zero]
  simpa [hzero] using hFTC.symm

theorem sqrtSin_AC :
    AbsolutelyContinuousOnInterval sqrtSin (0 : ℝ) Real.pi := by
  have hprimitive : AbsolutelyContinuousOnInterval
      (fun θ : ℝ => ∫ t in (0 : ℝ)..θ, sqrtSinDerivative t)
      (0 : ℝ) Real.pi :=
    sqrtSinDerivative_integrable.absolutelyContinuousOnInterval_intervalIntegral
      (by simp [Real.pi_pos.le])
  rw [absolutelyContinuousOnInterval_iff] at hprimitive ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hprimitive ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlength
  have h := hδprop E hE hlength
  calc
    (∑ i ∈ Finset.range E.1, dist (sqrtSin (E.2 i).1) (sqrtSin (E.2 i).2)) =
        ∑ i ∈ Finset.range E.1,
          dist (∫ t in (0 : ℝ)..(E.2 i).1, sqrtSinDerivative t)
            (∫ t in (0 : ℝ)..(E.2 i).2, sqrtSinDerivative t) := by
      apply Finset.sum_congr rfl
      intro i hi
      have ha : (E.2 i).1 ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using (hE.1 i hi).1
      have hb : (E.2 i).2 ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using (hE.1 i hi).2
      rw [sqrtSin_eq_integral _ ha, sqrtSin_eq_integral _ hb]
    _ < ε := h

theorem sqrtSinFlux_AC (r : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun θ : ℝ => Real.exp (r * Real.cos θ) *
        Real.rpow (Real.sin θ) (1 / 2 : ℝ) * Real.cos θ)
      (0 : ℝ) Real.pi := by
  have hsmooth : ContDiff ℝ 1
      (fun θ : ℝ => Real.exp (r * Real.cos θ) * Real.cos θ) := by
    fun_prop
  obtain ⟨K, hK⟩ :=
    hsmooth.contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc (0 : ℝ) Real.pi) isCompact_Icc
  have hKs : LipschitzOnWith K
      (fun θ : ℝ => Real.exp (r * Real.cos θ) * Real.cos θ)
      (Set.uIcc (0 : ℝ) Real.pi) := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hK
  have hAC := hKs.absolutelyContinuousOnInterval.mul sqrtSin_AC
  convert hAC using 1
  funext θ
  simp only [Pi.mul_apply, sqrtSin, Real.rpow_eq_pow]
  ring

/-- Exact `n=3` specialization of the flux used by the general moment
identity, with no endpoint differentiability assumption. -/
theorem momentFlux_three_AC (r : ℝ) :
    AbsolutelyContinuousOnInterval (momentFlux 3 r) (0 : ℝ) Real.pi := by
  convert sqrtSinFlux_AC r using 1
  funext θ
  norm_num [momentFlux, halfPower]

end

end DFL.GCI
