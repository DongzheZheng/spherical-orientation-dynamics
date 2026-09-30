import DFL.GCI.AngularCauchy2D
import DFL.Probability.PiconeAC

/-!
# Applying the nonsingular Picone identity to the original 2D GCI weak space

The barrier is the explicitly proved positive strict supersolution from
`AngularBarrier2D`.  This file transports its pointwise inequality
through the actual absolutely continuous representative of the original
angular weak space.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def twoDBarrierProfile (r : ℝ) : ℝ → ℝ :=
  twoDBarrier r (twoDBarrierEpsilon r)

def twoDLogSlope (r θ : ℝ) : ℝ :=
  deriv (twoDBarrierProfile r) θ / twoDBarrierProfile r θ

def twoDWeight (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ)

private theorem twoDBarrierProfile_contDiff (r : ℝ) :
    ContDiff ℝ 2 (twoDBarrierProfile r) := by
  unfold twoDBarrierProfile twoDBarrier twoDGround twoDLift
  fun_prop

private theorem twoDWeight_contDiff (r : ℝ) :
    ContDiff ℝ 1 (twoDWeight r) := by
  unfold twoDWeight
  fun_prop

theorem twoDLogSlope_continuousOn (r : ℝ) (hr : 0 < r) :
    ContinuousOn (twoDLogSlope r)
      (Set.Icc (0 : ℝ) Real.pi) := by
  have hphi2 := twoDBarrierProfile_contDiff r
  have hphi2' : ContDiff ℝ (1 + 1) (twoDBarrierProfile r) :=
    hphi2
  have hderiv : Continuous (deriv (twoDBarrierProfile r)) :=
    hphi2'.deriv'.continuous
  have hphi : Continuous (twoDBarrierProfile r) := hphi2.continuous
  have hne (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
      twoDBarrierProfile r θ ≠ 0 :=
    (twoDBarrier_pos r hr θ hθ).ne'
  unfold twoDLogSlope
  exact hderiv.continuousOn.div hphi.continuousOn hne

theorem twoDWeightedLogSlope_AC (r : ℝ) (hr : 0 < r) :
    AbsolutelyContinuousOnInterval
      (fun θ => twoDWeight r θ * twoDLogSlope r θ)
      (0 : ℝ) Real.pi := by
  have hphi2 := twoDBarrierProfile_contDiff r
  have hphi2' : ContDiff ℝ (1 + 1) (twoDBarrierProfile r) :=
    hphi2
  have hderiv : ContDiff ℝ 1
      (deriv (twoDBarrierProfile r)) := hphi2'.deriv'
  have hphi1 : ContDiff ℝ 1 (twoDBarrierProfile r) :=
    hphi2.of_le (by norm_num)
  have hne (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
      twoDBarrierProfile r θ ≠ 0 :=
    (twoDBarrier_pos r hr θ hθ).ne'
  have hA : ContDiffOn ℝ 1 (twoDLogSlope r)
      (Set.Icc (0 : ℝ) Real.pi) := by
    unfold twoDLogSlope
    exact hderiv.contDiffOn.div hphi1.contDiffOn hne
  have hpA : ContDiffOn ℝ 1
      (fun θ => twoDWeight r θ * twoDLogSlope r θ)
      (Set.Icc (0 : ℝ) Real.pi) :=
    (twoDWeight_contDiff r).contDiffOn.mul hA
  obtain ⟨K, hK⟩ :=
    hpA.exists_lipschitzOnWith (by norm_num)
      (convex_Icc (0 : ℝ) Real.pi) isCompact_Icc
  have hKu : LipschitzOnWith K
      (fun θ => twoDWeight r θ * twoDLogSlope r θ)
      (Set.uIcc (0 : ℝ) Real.pi) := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hK
  exact hKu.absolutelyContinuousOnInterval

def twoDBarrierRemainder (r θ : ℝ) : ℝ :=
  -(deriv (fun y => twoDWeight r y * twoDLogSlope r y) θ) -
    twoDWeight r θ * (twoDLogSlope r θ) ^ 2 -
    twoDWeight r θ

/-- The Picone remainder is exactly the angular weight times the
relative strict supersolution residual. -/
theorem twoDBarrierRemainder_eq
    (r : ℝ) (hr : 0 < r)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    twoDBarrierRemainder r θ =
      twoDWeight r θ *
        (twoDOperatorValue r θ
          (deriv (twoDBarrierProfile r) θ)
          (deriv (deriv (twoDBarrierProfile r)) θ) -
          twoDBarrierProfile r θ) /
        twoDBarrierProfile r θ := by
  let φ := twoDBarrierProfile r
  have hφne : φ θ ≠ 0 :=
    (twoDBarrier_pos r hr θ hθ).ne'
  have hφ2 : ContDiff ℝ 2 φ := twoDBarrierProfile_contDiff r
  have hφd : HasDerivAt φ (deriv φ θ) θ :=
    (hφ2.differentiable (by norm_num) θ).hasDerivAt
  have hφdd : HasDerivAt (deriv φ)
      (deriv (deriv φ) θ) θ :=
    (hφ2.differentiable_deriv_two θ).hasDerivAt
  have hpd : HasDerivAt (twoDWeight r)
      (-r * Real.sin θ * twoDWeight r θ) θ := by
    have harg : HasDerivAt (fun x : ℝ => r * Real.cos x)
        (-r * Real.sin θ) θ := by
      convert (Real.hasDerivAt_cos θ).const_mul r using 1
      ring
    convert harg.exp using 1
    unfold twoDWeight
    ring
  have hAd : HasDerivAt (twoDLogSlope r)
      ((deriv (deriv φ) θ * φ θ -
          deriv φ θ * deriv φ θ) / (φ θ) ^ 2) θ := by
    unfold twoDLogSlope
    exact hφdd.div hφd hφne
  have hpAd := hpd.mul hAd
  have hpAderiv :
      deriv (fun y => twoDWeight r y * twoDLogSlope r y) θ =
        (-r * Real.sin θ * twoDWeight r θ) *
          twoDLogSlope r θ +
        twoDWeight r θ *
          ((deriv (deriv φ) θ * φ θ -
            deriv φ θ * deriv φ θ) / (φ θ) ^ 2) := by
    exact hpAd.deriv
  unfold twoDBarrierRemainder
  rw [hpAderiv]
  unfold twoDLogSlope twoDOperatorValue
  dsimp [φ, twoDBarrierProfile]
  have hne : twoDBarrier r (twoDBarrierEpsilon r) θ ≠ 0 := hφne
  field_simp [hne]
  ring

theorem twoDBarrierRemainder_pos
    (r : ℝ) (hr : 0 < r)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    0 < twoDBarrierRemainder r θ := by
  rw [twoDBarrierRemainder_eq r hr θ hθ]
  have hp : 0 < twoDWeight r θ := Real.exp_pos _
  have hφ : 0 < twoDBarrierProfile r θ :=
    twoDBarrier_pos r hr θ hθ
  have hL := twoDBarrier_strict_supersolution r hr θ hθ
  exact div_pos (mul_pos hp (sub_pos.mpr hL)) hφ

theorem twoDBarrierRemainder_continuousOn
    (r : ℝ) (hr : 0 < r) :
    ContinuousOn (twoDBarrierRemainder r)
      (Set.Icc (0 : ℝ) Real.pi) := by
  let φ := twoDBarrierProfile r
  have hφ2 : ContDiff ℝ 2 φ := twoDBarrierProfile_contDiff r
  have hφ2' : ContDiff ℝ (1 + 1) φ := hφ2
  have hφd1 : ContDiff ℝ 1 (deriv φ) := hφ2'.deriv'
  have hφd0 : Continuous (deriv φ) := hφd1.continuous
  have hφdd : Continuous (deriv (deriv φ)) := by
    have hφd1' : ContDiff ℝ (0 + 1) (deriv φ) := hφd1
    exact hφd1'.deriv'.continuous
  have hφ0 : Continuous φ := hφ2.continuous
  have hp0 : Continuous (twoDWeight r) := by
    unfold twoDWeight
    fun_prop
  have hL : Continuous
      (fun θ => twoDOperatorValue r θ
        (deriv φ θ) (deriv (deriv φ) θ) - φ θ) := by
    unfold twoDOperatorValue
    exact (hφdd.neg.add
      ((continuous_const.mul Real.continuous_sin).mul hφd0)).sub hφ0
  have hne (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
      φ θ ≠ 0 := (twoDBarrier_pos r hr θ hθ).ne'
  have hquot : ContinuousOn
      (fun θ =>
        twoDWeight r θ *
          (twoDOperatorValue r θ
            (deriv φ θ) (deriv (deriv φ) θ) - φ θ) /
          φ θ)
      (Set.Icc (0 : ℝ) Real.pi) :=
    (hp0.mul hL).continuousOn.div hφ0.continuousOn hne
  apply hquot.congr
  intro θ hθ
  dsimp only
  exact twoDBarrierRemainder_eq r hr θ hθ

theorem twoDPrimitive_deriv_ae
    (s : AngularState) (hs : AngularEnergyDomain 2 s) :
    ∀ᵐ θ ∂volume.restrict (Set.uIoc (0 : ℝ) Real.pi),
      deriv (twoDPrimitive s) θ = s.scaledDerivative θ := by
  have hqae := hs.1.ae_hasDerivAt_integral
  filter_upwards [ae_restrict_of_ae hqae,
    ae_restrict_mem measurableSet_uIoc] with θ hq hθ
  have hθIoc : θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
    simpa only [Set.uIoc_of_le Real.pi_pos.le] using hθ
  have hθIcc : θ ∈ Set.uIcc (0 : ℝ) Real.pi := by
    rw [Set.uIcc_of_le Real.pi_pos.le]
    exact ⟨hθIoc.1.le, hθIoc.2⟩
  have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) Real.pi := by
    simp [Real.pi_pos.le]
  exact (hq hθIcc 0 h0).deriv

theorem twoDPrimitive_nonzero_point_of_weak_solution
    (r : ℝ) (s : AngularState)
    (hs : OriginalWeakGCISolution 2 r s) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      twoDPrimitive s θ ≠ 0 := by
  by_contra hnone
  have hzero (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
      twoDPrimitive s θ = 0 := by
    by_contra hne
    exact hnone ⟨θ, hθ, hne⟩
  have hDzero : originalGCIDenominator 2 r s = 0 := by
    rw [twoD_denominator_formula]
    calc
      (∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (r * Real.cos θ) * Real.sin θ * s.g θ) =
          ∫ θ in (0 : ℝ)..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        have hθIcc : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
          simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
        dsimp only
        rw [twoD_reconstruction s hs.1 θ hθIcc,
          hzero θ hθIcc]
        ring
      _ = 0 := by simp
  have hDpos := weak_solution_denominator_pos 2 (by omega) r s hs
  linarith

theorem twoDBarrier_remainder_mass_pos_point
    (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution 2 r s) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      0 < twoDBarrierRemainder r θ * (twoDPrimitive s θ) ^ 2 := by
  obtain ⟨θ, hθ, hu⟩ :=
    twoDPrimitive_nonzero_point_of_weak_solution r s hs
  refine ⟨θ, hθ, ?_⟩
  exact mul_pos (twoDBarrierRemainder_pos r hr θ hθ)
    (sq_pos_of_ne_zero hu)

private theorem twoD_picone_integrabilities
    (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution 2 r s) :
    IntervalIntegrable
        (fun θ => twoDWeight r θ * (deriv (twoDPrimitive s) θ) ^ 2)
        volume (0 : ℝ) Real.pi ∧
    IntervalIntegrable
        (fun θ => twoDWeight r θ *
          (deriv (twoDPrimitive s) θ -
            twoDLogSlope r θ * twoDPrimitive s θ) ^ 2)
        volume (0 : ℝ) Real.pi ∧
    IntervalIntegrable
        (fun θ =>
          (-(deriv (fun y => twoDWeight r y * twoDLogSlope r y) θ) -
            twoDWeight r θ * (twoDLogSlope r θ) ^ 2) *
              (twoDPrimitive s θ) ^ 2)
        volume (0 : ℝ) Real.pi ∧
    IntervalIntegrable
        (fun θ => twoDWeight r θ * (twoDPrimitive s θ) ^ 2)
        volume (0 : ℝ) Real.pi ∧
    IntervalIntegrable
        (fun θ => twoDBarrierRemainder r θ *
          (twoDPrimitive s θ) ^ 2)
        volume (0 : ℝ) Real.pi := by
  let I := Set.Icc (0 : ℝ) Real.pi
  have hu : ContinuousOn (twoDPrimitive s) I := by
    change ContinuousOn (twoDPrimitive s) (Set.Icc (0 : ℝ) Real.pi)
    simpa only [Set.uIcc_of_le Real.pi_pos.le]
      using (twoDPrimitive_AC s hs.1).continuousOn
  have hp : ContinuousOn (twoDWeight r) I :=
    (twoDWeight_contDiff r).continuous.continuousOn
  have hpU : ContinuousOn (twoDWeight r)
      (Set.uIcc (0 : ℝ) Real.pi) := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hp
  have hA : ContinuousOn (twoDLogSlope r) I :=
    twoDLogSlope_continuousOn r hr
  have hR : ContinuousOn (twoDBarrierRemainder r) I :=
    twoDBarrierRemainder_continuousOn r hr
  have hq : IntervalIntegrable s.scaledDerivative volume
      (0 : ℝ) Real.pi := hs.1.1
  have hq2 : IntervalIntegrable
      (fun θ : ℝ => (s.scaledDerivative θ) ^ 2)
      volume (0 : ℝ) Real.pi := hs.1.2.1
  have hEp : IntervalIntegrable
      (fun θ => twoDWeight r θ * (s.scaledDerivative θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    hq2.continuousOn_mul hpU
  have hDeriv := twoDPrimitive_deriv_ae s hs.1
  have hE : IntervalIntegrable
      (fun θ => twoDWeight r θ * (deriv (twoDPrimitive s) θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
    apply hEp.congr_ae
    filter_upwards [hDeriv] with θ hd
    rw [hd]
  have hCoeff : ContinuousOn
      (fun θ => 2 * twoDWeight r θ *
        twoDLogSlope r θ * twoDPrimitive s θ) I := by
    exact (((continuousOn_const.mul hp).mul hA).mul hu)
  have hCoeffU : ContinuousOn
      (fun θ => 2 * twoDWeight r θ *
        twoDLogSlope r θ * twoDPrimitive s θ)
      (Set.uIcc (0 : ℝ) Real.pi) := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hCoeff
  have hCross : IntervalIntegrable
      (fun θ => (2 * twoDWeight r θ *
        twoDLogSlope r θ * twoDPrimitive s θ) *
          s.scaledDerivative θ)
      volume (0 : ℝ) Real.pi :=
    hq.continuousOn_mul hCoeffU
  have hLast : IntervalIntegrable
      (fun θ => twoDWeight r θ *
        (twoDLogSlope r θ * twoDPrimitive s θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    (hp.mul ((hA.mul hu).pow 2)).intervalIntegrable_of_Icc
      Real.pi_pos.le
  have hQbase : IntervalIntegrable
      (fun θ => twoDWeight r θ *
        (s.scaledDerivative θ -
          twoDLogSlope r θ * twoDPrimitive s θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
    apply ((hEp.sub hCross).add hLast).congr
    intro θ _
    dsimp only
    ring
  have hQ : IntervalIntegrable
      (fun θ => twoDWeight r θ *
        (deriv (twoDPrimitive s) θ -
          twoDLogSlope r θ * twoDPrimitive s θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
    apply hQbase.congr_ae
    filter_upwards [hDeriv] with θ hd
    rw [hd]
  have hL2 : IntervalIntegrable
      (fun θ => twoDWeight r θ * (twoDPrimitive s θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    (hp.mul (hu.pow 2)).intervalIntegrable_of_Icc Real.pi_pos.le
  have hRint : IntervalIntegrable
      (fun θ => twoDBarrierRemainder r θ *
        (twoDPrimitive s θ) ^ 2)
      volume (0 : ℝ) Real.pi :=
    (hR.mul (hu.pow 2)).intervalIntegrable_of_Icc Real.pi_pos.le
  have hV : IntervalIntegrable
      (fun θ =>
        (-(deriv (fun y => twoDWeight r y * twoDLogSlope r y) θ) -
          twoDWeight r θ * (twoDLogSlope r θ) ^ 2) *
            (twoDPrimitive s θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
    have hsum := hRint.add hL2
    apply hsum.congr
    intro θ _
    dsimp only
    unfold twoDBarrierRemainder
    ring
  exact ⟨hE, hQ, hV, hL2, hRint⟩

theorem twoD_energy_formula (r : ℝ) (s : AngularState) :
    originalWeakForm 2 r s s =
      ∫ θ in (0 : ℝ)..Real.pi,
        twoDWeight r θ * (s.scaledDerivative θ) ^ 2 := by
  unfold originalWeakForm
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  have hpot : angularPotential 2 θ = 0 := by
    simp [angularPotential]
  rw [twoD_angularWeight, twoD_angularDerivative, hpot]
  unfold twoDWeight
  ring

/-- The original two-dimensional weak solution has a strict angular
spectral gap above the first transverse mode's zero-field eigenvalue:
weighted mass is less than its actual energy/source denominator.

This uses the fully constructed positive supersolution and the AC Picone
identity, without assuming smoothness or sign of the weak solution. -/
theorem weak_solution_mass_lt_denominator_twoD
    (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution 2 r s) :
    twoDMass r s < originalGCIDenominator 2 r s := by
  let u := twoDPrimitive s
  let p := twoDWeight r
  let A := twoDLogSlope r
  have hu : AbsolutelyContinuousOnInterval u (0 : ℝ) Real.pi :=
    twoDPrimitive_AC s hs.1
  have hf : AbsolutelyContinuousOnInterval
      (fun θ => p θ * A θ) (0 : ℝ) Real.pi :=
    twoDWeightedLogSlope_AC r hr
  have hu0 : u 0 = 0 := by
    simp [u, twoDPrimitive]
  have huπ : u Real.pi = 0 := hs.1.2.2.2.1
  have hp (θ : ℝ) (_ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
      0 ≤ p θ := Real.exp_nonneg _
  obtain ⟨hE, hQ, hV, hL2, hR⟩ :=
    twoD_picone_integrabilities r hr s hs
  have hRcont : ContinuousOn
      (fun θ =>
        (-(deriv (fun y => p y * A y) θ) -
          p θ * A θ ^ 2 - p θ) * u θ ^ 2)
      (Set.Icc (0 : ℝ) Real.pi) := by
    have hbase : ContinuousOn
        (fun θ => twoDBarrierRemainder r θ * u θ ^ 2)
        (Set.Icc (0 : ℝ) Real.pi) := by
      have hucont : ContinuousOn u
          (Set.Icc (0 : ℝ) Real.pi) := by
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using hu.continuousOn
      exact (twoDBarrierRemainder_continuousOn r hr).mul
        (hucont.pow 2)
    convert hbase using 1
  have hRnonneg :
      ∀ θ ∈ Set.Ioc (0 : ℝ) Real.pi,
        0 ≤ (-(deriv (fun y => p y * A y) θ) -
          p θ * A θ ^ 2 - p θ) * u θ ^ 2 := by
    intro θ hθ
    have hθIcc : θ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hθ.1.le, hθ.2⟩
    change 0 ≤ twoDBarrierRemainder r θ * u θ ^ 2
    exact mul_nonneg (twoDBarrierRemainder_pos r hr θ hθIcc).le
      (sq_nonneg _)
  have hRpos :
      ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi,
        0 < (-(deriv (fun y => p y * A y) θ) -
          p θ * A θ ^ 2 - p θ) * u θ ^ 2 := by
    simpa only [twoDBarrierRemainder, u, p, A]
      using twoDBarrier_remainder_mass_pos_point r hr s hs
  have hRint : IntervalIntegrable
      (fun θ =>
        (-(deriv (fun y => p y * A y) θ) -
          p θ * A θ ^ 2 - p θ) * u θ ^ 2)
      volume (0 : ℝ) Real.pi := hR
  have hPicone :
      (∫ θ in (0 : ℝ)..Real.pi, p θ * u θ ^ 2) <
        ∫ θ in (0 : ℝ)..Real.pi,
          p θ * (deriv u θ) ^ 2 :=
    DFL.Probability.picone_strict_energy_ac u p A Real.pi_pos
      hu hf hu0 huπ hp hE hQ hV hL2 hRint
      hRcont hRnonneg hRpos
  calc
    twoDMass r s =
        ∫ θ in (0 : ℝ)..Real.pi, p θ * u θ ^ 2 := by
      unfold twoDMass
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθIcc : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
      dsimp only
      rw [twoD_reconstruction s hs.1 θ hθIcc]
      rfl
    _ < ∫ θ in (0 : ℝ)..Real.pi,
          p θ * (deriv u θ) ^ 2 := hPicone
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          p θ * (s.scaledDerivative θ) ^ 2 := by
      apply intervalIntegral.integral_congr_ae
      have hqae := hs.1.1.ae_hasDerivAt_integral
      filter_upwards [hqae] with θ hq hθ
      have hθIoc : θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
        simpa only [Set.uIoc_of_le Real.pi_pos.le] using hθ
      have hθIcc : θ ∈ Set.uIcc (0 : ℝ) Real.pi := by
        rw [Set.uIcc_of_le Real.pi_pos.le]
        exact ⟨hθIoc.1.le, hθIoc.2⟩
      have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) Real.pi := by
        simp [Real.pi_pos.le]
      have hd : deriv u θ = s.scaledDerivative θ :=
        (hq hθIcc 0 h0).deriv
      rw [hd]
    _ = originalWeakForm 2 r s s :=
      (twoD_energy_formula r s).symm
    _ = originalGCIDenominator 2 r s := by
      rw [(hs.2 s hs.1).2.2,
        originalSourcePairing_eq_denominator 2 (by omega) r s]

/-- The positive-numerator half of DFL 2015 Conjecture 5.1 is proved
for every original two-dimensional weak solution and every `r>0`. -/
theorem weak_solution_numerator_pos_twoD
    (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution 2 r s) :
    0 < originalGCINumerator 2 r s := by
  have hM := weak_solution_mass_lt_denominator_twoD r hr s hs
  have hC := weak_solution_weighted_cauchy_twoD r s hs
  have hD := weak_solution_denominator_pos 2 (by omega) r s hs
  have hZ := originalForcingNorm_pos_of_weak_solution
    2 (by omega) r s hs
  have hZM : originalForcingNorm 2 r * twoDMass r s <
      originalForcingNorm 2 r * originalGCIDenominator 2 r s :=
    mul_lt_mul_of_pos_left hM hZ
  have hDZ : originalGCIDenominator 2 r s <
      originalForcingNorm 2 r := by
    nlinarith
  exact (weak_solution_numerator_pos_iff_twoD r hr s hs).2 hDZ

theorem weak_solution_coefficient_pos_twoD
    (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution 2 r s) :
    0 < originalGCICoefficient 2 r s := by
  unfold originalGCICoefficient
  exact div_pos (weak_solution_numerator_pos_twoD r hr s hs)
    (weak_solution_denominator_pos 2 (by omega) r s hs)

end

end DFL.GCI
