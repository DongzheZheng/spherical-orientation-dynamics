import DFLSphere433.OriginalLatitude.GroundConcavity

/-! The manuscript's positive-profile Picone identity for the exact original
half-density latitude operator. No Rayleigh minimum is assumed. -/
noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped Interval
namespace DFL.Spectral

private theorem tiltApply_explicit (M : ℕ) (lam0 r a : ℝ) (v : ℝ → ℝ) (t : ℝ) :
    tiltApply M lam0 r a v t = -(1-t^2)*deriv (deriv v) t +
      (M : ℝ)*t*deriv v t+(lam0+r^2*(1-t^2)/4-a*r*t)*v t := by
  unfold tiltApply halfDensityApply halfDensityPotential
  ring

/-- Original two-pole Picone remainder, in the original fixed latitude
weight. Closed-interval positivity removes every pole denominator. -/
theorem positive_tilt_eigenprofile_picone (M : ℕ) (hM : 2 ≤ M)
    (lam0 r a lam : ℝ) (u v : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < u t)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1, tiltApply M lam0 r a u t = lam*u t) :
    tiltPair M lam0 r a v v-lam*latitudeNorm M 0 v =
      ∫ t in (-1 : ℝ)..1, latitudeFluxFactor M 0 t *
        (deriv v t-v t*(deriv u t/u t))^2 := by
  have hm : 0 < M := by omega
  have hu1 : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hv1 : ContDiff ℝ 1 (deriv v) := hv.deriv'
  have hud := hu.differentiable (by norm_num)
  have hvd := hv.differentiable (by norm_num)
  have hud' := hu1.differentiable (by norm_num)
  have hvd' := hv1.differentiable (by norm_num)
  let Q : ℝ → ℝ := fun t => deriv u t/u t
  let F : ℝ → ℝ := fun t => latitudeFluxFactor M 0 t *
    (v t*deriv v t-(v t)^2*Q t)
  let A : ℝ → ℝ := fun t => latitudeFluxFactor M 0 t * (deriv v t-v t*Q t)^2
  let B : ℝ → ℝ := fun t => radialWeight M 0 t*v t*(tiltApply M lam0 r a v t-lam*v t)
  have hQ : ContinuousOn Q (Icc (-1 : ℝ) 1) :=
    hu1.continuous.continuousOn.div hu.continuous.continuousOn
      (fun t ht => ne_of_gt (hpos t ht))
  have hF : ContinuousOn F (Icc (-1 : ℝ) 1) :=
    (latitudeFluxFactor_continuous M 0).continuousOn.mul
      ((hv.continuous.mul hv1.continuous).continuousOn.sub
        ((hv.continuous.pow 2).continuousOn.mul hQ))
  have hA : ContinuousOn A (Icc (-1 : ℝ) 1) :=
    (latitudeFluxFactor_continuous M 0).continuousOn.mul
      ((hv1.continuous.continuousOn.sub (hv.continuous.continuousOn.mul hQ)).pow 2)
  have hB : Continuous B := ((radialWeight_continuous_ge_two M hM 0).mul hv.continuous).mul
    ((halfDensityApply_continuous M _ lam0 r v hv).sub (continuous_const.mul hv.continuous))
  have hderiv : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (A t-B t) t := by
    intro t ht
    have hn : u t ≠ 0 := ne_of_gt (hpos t ⟨ht.1.le,ht.2.le⟩)
    have he := heig t ⟨ht.1.le,ht.2.le⟩
    rw [tiltApply_explicit] at he
    convert! (latitudeFluxFactor_hasDerivAt M 0 ht).mul
      (((hvd t).hasDerivAt.mul (hvd' t).hasDerivAt).sub
        (((hvd t).hasDerivAt.pow 2).mul ((hud' t).hasDerivAt.div (hud t).hasDerivAt hn))) using 1
    dsimp [F,A,B,Q]
    rw [latitudeFluxFactor_eq_weight M 0 ht,tiltApply_explicit]
    field_simp
    linear_combination -(4*radialWeight M 0 t)*(v t)^2*u t*he
  have hAI : IntervalIntegrable A volume (-1 : ℝ) 1 :=
    hA.intervalIntegrable_of_Icc (by norm_num)
  have hBI : IntervalIntegrable B volume (-1 : ℝ) 1 := hB.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1 : ℝ) ≤ 1) hF hderiv (hAI.sub hBI)
  have hz : (∫ t in (-1 : ℝ)..1, A t)-(∫ t in (-1 : ℝ)..1, B t) = 0 := by
    rw [intervalIntegral.integral_sub hAI hBI] at hFTC
    simpa [F,latitudeFluxFactor_left M hm 0,latitudeFluxFactor_right M hm 0] using hFTC
  have hPairI : IntervalIntegrable (fun t => radialWeight M 0 t*v t*tiltApply M lam0 r a v t)
      volume (-1 : ℝ) 1 := (((radialWeight_continuous_ge_two M hM 0).mul hv.continuous).mul
    (halfDensityApply_continuous M _ lam0 r v hv)).intervalIntegrable _ _
  have hNormI : IntervalIntegrable (fun t => radialWeight M 0 t*(v t)^2) volume (-1 : ℝ) 1 :=
    ((radialWeight_continuous_ge_two M hM 0).mul (hv.continuous.pow 2)).intervalIntegrable _ _
  have hBint : (∫ t in (-1 : ℝ)..1, B t) = tiltPair M lam0 r a v v-lam*latitudeNorm M 0 v := by
    calc
      _ = ∫ t in (-1 : ℝ)..1, radialWeight M 0 t*v t*tiltApply M lam0 r a v t-
          lam*(radialWeight M 0 t*(v t)^2) := by
        apply intervalIntegral.integral_congr
        intro t _; dsimp [B]; ring
      _ = _ := by
        rw [intervalIntegral.integral_sub hPairI (hNormI.const_mul lam),intervalIntegral.integral_const_mul]
        rfl
  rw [hBint] at hz
  exact (sub_eq_zero.mp hz).symm

/-- Original Rayleigh lower bound follows from the actual positive C²
profile and its eigen-equation, by the proved Picone square. -/
theorem positive_tilt_eigenprofile_rayleigh (M : ℕ) (hM : 2 ≤ M)
    (lam0 r a lam : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < u t)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1, tiltApply M lam0 r a u t = lam*u t) :
    ∀ v : ℝ → ℝ, ContDiff ℝ 2 v →
      lam*latitudeNorm M 0 v ≤ tiltPair M lam0 r a v v := by
  intro v hv
  apply sub_nonneg.mp
  rw [positive_tilt_eigenprofile_picone M hM lam0 r a lam u v hu hv hpos heig]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  have hp : 0 ≤ latitudeFluxFactor M 0 t := by
    rw [latitudeFluxFactor_eq_weight_Icc M (by omega) 0 ht]
    exact mul_nonneg (radialWeight_nonneg_Icc M 0 ht) (by nlinarith [ht.1,ht.2])
  exact mul_nonneg hp (sq_nonneg _)

private theorem tiltApply_const_mul (M : ℕ) (lam0 r a c : ℝ)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (t : ℝ) :
    tiltApply M lam0 r a (fun x => c*u x) t = c*tiltApply M lam0 r a u t := by
  have hud := hu.differentiable (by norm_num)
  have hud' := (hu.deriv' : ContDiff ℝ 1 (deriv u)).differentiable (by norm_num)
  have hd : deriv (fun x => c*u x) = fun x => c*deriv u x := by
    funext x
    exact ((hud x).hasDerivAt.const_mul c).deriv
  have hdd : deriv (fun x => c*deriv u x) t = c*deriv (deriv u) t :=
    ((hud' t).hasDerivAt.const_mul c).deriv
  simp only [tiltApply_explicit,hd,hdd]
  ring

/-- Actual positive eigenprofiles have the original normalized ground
profile structure; its Rayleigh field is proved by Picone, not assumed. -/
theorem positive_tilt_eigenprofile_normalized_ground (M : ℕ) (hM : 2 ≤ M)
    (lam0 r a lam : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < u t)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1, tiltApply M lam0 r a u t = lam*u t) :
    ∃ g : ℝ → ℝ, IsTiltGroundProfile M lam0 r a lam g ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, 0 < g t) ∧
      ∀ t, g t = u t/Real.sqrt (latitudeNorm M 0 u) := by
  have hN : 0 < latitudeNorm M 0 u := latitudeNorm_pos M hM 0 u hu.continuous
    (fun t ht => hpos t ⟨ht.1.le,ht.2.le⟩)
  let c : ℝ := (Real.sqrt (latitudeNorm M 0 u))⁻¹
  let g : ℝ → ℝ := fun t => c*u t
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hN)
  have hg : ContDiff ℝ 2 g := contDiff_const.mul hu
  have hgpos : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < g t := fun t ht => mul_pos hc (hpos t ht)
  have hgn : latitudeNorm M 0 g = 1 := by
    have heq : latitudeNorm M 0 g = c^2*latitudeNorm M 0 u := by
      unfold latitudeNorm
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _; dsimp [g]; ring
    rw [heq]
    dsimp [c]
    rw [inv_pow,Real.sq_sqrt hN.le]
    exact inv_mul_cancel₀ (ne_of_gt hN)
  have hge : ∀ t ∈ Icc (-1 : ℝ) 1, tiltApply M lam0 r a g t = lam*g t := by
    intro t ht
    rw [tiltApply_const_mul M lam0 r a c u hu t,heig t ht]
    dsimp [g]; ring
  refine ⟨g,⟨hg,fun t ht => hgpos t ⟨ht.1.le,ht.2.le⟩,hgn,hge,
    positive_tilt_eigenprofile_rayleigh M hM lam0 r a lam u hu hpos heig⟩,hgpos,?_⟩
  intro t
  dsimp [g,c]
  rw [div_eq_mul_inv,mul_comm]

end DFL.Spectral
