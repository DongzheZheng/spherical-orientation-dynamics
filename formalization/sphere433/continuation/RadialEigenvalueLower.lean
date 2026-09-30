import continuation.OriginalTiltGroundExists
import continuation.TransverseSphereMode
import DFLSphere433.OriginalLatitude.RadialPartner

/-! The manuscript's radial derivative partner, followed by the actual
auxiliary-sphere ground Rayleigh bound. No minimum, profile existence, or
spectral comparison is an input to the lower bound. -/
noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Interval Topology
namespace DFL.Spectral
open DFLSphere DFLTransverseSphere

/-- A continuous original latitude profile nonzero at one interior point
has strictly positive original weighted norm. -/
theorem latitudeNorm_pos_of_nonzero (M : ℕ) (hM : 2 ≤ M) (r : ℝ)
    (v : ℝ → ℝ) (hv : Continuous v)
    (hne : ∃ t ∈ Ioo (-1 : ℝ) 1, v t ≠ 0) :
    0 < latitudeNorm M r v := by
  apply intervalIntegral.integral_pos (by norm_num)
    ((radialWeight_continuous_ge_two M hM r).mul (hv.pow 2)).continuousOn
  · intro t ht
    exact mul_nonneg (radialWeight_nonneg_Icc M r ⟨ht.1.le, ht.2⟩) (sq_nonneg _)
  · obtain ⟨t,ht,hv⟩ := hne
    exact ⟨t,⟨ht.1.le,ht.2.le⟩,mul_pos (radialWeight_pos M r ht) (sq_pos_of_ne_zero hv)⟩

/-- A nonzero positive-eigenvalue radial profile has a nonzero derivative
in the physical interior; even the second derivative is computed from
local equality rather than imposed. -/
theorem radial_eigenprofile_derivative_nonzero (d : ℕ) (r lam : ℝ)
    (hlam : lam ≠ 0) (f : ℝ → ℝ)
    (heig : RadialEigenEquation d r lam f)
    (hne : ∃ t ∈ Ioo (-1 : ℝ) 1, f t ≠ 0) :
    ∃ t ∈ Ioo (-1 : ℝ) 1, deriv f t ≠ 0 := by
  by_contra h
  have hz : ∀ t ∈ Ioo (-1 : ℝ) 1, deriv f t = 0 := by
    simpa only [not_exists,not_and,not_not] using h
  obtain ⟨t,ht,hft⟩ := hne
  have hev : deriv f =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
    exact hz y hy
  have hdd : deriv (deriv f) t = 0 := by
    rw [hev.deriv_eq]
    simp
  have hh := heig t ht
  simp only [radialApply,hz t ht,hdd,mul_zero,zero_add] at hh
  exact hft ((mul_eq_zero.mp hh.symm).resolve_left hlam)

/-- The true auxiliary minimum bounds every original radial C³
positive-eigenvalue candidate from below, by the manuscript's derivative
partner and half-density conjugation. This includes d=1. -/
theorem radial_eigenvalue_ge_actual_ground (d : ℕ) (r lam : ℝ)
    (hlam : lam ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    (heig : RadialEigenEquation d r lam f)
    (hne : ∃ t ∈ Ioo (-1 : ℝ) 1, f t ≠ 0) :
    roundTiltMinimum d (d : ℝ) r ((d : ℝ)/2-1) ≤ lam := by
  let v := deriv f
  have hv : ContDiff ℝ 2 v := hf.deriv'
  have he := radial_eigenfunction_derivative_partner d r lam f hf heig
  have heclosed := latitudeEigenEquation_closed (d+2) 2 (d : ℝ) r lam v hv he
  let u := halfDensityLift r v
  have hu : ContDiff ℝ 2 u := halfDensityLift_smooth r v hv
  have hue : ∀ t ∈ Icc (-1 : ℝ) 1,
      tiltApply (d+2) (d : ℝ) r ((d : ℝ)/2-1) u t = lam*u t := by
    intro t ht
    have hb : ((d+2 : ℕ) : ℝ)/2-((d : ℝ)/2-1) = 2 := by push_cast; ring
    change halfDensityApply (d+2) _ (d : ℝ) r (halfDensityLift r v) t = _
    rw [hb,halfDensityApply_lift (d+2) 2 (d : ℝ) r v hv t,heclosed t ht]
    dsimp [u,halfDensityLift]
    ring
  have hune : ∃ t ∈ Ioo (-1 : ℝ) 1, u t ≠ 0 := by
    obtain ⟨t,ht,hvne⟩ := radial_eigenprofile_derivative_nonzero d r lam hlam f heig hne
    exact ⟨t,ht,mul_ne_zero (Real.exp_ne_zero _) hvne⟩
  have hnorm := latitudeNorm_pos_of_nonzero (d+2) (by omega) 0 u hu.continuous hune
  obtain ⟨g,hg,_⟩ := original_tilt_ground_exists_ge_two (d+2) (by omega)
    (d : ℝ) r ((d : ℝ)/2-1)
  have hbound := hg.rayleigh u hu
  have henergy : tiltPair (d+2) (d : ℝ) r ((d : ℝ)/2-1) u u =
      lam*latitudeNorm (d+2) 0 u := by
    unfold tiltPair latitudeNorm
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have htcc : t ∈ Icc (-1 : ℝ) 1 := by simpa using ht
    dsimp only
    rw [hue t htcc]
    ring
  rw [henergy,Nat.add_sub_cancel] at hbound
  exact le_of_mul_le_mul_right hbound hnorm

/-- The circle is the exact dimensional boundary: its two auxiliary
partner tilts are reflections, so their actual minima agree. -/
theorem circle_radial_transverse_actual_ground_eq (r : ℝ) :
    roundTiltMinimum 1 1 r (1/2-1) = roundTiltMinimum 1 1 r (1/2) := by
  have he := original_tilt_minimum_even 3 (by omega) 1 r (1/2)
  rw [originalTiltSmoothMinimum_eq_round 3 (by omega),
    originalTiltSmoothMinimum_eq_round 3 (by omega)] at he
  norm_num at he ⊢
  exact he

/-- The physical first-transverse actual ground never exceeds the radial
partner ground for d≥1; the circle equality is handled explicitly. -/
theorem radial_transverse_actual_ground_le (d : ℕ) (hd : 1 ≤ d)
    (r : ℝ) (hr : 0 < r) :
    roundTiltMinimum d (d : ℝ) r ((d : ℝ)/2) ≤
      roundTiltMinimum d (d : ℝ) r ((d : ℝ)/2-1) := by
  by_cases hd2 : 2 ≤ d
  · have he := original_radial_transverse_actual_ground_ordering d hd2 r hr
    have ha : ((d : ℝ)-2)/2 = (d : ℝ)/2-1 := by ring
    rw [ha] at he
    exact he.le
  · have hd1 : d = 1 := by omega
    subst d
    simpa only [Nat.cast_one] using (circle_radial_transverse_actual_ground_eq r).ge

end DFL.Spectral
