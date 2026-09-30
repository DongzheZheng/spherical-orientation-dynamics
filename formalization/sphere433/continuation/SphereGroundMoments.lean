import continuation.TiltHellmannFeynman
import continuation.RoundSphereActualTiltProfile
import continuation.OriginalWeightedGround

/-! The manuscript's moments on the actual sphere measure. The Green
identity gives the pole-flux moment relation directly, so the original
strict rate requires no separately assumed coordinate marginal formula. -/
noncomputable section
set_option maxHeartbeats 1400000
open Bundle Manifold MeasureTheory Set Filter Metric Module
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DFLLatitudeOperator DFLSpectralCoordinates DFLGroundAxisymmetry DFL.Spectral

namespace DFLSphere
private local instance (k : ℕ) : MeasurableSpace (RoundSphere k) := borel (RoundSphere k)
private local instance (k : ℕ) : BorelSpace (RoundSphere k) := ⟨rfl⟩
private local instance (k : ℕ) : IsFiniteMeasure (roundVolume k) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (roundSphereMetric k)
private local instance (k : ℕ) : (roundVolume k).IsOpenPosMeasure :=
  riemannianVolumeMeasure_isOpenPosMeasure (roundSphereMetric k)

/-- The profile belongs to the same actual positive ground used in HF. -/
theorem positiveGround_C2_profile (k : ℕ) (lam0 r a : ℝ) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ ∧
      (∀ x : RoundSphere k, (positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x =
        ψ ((roundCoordinate k).toFun x)) ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, 0 < ψ t) ∧
      ∀ t ∈ Icc (-1 : ℝ) 1,
        tiltApply (k+2) lam0 r a ψ t = roundTiltMinimum k lam0 r a*ψ t := by
  let u := positiveGround k (roundTiltSmoothPotential k lam0 r a)
  have hs := positiveGround_spec k (roundTiltSmoothPotential k lam0 r a)
  let axis : RoundAmbient k := EuclideanSpace.single 0 1
  have haxis : ‖axis‖ = 1 := by simp [axis]
  let F : ℝ → ℝ := fun t => lam0+r^2/4*(1-t^2)-a*r*t
  have hF : Continuous F := by fun_prop
  have heig : ∀ x : RoundSphere k,
      -ΔG (roundMetric (E := RoundAmbient k) (n := k+2)) u.toContMDiffMap x+
        F ⟪axis,(x : RoundAmbient k)⟫_ℝ *u.toContMDiffMap x =
          roundTiltMinimum k lam0 r a*u.toContMDiffMap x := hs.2.2.2.2
  have hlat : ConstantOnLatitudes k u.toContMDiffMap := by
    intro x y hxy
    exact positive_latitude_eigenfunction_same_latitude (n := k+2) axis haxis F hF
      u.toContMDiffMap hs.2.1 (roundTiltMinimum k lam0 r a) heig x y hxy
  obtain ⟨ψ,hψ,hrepr,hpos⟩ := round_positive_same_latitude_exists_C2_profile k
    u.toContMDiffMap hlat hs.2.1
  refine ⟨ψ,hψ,hrepr,hpos,?_⟩
  intro t ht
  obtain ⟨x,hx⟩ := roundCoordinate_surjective_Icc k t ht
  have hh := latitude_schrodinger_equation (n := k+2) axis haxis F ψ hψ
    u.toContMDiffMap hrepr (roundTiltMinimum k lam0 r a) heig x
  change -(1-((roundCoordinate k).toFun x)^2)*deriv (deriv ψ) ((roundCoordinate k).toFun x)+
    ((k+2 : ℕ) : ℝ)*(roundCoordinate k).toFun x*deriv ψ ((roundCoordinate k).toFun x)+
    F ((roundCoordinate k).toFun x)*ψ ((roundCoordinate k).toFun x) =
      roundTiltMinimum k lam0 r a*ψ ((roundCoordinate k).toFun x) at hh
  rw [hx] at hh
  dsimp [F] at hh
  unfold tiltApply halfDensityApply halfDensityPotential
  convert hh using 1
  ring

def sphereProfileW (k : ℕ) (ψ : ℝ → ℝ) : ℝ :=
  ∫ x, (1-((roundCoordinate k).toFun x)^2)*(ψ ((roundCoordinate k).toFun x))^2 ∂roundVolume k

def sphereProfileMean (k : ℕ) (ψ : ℝ → ℝ) : ℝ :=
  ∫ x, (roundCoordinate k).toFun x*(ψ ((roundCoordinate k).toFun x))^2 ∂roundVolume k

def sphereProfileK (k : ℕ) (r : ℝ) (ψ : ℝ → ℝ) : ℝ :=
  ∫ x, (1-((roundCoordinate k).toFun x)^2)*ψ ((roundCoordinate k).toFun x)*
    (r/2*ψ ((roundCoordinate k).toFun x)-deriv ψ ((roundCoordinate k).toFun x)) ∂roundVolume k

/-- The moment with `1-t²` is strictly positive for every positive profile. -/
theorem sphereProfileW_pos (k : ℕ) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < ψ t) : 0 < sphereProfileW k ψ := by
  obtain ⟨x,hx⟩ := roundCoordinate_surjective_Icc k 0 (by norm_num)
  have ht := (roundCoordinate k).smooth.continuous
  have hc : Continuous (fun x : RoundSphere k => (1-((roundCoordinate k).toFun x)^2)*
      (ψ ((roundCoordinate k).toFun x))^2) :=
    (continuous_const.sub (ht.pow 2)).mul ((hψ.comp ht).pow 2)
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _)
  · intro y
    have hty : (roundCoordinate k).toFun y ∈ Icc (-1 : ℝ) 1 := by rw [← roundCoordinate_range k]; exact mem_range_self y
    have hw : 0 ≤ 1-((roundCoordinate k).toFun y)^2 := by rcases hty with ⟨hl,hr⟩; nlinarith
    exact mul_nonneg hw (sq_nonneg _)
  · rw [hx]
    have hp := hpos 0 (by norm_num)
    norm_num
    exact hp.ne'

/-- The flux moment is strictly positive when the ungauged profile decreases. -/
theorem sphereProfileK_pos (k : ℕ) (r : ℝ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < ψ t)
    (hneg : ∀ t ∈ Ioo (-1 : ℝ) 1, deriv ψ t-r/2*ψ t < 0) :
    0 < sphereProfileK k r ψ := by
  obtain ⟨x,hx⟩ := roundCoordinate_surjective_Icc k 0 (by norm_num)
  have ht := (roundCoordinate k).smooth.continuous
  have hp := hψ.continuous.comp ht
  have hd := (hψ.deriv' : ContDiff ℝ 1 (deriv ψ)).continuous.comp ht
  have hc : Continuous (fun x : RoundSphere k => (1-((roundCoordinate k).toFun x)^2)*
      ψ ((roundCoordinate k).toFun x)*(r/2*ψ ((roundCoordinate k).toFun x)-
        deriv ψ ((roundCoordinate k).toFun x))) :=
    ((continuous_const.sub (ht.pow 2)).mul hp).mul ((continuous_const.mul hp).sub hd)
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _)
  · intro y
    let t := (roundCoordinate k).toFun y
    have hty : t ∈ Icc (-1 : ℝ) 1 := by rw [← roundCoordinate_range k]; exact mem_range_self y
    by_cases hl : t = -1
    · simp only [t] at hl
      simp [hl]
    by_cases hr : t = 1
    · simp only [t] at hr
      simp [hr]
    have hti : t ∈ Ioo (-1 : ℝ) 1 := ⟨lt_of_le_of_ne hty.1 (Ne.symm hl),lt_of_le_of_ne hty.2 hr⟩
    have hw : 0 < 1-t^2 := by rcases hti with ⟨h₁,h₂⟩; nlinarith
    have hn := hneg t hti
    exact (mul_pos (mul_pos hw (hpos t hty)) (by linarith)).le
  · rw [hx]
    have hp₀ := hpos 0 (by norm_num)
    have hn₀ := hneg 0 (by norm_num)
    have hn : 0 < r/2*ψ 0-deriv ψ 0 := by linarith
    simpa only [sq,zero_mul,sub_zero,one_mul] using (mul_pos hp₀ hn).ne'

/-- True Green identity on the round sphere gives the same moment flux
relation as the manuscript's both-pole integration by parts. -/
theorem sphere_profile_weight_flux (k : ℕ) (r : ℝ) (u : SmoothScalar (roundSphereMetric k))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hrepr : ∀ x : RoundSphere k, u.toFun x = ψ ((roundCoordinate k).toFun x)) :
    r*sphereProfileW k ψ-((k+2 : ℕ) : ℝ)*sphereProfileMean k ψ-2*sphereProfileK k r ψ = 0 := by
  let g := roundSphereMetric k
  let t := (roundCoordinate k).toContMDiffMap
  let axis : RoundAmbient k := EuclideanSpace.single 0 1
  have haxis : ‖axis‖ = 1 := by simp [axis]
  have hgreen := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian g
    (u.smooth.mul u.smooth) t.contMDiff (HasCompactSupport.of_compactSpace _)
  have hgrad (x : RoundSphere k) :
      g.inner x (gradFun g (fun y => u.toFun y*u.toFun y) x) (gradFun g t x) =
        2*(1-(t x)^2)*ψ (t x)*deriv ψ (t x) := by
    have hu : (fun y : RoundSphere k => u.toFun y*u.toFun y) = fun y => ψ (t y)*ψ (t y) := by
      funext y
      rw [hrepr y]
      rfl
    have hd₀ := (hψ.differentiable (by norm_num) (t x)).hasDerivAt
    have hd := hd₀.mul hd₀
    have hid : deriv ψ (t x)*ψ (t x)+ψ (t x)*deriv ψ (t x) =
        2*ψ (t x)*deriv ψ (t x) := by ring
    rw [hid] at hd
    have hchain := gradFun_comp g hd.differentiableAt (t.contMDiff.mdifferentiable (by simp) x)
    change gradFun g (fun y => ψ (t y)*ψ (t y)) x =
      deriv (ψ*ψ) (t x) • gradFun g t x at hchain
    rw [hu,hchain,hd.deriv]
    have hnorm := latitude_gradient_norm_sq (n := k+2) axis haxis x
    change g.inner x (gradFun g t x) (gradFun g t x) = 1-(t x)^2 at hnorm
    rw [(g.inner x).map_smul,smul_apply,smul_eq_mul,hnorm]
    ring
  have hLap (x : RoundSphere k) : ΔG g t x = -((k+2 : ℕ) : ℝ)*t x :=
    coordinate_laplacian x axis
  change (∫ x, g.inner x (gradFun g (fun y => u.toFun y*u.toFun y) x) (gradFun g t x) ∂roundVolume k) =
    -(∫ x, u.toFun x*u.toFun x*ΔG g t x ∂roundVolume k) at hgreen
  have hGL : (∫ x, g.inner x (gradFun g (fun y => u.toFun y*u.toFun y) x) (gradFun g t x) ∂roundVolume k) =
      ∫ x, 2*(1-(t x)^2)*ψ (t x)*deriv ψ (t x) ∂roundVolume k :=
    integral_congr_ae (Eventually.of_forall hgrad)
  have hGR : -(∫ x, u.toFun x*u.toFun x*ΔG g t x ∂roundVolume k) =
      ((k+2 : ℕ) : ℝ)*sphereProfileMean k ψ := by
    unfold sphereProfileMean
    rw [← integral_const_mul]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hLap,hrepr x]
    dsimp [sphereProfileMean,t]
    ring
  rw [hGL,hGR] at hgreen
  have ht := (roundCoordinate k).smooth.continuous
  have hp := hψ.continuous.comp ht
  have hd := (hψ.deriv' : ContDiff ℝ 1 (deriv ψ)).continuous.comp ht
  have hW : Integrable (fun x : RoundSphere k => (1-((roundCoordinate k).toFun x)^2)*
      (ψ ((roundCoordinate k).toFun x))^2) (roundVolume k) :=
    ((continuous_const.sub (ht.pow 2)).mul (hp.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hT : Integrable (fun x : RoundSphere k => (1-((roundCoordinate k).toFun x)^2)*
      ψ ((roundCoordinate k).toFun x)*deriv ψ ((roundCoordinate k).toFun x)) (roundVolume k) :=
    (((continuous_const.sub (ht.pow 2)).mul hp).mul hd).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK : sphereProfileK k r ψ = r/2*sphereProfileW k ψ-
      ∫ x, (1-(t x)^2)*ψ (t x)*deriv ψ (t x) ∂roundVolume k := by
    unfold sphereProfileK sphereProfileW
    change (∫ x, (1-((roundCoordinate k).toFun x)^2)*ψ ((roundCoordinate k).toFun x)*
      (r/2*ψ ((roundCoordinate k).toFun x)-deriv ψ ((roundCoordinate k).toFun x)) ∂roundVolume k) =
      r/2*(∫ x, (1-((roundCoordinate k).toFun x)^2)*(ψ ((roundCoordinate k).toFun x))^2 ∂roundVolume k)-
      ∫ x, (1-((roundCoordinate k).toFun x)^2)*ψ ((roundCoordinate k).toFun x)*
        deriv ψ ((roundCoordinate k).toFun x) ∂roundVolume k
    rw [← integral_const_mul,← integral_sub (hW.const_mul (r/2)) hT]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hTwo : (∫ x, 2*(1-(t x)^2)*ψ (t x)*deriv ψ (t x) ∂roundVolume k) =
      2*(∫ x, (1-(t x)^2)*ψ (t x)*deriv ψ (t x) ∂roundVolume k) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hTwo] at hgreen
  rw [hK]
  linarith

/-- The actual sphere HF integral is the manuscript's two-moment expression. -/
theorem sphere_HF_integral_eq_moments (k : ℕ) (r a : ℝ) (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    (∫ x, (r*(1-((roundCoordinate k).toFun x)^2)/2-a*(roundCoordinate k).toFun x)*
      (ψ ((roundCoordinate k).toFun x))^2 ∂roundVolume k) =
      r/2*sphereProfileW k ψ-a*sphereProfileMean k ψ := by
  have ht := (roundCoordinate k).smooth.continuous
  have hp := hψ.comp ht
  have hW : Integrable (fun x : RoundSphere k => (1-((roundCoordinate k).toFun x)^2)*
      (ψ ((roundCoordinate k).toFun x))^2) (roundVolume k) :=
    ((continuous_const.sub (ht.pow 2)).mul (hp.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hm : Integrable (fun x : RoundSphere k => (roundCoordinate k).toFun x*
      (ψ ((roundCoordinate k).toFun x))^2) (roundVolume k) :=
    (ht.mul (hp.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold sphereProfileW sphereProfileMean
  rw [← integral_const_mul,← integral_const_mul,← integral_sub (hW.const_mul (r/2)) (hm.const_mul a)]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The HF expression equals the positive original flux expression on the
same actual sphere ground profile. -/
theorem sphere_HF_rate_eq_flux (k : ℕ) (b r : ℝ)
    (u : SmoothScalar (roundSphereMetric k)) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hrepr : ∀ x : RoundSphere k, u.toFun x = ψ ((roundCoordinate k).toFun x)) :
    r/2*sphereProfileW k ψ+(b-((k+2 : ℕ) : ℝ)/2)*sphereProfileMean k ψ =
      (b*r*sphereProfileW k ψ+(((k+2 : ℕ) : ℝ)-2*b)*sphereProfileK k r ψ)/((k+2 : ℕ) : ℝ) := by
  have hM : ((k+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hflux := sphere_profile_weight_flux k r u ψ hψ hrepr
  apply (eq_div_iff hM).mpr
  linear_combination (((k+2 : ℕ) : ℝ)/2-b)*hflux

/-- The original actual spectral derivative is strictly positive in the
parameter range `0<b≤M/2`. Neither derivative sign nor a profile/eigenbranch
is an input; the same actual ground is used in HF, flux, and positivity. -/
theorem roundTiltMinimum_deriv_r_pos (k : ℕ) (lam0 b r : ℝ)
    (hb : 0 < b) (hbhalf : 2*b ≤ ((k+2 : ℕ) : ℝ)) (hr : 0 < r) :
    0 < deriv (fun s => roundTiltMinimum k lam0 s (((k+2 : ℕ) : ℝ)/2-b)) r := by
  let a := ((k+2 : ℕ) : ℝ)/2-b
  let u := positiveGround k (roundTiltSmoothPotential k lam0 r a)
  obtain ⟨ψ,hψ,hrepr,hpos,heig⟩ := positiveGround_C2_profile k lam0 r a
  have hneg : ∀ t ∈ Ioo (-1 : ℝ) 1, deriv ψ t-r/2*ψ t < 0 := by
    intro t ht
    have hn := positive_tilt_profile_ungauged_deriv_neg (k+2) (by omega) b lam0 r
      (roundTiltMinimum k lam0 r a) (mul_pos hb hr) ψ hψ hpos heig ht
    rw [weightedProfileFromHalfDensity_deriv r ψ hψ t] at hn
    have hexp := Real.exp_pos ((-r/2)*t)
    nlinarith
  have hW := sphereProfileW_pos k ψ hψ.continuous hpos
  have hK := sphereProfileK_pos k r ψ hψ hpos hneg
  have hHF := roundTiltMinimum_deriv_r k lam0 a r
  have hrepr' : ∀ x : RoundSphere k,
      (positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x = ψ ((roundCoordinate k).toFun x) := hrepr
  have hint : (∫ x, (r*(1-((roundCoordinate k).toFun x)^2)/2-a*(roundCoordinate k).toFun x)*
      ((positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x)^2 ∂roundVolume k) =
      r/2*sphereProfileW k ψ-a*sphereProfileMean k ψ := by
    rw [← sphere_HF_integral_eq_moments k r a ψ hψ.continuous]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hrepr' x]
  rw [hint] at hHF
  have hrate := sphere_HF_rate_eq_flux k b r u ψ hψ hrepr
  have hscalar : r/2*sphereProfileW k ψ-a*sphereProfileMean k ψ =
      r/2*sphereProfileW k ψ+(b-((k+2 : ℕ) : ℝ)/2)*sphereProfileMean k ψ := by dsimp [a]; ring
  rw [hscalar,hrate] at hHF
  rw [hHF]
  apply div_pos
  · exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos hb hr) hW)
      (mul_nonneg (by linarith) hK.le)
  · positivity

end DFLSphere
