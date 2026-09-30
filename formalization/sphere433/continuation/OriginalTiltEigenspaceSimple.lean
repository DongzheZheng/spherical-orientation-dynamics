import continuation.OriginalWeightedGround
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Original two-pole Wronskian proof of the C² latitude ground
eigenspace's simplicity. The compared eigenfunction need not be positive.
The positive normalized profile and its actual minimum are then supplied
by the genuine auxiliary sphere ground construction. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set
namespace DFL.Spectral
open DFLSphere

private theorem closed_interval_const_of_deriv_zero (F : ℝ → ℝ)
    (hF : ContinuousOn F (Icc (-1 : ℝ) 1))
    (hder : ∀ t ∈ Ioo (-1 : ℝ) 1,HasDerivAt F 0 t) :
    ∀ t ∈ Icc (-1 : ℝ) 1,F t=F (-1) := by
  have hd : DifferentiableOn ℝ F (interior (Icc (-1 : ℝ) 1)) := by
    intro t ht
    rw [interior_Icc] at ht
    exact (hder t ht).differentiableAt.differentiableWithinAt
  have h0 : ∀ t ∈ interior (Icc (-1 : ℝ) 1),deriv F t=0 := by
    intro t ht
    rw [interior_Icc] at ht
    exact (hder t ht).deriv
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc (-1 : ℝ) 1) hF hd
    (fun t ht => by rw [h0 t ht])
  have ha := antitoneOn_of_deriv_nonpos (convex_Icc (-1 : ℝ) 1) hF hd
    (fun t ht => by rw [h0 t ht])
  intro t ht
  exact le_antisymm (ha (by norm_num) ht ht.1) (hm (by norm_num) ht ht.1)

/-- The original vanishing pole coefficient forces the Wronskian of
two C² eigenprofiles with the same eigenvalue to vanish pointwise.
Only the actual original differential equations on the open interval
are used; no boundary data or simplicity premise is supplied. -/
theorem original_tilt_eigen_wronskian_zero (M : ℕ) (hM : 0<M)
    (lam0 r a lam : ℝ) (u v : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (heu : ∀ t ∈ Ioo (-1 : ℝ) 1,tiltApply M lam0 r a u t=lam*u t)
    (hev : ∀ t ∈ Ioo (-1 : ℝ) 1,tiltApply M lam0 r a v t=lam*v t) :
    ∀ t ∈ Ioo (-1 : ℝ) 1,v t*deriv u t-u t*deriv v t=0 := by
  have hu1 : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hv1 : ContDiff ℝ 1 (deriv v) := hv.deriv'
  have hud := hu.differentiable (by norm_num)
  have hvd := hv.differentiable (by norm_num)
  have hud' := hu1.differentiable (by norm_num)
  have hvd' := hv1.differentiable (by norm_num)
  let F : ℝ → ℝ := fun t => latitudeFluxFactor M 0 t*(v t*deriv u t-u t*deriv v t)
  have hF : Continuous F := (latitudeFluxFactor_continuous M 0).mul
    ((hv.continuous.mul hu1.continuous).sub (hu.continuous.mul hv1.continuous))
  have hd : ∀ t ∈ Ioo (-1 : ℝ) 1,HasDerivAt F 0 t := by
    intro t ht
    have hh : HasDerivAt F (radialWeight M 0 t*
        (u t*tiltApply M lam0 r a v t-v t*tiltApply M lam0 r a u t)) t := by
      convert (latitudeFluxFactor_hasDerivAt M 0 ht).mul
        (((hvd t).hasDerivAt.mul (hud' t).hasDerivAt).sub
          ((hud t).hasDerivAt.mul (hvd' t).hasDerivAt)) using 1
      all_goals try rfl
      rw [latitudeFluxFactor_eq_weight M 0 ht]
      unfold tiltApply halfDensityApply
      simp only [Pi.sub_apply,Pi.mul_apply]
      ring
    simpa only [heu t ht,hev t ht,mul_comm,mul_left_comm,sub_self,mul_zero,zero_mul] using hh
  intro t ht
  have hf0 := closed_interval_const_of_deriv_zero F hF.continuousOn hd t ⟨ht.1.le,ht.2.le⟩
  have hz : latitudeFluxFactor M 0 t*(v t*deriv u t-u t*deriv v t)=0 := by
    simpa only [F,latitudeFluxFactor_left M hM 0,zero_mul] using hf0
  exact (mul_eq_zero.mp hz).resolve_left (latitudeFluxFactor_pos M 0 ht).ne'

/-- Every C² eigenprofile for the same original tilt eigenvalue is a
constant multiple of any closed-interval positive C² eigenprofile.
The conclusion includes both poles, and the compared profile may change
sign or vanish. -/
theorem original_tilt_eigenprofile_proportional (M : ℕ) (hM : 0<M)
    (lam0 r a lam : ℝ) (u v : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1,0<u t)
    (heu : ∀ t ∈ Ioo (-1 : ℝ) 1,tiltApply M lam0 r a u t=lam*u t)
    (hev : ∀ t ∈ Ioo (-1 : ℝ) 1,tiltApply M lam0 r a v t=lam*v t) :
    ∃ c : ℝ,∀ t ∈ Icc (-1 : ℝ) 1,v t=c*u t := by
  have hW := original_tilt_eigen_wronskian_zero M hM lam0 r a lam u v hu hv heu hev
  let Q : ℝ → ℝ := fun t => v t/u t
  have hQ : ContinuousOn Q (Icc (-1 : ℝ) 1) :=
    hv.continuous.continuousOn.div hu.continuous.continuousOn
      (fun t ht => (hpos t ht).ne')
  have hd : ∀ t ∈ Ioo (-1 : ℝ) 1,HasDerivAt Q 0 t := by
    intro t ht
    have hn := (hpos t ⟨ht.1.le,ht.2.le⟩).ne'
    have hh := ((hv.differentiable (by norm_num) t).hasDerivAt).div
      ((hu.differentiable (by norm_num) t).hasDerivAt) hn
    have hz : (deriv v t*u t-v t*deriv u t)/(u t)^2=0 := by
      rw [show deriv v t*u t-v t*deriv u t=0 from by nlinarith [hW t ht],zero_div]
    rw [hz] at hh
    exact hh
  refine ⟨Q (-1),?_⟩
  intro t ht
  have hh := closed_interval_const_of_deriv_zero Q hQ hd t ht
  exact (div_eq_iff (hpos t ht).ne').mp hh

/-- The original weighted amplitude has the same one-dimensional
eigenspace; the actual half-density conjugacy transports the proof. -/
theorem original_weighted_eigenprofile_proportional (M : ℕ) (hM : 0<M)
    (b lam0 r lam : ℝ) (u v : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1,0<u t)
    (heu : LatitudeEigenEquation M b lam0 r lam u)
    (hev : LatitudeEigenEquation M b lam0 r lam v) :
    ∃ c : ℝ,∀ t ∈ Icc (-1 : ℝ) 1,v t=c*u t := by
  have hb : (M : ℝ)/2-((M : ℝ)/2-b)=b := by ring
  have he (w : ℝ → ℝ) (hw : ContDiff ℝ 2 w)
      (heq : LatitudeEigenEquation M b lam0 r lam w) :
      ∀ t ∈ Ioo (-1 : ℝ) 1,
        tiltApply M lam0 r ((M : ℝ)/2-b) (halfDensityLift r w) t=lam*halfDensityLift r w t := by
    intro t ht
    simpa only [tiltApply,hb] using halfDensityLift_eigen M b lam0 r lam w hw heq ht
  obtain ⟨c,hc⟩ := original_tilt_eigenprofile_proportional M hM lam0 r ((M : ℝ)/2-b) lam
    (halfDensityLift r u) (halfDensityLift r v) (halfDensityLift_smooth r u hu)
    (halfDensityLift_smooth r v hv) (fun t ht => mul_pos (Real.exp_pos _) (hpos t ht))
    (he u hu heu) (he v hv hev)
  refine ⟨c,?_⟩
  intro t ht
  have hh := hc t ht
  dsimp only [halfDensityLift] at hh
  apply mul_left_cancel₀ (Real.exp_ne_zero ((r/2)*t))
  exact hh.trans (by ring)

/-- Actual original normalized tilt ground existence and C² eigenspace
simplicity, with all ground and minimum premises discharged. -/
theorem original_tilt_minimum_eigenspace_simple_exists (M : ℕ) (hM : 2≤M)
    (lam0 r a : ℝ) :
    ∃ u : ℝ → ℝ,IsTiltGroundProfile M lam0 r a (roundTiltMinimum (M-2) lam0 r a) u ∧
      (∀ t ∈ Icc (-1 : ℝ) 1,0<u t) ∧
      ∀ v : ℝ → ℝ,ContDiff ℝ 2 v →
        (∀ t ∈ Ioo (-1 : ℝ) 1,
          tiltApply M lam0 r a v t=roundTiltMinimum (M-2) lam0 r a*v t) →
        ∃ c : ℝ,∀ t ∈ Icc (-1 : ℝ) 1,v t=c*u t := by
  obtain ⟨u,hu,hp⟩ := original_tilt_ground_exists_ge_two M hM lam0 r a
  refine ⟨u,hu,hp,?_⟩
  intro v hv he
  exact original_tilt_eigenprofile_proportional M (by omega) lam0 r a _ u v hu.smooth hv hp
    (fun t ht => hu.eigen t ⟨ht.1.le,ht.2.le⟩) he

/-- Actual original weighted positive ground and simplicity of its full
C² latitude eigenspace, for all M≥2 and real parameters. -/
theorem original_weighted_minimum_eigenspace_simple_exists (M : ℕ) (hM : 2≤M)
    (b lam0 r : ℝ) :
    ∃ u : ℝ → ℝ,ContDiff ℝ 2 u ∧ (∀ t ∈ Icc (-1 : ℝ) 1,0<u t) ∧ latitudeNorm M r u=1 ∧
      LatitudeEigenEquation M b lam0 r (roundTiltMinimum (M-2) lam0 r ((M : ℝ)/2-b)) u ∧
      ∀ v : ℝ → ℝ,ContDiff ℝ 2 v →
        LatitudeEigenEquation M b lam0 r (roundTiltMinimum (M-2) lam0 r ((M : ℝ)/2-b)) v →
        ∃ c : ℝ,∀ t ∈ Icc (-1 : ℝ) 1,v t=c*u t := by
  obtain ⟨u,hu,hp,hn,he⟩ := original_weighted_positive_ground_exists M hM b lam0 r
  exact ⟨u,hu,hp,hn,he,fun v hv hev =>
    original_weighted_eigenprofile_proportional M (by omega) b lam0 r _ u v hu hv hp he hev⟩

end DFL.Spectral
