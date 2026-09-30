import continuation.ActualTiltProfileWitness
import continuation.OriginalTiltEigenspaceSimple
import DFLSphere433.OriginalLatitude.RadialPartner

/-! Compatible finite pole profiles of the same actual smooth auxiliary
sphere state also control its differentiated radial reconstruction.
No globally C-infinity real extension is assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold Metric Module Set Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLTransverseSphere DFL.Spectral
namespace DFLSphere

/-- Equality of genuine C¹ profiles on the physical closed interval
forces equality of their first derivatives there, including both poles. -/
theorem C1_profiles_deriv_eq_on_Icc (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (he : ∀ t ∈ Icc (-1 : ℝ) 1,u t=v t) :
    ∀ t ∈ Icc (-1 : ℝ) 1,deriv u t=deriv v t := by
  have hI : EqOn (deriv u) (deriv v) (Ioo (-1 : ℝ) 1) := by
    intro t ht
    have hh : u=ᶠ[𝓝 t] v := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
      exact he y ⟨hy.1.le,hy.2.le⟩
    exact hh.deriv_eq
  have hcl := hI.closure (hu.deriv' : ContDiff ℝ 0 (deriv u)).continuous
    (hv.deriv' : ContDiff ℝ 0 (deriv v)).continuous
  rw [closure_Ioo (by norm_num : (-1 : ℝ)≠1)] at hcl
  exact hcl

/-- The actual normalized tilt ground has a true C³ original profile
and retains its actual smooth auxiliary sphere representative. -/
theorem original_tilt_ground_C3_actual_witness (k : ℕ) (lam0 r a : ℝ) :
    ∃ psi : ℝ → ℝ,ContDiff ℝ 3 psi ∧
      IsTiltGroundProfile (k+2) lam0 r a (roundTiltMinimum k lam0 r a) psi ∧
      (∀ t ∈ Icc (-1 : ℝ) 1,0<psi t) ∧
      ∃ s : C^∞⟮𝓡 (k+2),RoundSphere k;ℝ⟯,
        ConstantOnLatitudes k s ∧ ∀ x,s x=psi ((roundCoordinate k).toFun x) := by
  obtain ⟨u,hu,hpos,s,hs,hus⟩ := original_tilt_ground_actual_witness k lam0 r a
  obtain ⟨v,hv,hvs⟩ := round_smooth_same_latitude_exists_finite_profile 3 k s hs
  have he := round_profiles_eq_on_Icc k s u v hus hvs
  have hd := C1_profiles_deriv_eq_on_Icc u v (hu.smooth.of_le (by decide))
    (hv.of_le (by decide)) he
  have hvd2 : ContDiff ℝ 2 (deriv v) := hv.deriv'
  have hdd := C1_profiles_deriv_eq_on_Icc (deriv u) (deriv v) hu.smooth.deriv'
    (hvd2.of_le (by decide)) hd
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by decide)
  have hvp : ∀ t ∈ Icc (-1 : ℝ) 1,0<v t := by intro t ht;rw [← he t ht];exact hpos t ht
  have hve : ∀ t ∈ Icc (-1 : ℝ) 1,
      tiltApply (k+2) lam0 r a v t=roundTiltMinimum k lam0 r a*v t := by
    intro t ht
    have hh := hu.eigen t ht
    unfold tiltApply halfDensityApply at hh ⊢
    rw [he t ht,hd t ht,hdd t ht] at hh
    exact hh
  have hvn : latitudeNorm (k+2) 0 v=1 := by
    have heN : latitudeNorm (k+2) 0 v=latitudeNorm (k+2) 0 u := by
      unfold latitudeNorm
      apply intervalIntegral.integral_congr
      intro t ht
      change radialWeight (k+2) 0 t*(v t)^2=radialWeight (k+2) 0 t*(u t)^2
      rw [he t (by simpa using ht)]
    rw [heN,hu.normalized]
  refine ⟨v,hv,⟨hv2,fun t ht => hvp t ⟨ht.1.le,ht.2.le⟩,hvn,hve,
    positive_tilt_eigenprofile_rayleigh (k+2) (by omega) lam0 r a _ v hv2 hvp hve⟩,hvp,s,hs,hvs⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)]

omit [FiniteDimensional ℝ E] in
/-- D* applied to the actual auxiliary profile produces a truly smooth
physical sphere radial observable. Its first profile derivative at both
poles is controlled by compatible finite profiles of the same sphere state. -/
theorem actual_auxiliary_profile_radialRecover_contMDiff (p : E) (hp : ‖p‖=1)
    (r lam : ℝ) (psi : ℝ → ℝ) (hpsi : ContDiff ℝ 2 psi)
    (s : C^∞⟮𝓡 (n+2),RoundSphere n;ℝ⟯) (hs : ConstantOnLatitudes n s)
    (hps : ∀ z,s z=psi ((roundCoordinate n).toFun z)) :
    ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (fun x : sphere (0 : E) 1 =>
      radialRecover n r lam (weightedProfileFromHalfDensity r psi) ⟪p,(x : E)⟫_ℝ) := by
  let u := weightedProfileFromHalfDensity r psi
  have hu : ContDiff ℝ 2 u := weightedProfileFromHalfDensity_smooth r psi hpsi
  apply contMDiff_infty.mpr
  intro m
  obtain ⟨phi,hphi,hphis⟩ := round_smooth_same_latitude_exists_finite_profile (m+1) n s hs
  let v := weightedProfileFromHalfDensity r phi
  have hv : ContDiff ℝ ((m+1 : ℕ) : ℕ∞ω) v :=
    ((contDiff_const.mul contDiff_id).exp).mul hphi
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by exact_mod_cast (show (1 : ℕ) ≤ m + 1 from Nat.succ_le_succ (Nat.zero_le m)))
  have he : ∀ t ∈ Icc (-1 : ℝ) 1,u t=v t := by
    intro t ht
    have hh := round_profiles_eq_on_Icc n s psi phi hps hphis t ht
    dsimp only [u,v,weightedProfileFromHalfDensity,halfDensityLift]
    rw [hh]
  have hed := C1_profiles_deriv_eq_on_Icc u v (hu.of_le (by decide)) hv1 he
  have hv' : ContDiff ℝ ((m : ℕ∞ω)+1) v := by
    simpa only [Nat.cast_add,Nat.cast_one] using hv
  have hvd : ContDiff ℝ (m : ℕ∞ω) (deriv v) := hv'.deriv'
  have hvm : ContDiff ℝ (m : ℕ∞ω) v := hv.of_le (by exact_mod_cast Nat.le_succ m)
  have hrec : ContDiff ℝ (m : ℕ∞ω) (radialRecover n r lam v) := by
    change ContDiff ℝ (m : ℕ∞ω) (fun t =>
      (-(1-t^2)*deriv v t+((n : ℝ)*t-r*(1-t^2))*v t)/lam)
    fun_prop
  have ht : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) (m : ℕ∞ω) (innerCoordFun (n := n) p) :=
    (innerCoordFun (n := n) p).contMDiff.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfun : (fun x : sphere (0 : E) 1 => radialRecover n r lam u ⟪p,(x : E)⟫_ℝ)=
      fun x : sphere (0 : E) 1 => radialRecover n r lam v ⟪p,(x : E)⟫_ℝ := by
    funext x
    have hb := abs_real_inner_le_norm p (x : E)
    rw [hp,norm_eq_of_mem_sphere x,mul_one] at hb
    have hx := abs_le.mp hb
    dsimp only [radialRecover,radialAdjoint]
    rw [he _ hx,hed _ hx]
  change ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) (m : ℕ∞ω) (fun x : sphere (0 : E) 1 => radialRecover n r lam u ⟪p,(x : E)⟫_ℝ)
  rw [hfun]
  exact hrec.contMDiff.comp ht

end DFLSphere
