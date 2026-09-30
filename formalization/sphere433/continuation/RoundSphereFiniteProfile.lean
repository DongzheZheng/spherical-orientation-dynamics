import continuation.PhysicalSphereFiniteProfile
import continuation.RoundSphereLatitudeProfileC3
import continuation.OriginalWeightedGround
import continuation.TransverseSphereMode

/-! The same genuine auxiliary smooth zonal sphere function supplies
compatible profiles of every finite order. This proves smoothness of its
physical transverse mode without a global real C-infinity extension. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold Metric Module Set
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLPhysicalLatitude DFLTransverseSphere DFL.Spectral
namespace DFLSphere

/-- Every finite order of original auxiliary pole regularity is a
consequence of genuine smoothness and actual zonality. -/
theorem round_smooth_same_latitude_exists_finite_profile (m k : ℕ)
    (s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (hlat : ConstantOnLatitudes k s) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (m : ℕ∞ω) v ∧
      ∀ x : RoundSphere k, s x = v ((roundCoordinate k).toFun x) := by
  have hp : PhysicalConstantOnLatitudes (k+1) s := hlat
  obtain ⟨v,hv,hvs⟩ := physical_smooth_same_latitude_exists_finite_profile m (k+1) s hp
  exact ⟨v,hv,hvs⟩

/-- All genuine profiles of one actual auxiliary function agree on the
closed physical latitude interval, including both poles. -/
theorem round_profiles_eq_on_Icc (k : ℕ)
    (s : RoundSphere k → ℝ) (u v : ℝ → ℝ)
    (hu : ∀ x, s x = u ((roundCoordinate k).toFun x))
    (hv : ∀ x, s x = v ((roundCoordinate k).toFun x)) :
    ∀ t ∈ Icc (-1 : ℝ) 1, u t = v t := by
  intro t ht
  obtain ⟨x,hx⟩ := roundCoordinate_surjective_Icc k t ht
  rw [← hx,← hu x,← hv x]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+1)]

omit [FiniteDimensional ℝ E] in
/-- A profile of a genuine smooth auxiliary state gives a genuine smooth
physical transverse mode. Compatible finite profiles prove all orders;
no single global real C-infinity profile is needed as an assumption. -/
theorem actual_auxiliary_profile_transverse_contMDiff (p a : E) (hp : ‖p‖ = 1)
    (r : ℝ) (psi : ℝ → ℝ) (s : C^∞⟮𝓡 (n+2), RoundSphere n; ℝ⟯)
    (hs : ConstantOnLatitudes n s)
    (hpsi : ∀ z, s z = psi ((roundCoordinate n).toFun z)) :
    ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞
      (transverseMode p a (weightedProfileFromHalfDensity r psi)) := by
  apply contMDiff_infty.mpr
  intro m
  obtain ⟨phi,hphi,hphis⟩ := round_smooth_same_latitude_exists_finite_profile m n s hs
  let v := weightedProfileFromHalfDensity r phi
  have hv : ContDiff ℝ (m : ℕ∞ω) v :=
    ((contDiff_const.mul contDiff_id).exp).mul hphi
  have ht : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) (m : ℕ∞ω) (innerCoordFun (n := n) p) :=
    (innerCoordFun (n := n) p).contMDiff.of_le (WithTop.coe_le_coe.mpr le_top)
  have ha : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) (m : ℕ∞ω) (innerCoordFun (n := n) a) :=
    (innerCoordFun (n := n) a).contMDiff.of_le (WithTop.coe_le_coe.mpr le_top)
  have hmode : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) (m : ℕ∞ω) (transverseMode p a v) :=
    ha.mul (hv.contMDiff.comp ht)
  have hfun : transverseMode p a (weightedProfileFromHalfDensity r psi) = transverseMode p a v := by
    funext x
    have hb := abs_real_inner_le_norm p (x : E)
    rw [hp,norm_eq_of_mem_sphere x,mul_one] at hb
    have he := round_profiles_eq_on_Icc n s psi phi hpsi hphis _ (abs_le.mp hb)
    dsimp [transverseMode,v,weightedProfileFromHalfDensity,halfDensityLift]
    rw [he]
  rw [hfun]
  exact hmode

end DFLSphere
