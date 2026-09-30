import continuation.PotentialMinimumDependence
import continuation.RoundSphereGroundAxisymmetry
import continuation.RoundSphereFiniteProfile
import DFLSphere433.LatitudePiconeGround
import continuation.RoundSphereLatitudeOperator
import DFLSphere433.OriginalLatitude.GroundConcavity

/-! The actual positive full-sphere ground supplies the original global
C² latitude profile and its exact closed-interval differential equation.
The pole regularity and latitude constancy are conclusions, not inputs. -/
noncomputable section
open Bundle Manifold Metric Module MeasureTheory Set
open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Laplacian
open DFLGroundAxisymmetry DFLLatitudeOperator DFL.Spectral

namespace DFLSphere

/-- The original latitude eigenprofile exists at the actual full-domain
minimum for every real tilt parameter, including the zero field. -/
theorem round_tilt_positive_profile_actual_witness (k : ℕ) (lam0 r a : ℝ) :
    ∃ s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯,
      ConstantOnLatitudes k s ∧ ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      (∀ x, s x = v ((roundCoordinate k).toFun x)) ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t) ∧
      ∀ t ∈ Icc (-1 : ℝ) 1,
        tiltApply (k+2) lam0 r a v t = roundTiltMinimum k lam0 r a * v t := by
  obtain ⟨lam,u,hn,hpos,he,hmin,heig⟩ :=
    round_tilt_positive_smooth_ground_exists k lam0 r a
  obtain ⟨W,hWn,hWe,hWmin⟩ := roundPotentialMinimum_minimizer k
    (roundTiltPotential k lam0 r a) (roundTiltPotential_continuous k lam0 r a)
  have hun : ‖H1ComplToLp (roundSphereMetric k)
      (smoothToH1Compl (roundSphereMetric k) u)‖ = 1 := by
    simpa only [H1ComplToLp_smoothToH1Compl] using hn
  have h1 := hmin W
  rw [hWn,one_pow,mul_one,hWe] at h1
  have h2 := hWmin (smoothToH1Compl (roundSphereMetric k) u)
  rw [hun,one_pow,mul_one,he] at h2
  have hlam : lam = roundTiltMinimum k lam0 r a := le_antisymm h1 h2
  let axis : RoundAmbient k := EuclideanSpace.single 0 1
  have haxis : ‖axis‖ = 1 := by simp [axis]
  let F : ℝ → ℝ := fun t => lam0+r^2/4*(1-t^2)-a*r*t
  have hF : Continuous F := by fun_prop
  have heig' : ∀ x : RoundSphere k,
      -ΔG (roundMetric (E := RoundAmbient k) (n := k+2)) u.toContMDiffMap x +
        F ⟪axis,(x : RoundAmbient k)⟫_ℝ * u.toContMDiffMap x =
          lam * u.toContMDiffMap x := by
    intro x
    exact heig x
  have hlat : ConstantOnLatitudes k u.toContMDiffMap := by
    intro x y hxy
    exact positive_latitude_eigenfunction_same_latitude (n := k+2)
      axis haxis F hF u.toContMDiffMap hpos lam heig' x y hxy
  obtain ⟨v,hv,hvs⟩ := round_smooth_same_latitude_exists_finite_profile 2 k u.toContMDiffMap hlat
  have hvp : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t := by
    intro t ht
    obtain ⟨x,hx⟩ := roundCoordinate_surjective_Icc k t ht
    rw [← hx,← hvs x]
    exact hpos x
  refine ⟨u.toContMDiffMap,hlat,v,hv,hvs,hvp,?_⟩
  intro t ht
  obtain ⟨x,hx⟩ := roundCoordinate_surjective_Icc k t ht
  have hvs' : ∀ y : RoundSphere k,
      u.toContMDiffMap y = v ⟪axis,(y : RoundAmbient k)⟫_ℝ := hvs
  have hh := latitude_schrodinger_equation (n := k+2) axis haxis F v hv
    u.toContMDiffMap hvs' lam heig' x
  change -(1-((roundCoordinate k).toFun x)^2)*deriv (deriv v) ((roundCoordinate k).toFun x)+
    ((k+2 : ℕ) : ℝ)*(roundCoordinate k).toFun x*deriv v ((roundCoordinate k).toFun x)+
    F ((roundCoordinate k).toFun x)*v ((roundCoordinate k).toFun x) =
      lam*v ((roundCoordinate k).toFun x) at hh
  rw [hx,hlam] at hh
  dsimp [F] at hh
  unfold tiltApply halfDensityApply halfDensityPotential
  convert hh using 1
  ring

/-- The actual normalized original ground retains a genuine smooth zonal
auxiliary sphere representative, so all finite pole profiles apply. -/
theorem original_tilt_ground_actual_witness (k : ℕ) (lam0 r a : ℝ) :
    ∃ psi : ℝ → ℝ,
      IsTiltGroundProfile (k+2) lam0 r a (roundTiltMinimum k lam0 r a) psi ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, 0 < psi t) ∧
      ∃ s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯,
        ConstantOnLatitudes k s ∧ ∀ x, s x = psi ((roundCoordinate k).toFun x) := by
  obtain ⟨s,hs,v,hv,hvs,hpos,he⟩ := round_tilt_positive_profile_actual_witness k lam0 r a
  obtain ⟨psi,hpsi,hpp,hpsiv⟩ := positive_tilt_eigenprofile_normalized_ground (k+2) (by omega)
    lam0 r a _ v hv hpos he
  let S : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯ :=
    ⟨fun x => s x/Real.sqrt (latitudeNorm (k+2) 0 v),s.contMDiff.div_const _⟩
  refine ⟨psi,hpsi,hpp,S,?_,?_⟩
  · intro x y hxy
    change s x/Real.sqrt (latitudeNorm (k+2) 0 v) = s y/Real.sqrt (latitudeNorm (k+2) 0 v)
    rw [hs x y hxy]
  · intro x
    change s x/Real.sqrt (latitudeNorm (k+2) 0 v) = psi ((roundCoordinate k).toFun x)
    rw [hpsiv,hvs x]

end DFLSphere
