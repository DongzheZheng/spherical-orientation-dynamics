import continuation.TiltHellmannFeynman
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Continuity of the genuine spectral response, derived from the actual
positive ground and its bounded multiplication operator. No differentiable
eigenfunction branch is a hypothesis. -/
noncomputable section
open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator
namespace DFLSphere
private local instance (k : ℕ) : MeasurableSpace (RoundSphere k) := borel (RoundSphere k)
private local instance (k : ℕ) : BorelSpace (RoundSphere k) := ⟨rfl⟩
private local instance (k : ℕ) : IsFiniteMeasure (roundVolume k) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (roundSphereMetric k)

/-- The exact HF response is the expectation of the actual bounded
potential-derivative operator in the same normalized positive ground. -/
theorem roundTiltMinimum_deriv_r_operator (k : ℕ) (lam0 a r : ℝ) :
    deriv (fun s => roundTiltMinimum k lam0 s a) r =
      ⟪(roundContinuousPotentialOperator k (roundTiltLinearPotential k a) +
          (2*r) • roundContinuousPotentialOperator k (roundTiltQuadraticPotential k))
        (smoothToLp (roundSphereMetric k) (positiveGround k (roundTiltSmoothPotential k lam0 r a))),
        smoothToLp (roundSphereMetric k) (positiveGround k (roundTiltSmoothPotential k lam0 r a))⟫_ℝ := by
  rw [roundTiltMinimum_deriv_r]
  let Vd := roundTiltLinearPotential k a+(2*r) • roundTiltQuadraticPotential k
  have hop : roundContinuousPotentialOperator k (roundTiltLinearPotential k a) +
      (2*r) • roundContinuousPotentialOperator k (roundTiltQuadraticPotential k) =
      roundContinuousPotentialOperator k Vd := by rw [map_add,map_smul]
  rw [hop]
  have hVd : MemLp (Vd : RoundSphere k → ℝ) ∞ (roundVolume k) :=
    Vd.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [roundContinuousPotentialOperator_eq k Vd hVd,boundedPotentialMultiplication_inner]
  apply integral_congr_ae
  filter_upwards [(positiveGround k (roundTiltSmoothPotential k lam0 r a)).memLp_two.coeFn_toLp] with x hx
  have he : smoothToLp (roundSphereMetric k)
      (positiveGround k (roundTiltSmoothPotential k lam0 r a)) x =
      (positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x := hx
  rw [he]
  change (r*(1-((roundCoordinate k).toFun x)^2)/2-a*(roundCoordinate k).toFun x)*
      (positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x ^ 2 =
    (-a*(roundCoordinate k).toFun x+(2*r)*((1-((roundCoordinate k).toFun x)^2)/4))*
      (positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x*
      (positiveGround k (roundTiltSmoothPotential k lam0 r a)).toFun x
  ring

/-- The actual derivative is continuous on the entire real field axis. -/
theorem roundTiltMinimum_continuous_deriv_r (k : ℕ) (lam0 a : ℝ) :
    Continuous (deriv (fun r => roundTiltMinimum k lam0 r a)) := by
  let u := fun r => smoothToLp (roundSphereMetric k)
    (positiveGround k (roundTiltSmoothPotential k lam0 r a))
  have hu : Continuous u := by
    have h := (H1ComplToLp (roundSphereMetric k)).continuous.comp
      (roundTiltPositiveGround_continuous_r k lam0 a)
    simpa only [Function.comp_def, H1ComplToLp_smoothToH1Compl, u] using h
  let B := roundContinuousPotentialOperator k (roundTiltLinearPotential k a)
  let C := roundContinuousPotentialOperator k (roundTiltQuadraticPotential k)
  have hop : Continuous (fun r : ℝ => B+(2*r) • C) := by fun_prop
  have he : deriv (fun r => roundTiltMinimum k lam0 r a) =
      fun r => ⟪(B+(2*r) • C) (u r),u r⟫_ℝ := by
    funext r
    exact roundTiltMinimum_deriv_r_operator k lam0 a r
  rw [he]
  exact (hop.clm_apply hu).inner hu

/-- The true variational minimum is C¹ in field strength. Its regularity
is proved, rather than supplied as a ground-branch assumption. -/
theorem roundTiltMinimum_contDiff_one_r (k : ℕ) (lam0 a : ℝ) :
    ContDiff ℝ 1 (fun r => roundTiltMinimum k lam0 r a) :=
  contDiff_one_iff_deriv.mpr ⟨roundTiltMinimum_differentiable_r k lam0 a,
    roundTiltMinimum_continuous_deriv_r k lam0 a⟩

end DFLSphere
