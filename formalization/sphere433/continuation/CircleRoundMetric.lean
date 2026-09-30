import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Operator.Laplacian.AddCircleScaling
import DifferentialGeometry.Geometry.Operator.Laplacian.Pullback
import DifferentialGeometry.Bundle.PartialMfderiv.Composition
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification

/-! The true round unit circle and its genuine periodic coordinate.
The metric factor is derived from the actual circle exponential derivative.
No circle Poincare inequality or supplied metric identity is used. -/
noncomputable section
open Bundle Manifold Metric Module Set
open scoped Manifold Topology ContDiff RealInnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection

namespace DFLCircleRound

private instance : Fact (finrank ℝ ℂ = 1 + 1) := Complex.finrank_real_complex_fact

abbrev UnitRoundCircle := sphere (0 : ℂ) 1

def circleDiffeomorph : Diffeomorph 𝓘(ℝ, ℝ) (𝓡 1)
    (AddCircle (1 : ℝ)) UnitRoundCircle ∞ := AddCircle.diffeomorphCircle

abbrev circleRoundMetric : SmoothRiemannianMetric (𝓡 1) UnitRoundCircle :=
  roundMetric (E := ℂ) (n := 1)

private theorem circleDiffeomorph_coe (t : ℝ) :
    (circleDiffeomorph (t : AddCircle (1 : ℝ)) : ℂ) =
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  change (AddCircle.homeomorphCircle one_ne_zero (t : AddCircle (1 : ℝ)) : ℂ) = _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  rw [Circle.coe_exp]
  congr 1
  simp

/-- The true ambient velocity of the unit circle's periodic coordinate. -/
theorem circleDiffeomorph_ambient_velocity (t : ℝ) :
    dIncl (n := 1) (circleDiffeomorph (t : AddCircle (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) circleDiffeomorph
        (t : AddCircle (1 : ℝ)) (AddCircle.parameterTangent (t : AddCircle (1 : ℝ)))) =
      (circleDiffeomorph (t : AddCircle (1 : ℝ)) : ℂ) *
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
  let c : AddCircle (1 : ℝ) → ℂ := fun z => (circleDiffeomorph z : ℂ)
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ c :=
    contMDiff_coe_sphere.comp circleDiffeomorph.contMDiff
  have hι : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ)
      ((↑) : UnitRoundCircle → ℂ) (circleDiffeomorph (t : AddCircle (1 : ℝ))) :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1)).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hΦ := circleDiffeomorph.contMDiff.mdifferentiableAt
    (by decide : (∞ : ℕ∞ω) ≠ 0) (x := (t : AddCircle (1 : ℝ)))
  have hchain := hι.mvfderiv_comp_apply hΦ (AddCircle.parameterTangent (t : AddCircle (1 : ℝ)))
  have hval : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) c (t : AddCircle (1 : ℝ))
      (AddCircle.parameterTangent (t : AddCircle (1 : ℝ))) =
      dIncl (n := 1) (circleDiffeomorph (t : AddCircle (1 : ℝ)))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) circleDiffeomorph
          (t : AddCircle (1 : ℝ)) (AddCircle.parameterTangent (t : AddCircle (1 : ℝ)))) := by
    with_unfolding_all exact hchain
  have hderiv : HasDerivAt (fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) *
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) t := by
    have hR : HasDerivAt (fun s : ℝ => 2 * Real.pi * s) (2 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
    exact ((hR.ofReal_comp).mul_const Complex.I).cexp
  have he : (fun s : ℝ => c (s : AddCircle (1 : ℝ))) =
      fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) :=
    funext circleDiffeomorph_coe
  rw [← hval, ← AddCircle.deriv_comp_coe (hc.mdifferentiableAt
    (by decide : (∞ : ℕ∞ω) ≠ 0)), he, hderiv.deriv, circleDiffeomorph_coe]

/-- Actual pullback of the unit-circle round metric is the circumference
squared times the genuine period-one flat metric. -/
theorem circleDiffeomorph_pullback_round :
    Diffeomorph.pullbackMetricCross circleRoundMetric circleDiffeomorph =
      scaleMetric ((2 * Real.pi)^2) (sq_pos_of_pos (by positivity)) AddCircle.flatMetric := by
  apply AddCircle.metricCoefficient_injective
  ext z
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [AddCircle.metricCoefficient_apply, Diffeomorph.pullbackMetricCross_inner]
  change (roundMetric (E := ℂ) (n := 1)).inner _ _ _ = _
  rw [roundMetric_inner, circleDiffeomorph_ambient_velocity, real_inner_self_eq_norm_sq]
  have hu : ‖(circleDiffeomorph (t : AddCircle (1 : ℝ)) : ℂ)‖ = 1 :=
    norm_eq_of_mem_sphere _
  have hv : ‖(circleDiffeomorph (t : AddCircle (1 : ℝ)) : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, hu, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    ring
  rw [hv]
  exact (AddCircle.metricCoefficient_scaleMetric_flatMetric _ _ _).symm

/-- A pointwise round-circle eigenfunction has the actual periodic ODE,
with the metric scale computed above. -/
theorem circle_eigenfunction_periodic_ode
    (f : C^∞⟮𝓡 1, UnitRoundCircle; ℝ⟯) (lam : ℝ)
    (heig : ∀ x, ΔG circleRoundMetric f x = -lam * f x) (t : ℝ) :
    deriv (deriv (fun s : ℝ => f (circleDiffeomorph (s : AddCircle (1 : ℝ))))) t =
      -((2 * Real.pi)^2 * lam) *
        f (circleDiffeomorph (t : AddCircle (1 : ℝ))) := by
  have hp := laplacian_pullbackCross circleRoundMetric circleDiffeomorph
    (f.contMDiff.contMDiffAt.of_le (by decide : (2 : ℕ∞ω) ≤ ∞))
      (x := (t : AddCircle (1 : ℝ)))
  rw [circleDiffeomorph_pullback_round] at hp
  rw [AddCircle.laplacian_scaleMetric_flatMetric_coe _ _
    ((f.contMDiff.comp circleDiffeomorph.contMDiff).contMDiffAt.of_le
      (by decide : (2 : ℕ∞ω) ≤ ∞))] at hp
  change ((2 * Real.pi)^2)⁻¹ *
    deriv (deriv (fun s : ℝ => f (circleDiffeomorph (s : AddCircle (1 : ℝ))))) t =
      laplacian (LeviCivita circleRoundMetric) circleRoundMetric f
        (circleDiffeomorph (t : AddCircle (1 : ℝ))) at hp
  have hright := laplacian_levi_eq circleRoundMetric f.contMDiff
    (circleDiffeomorph (t : AddCircle (1 : ℝ)))
  change laplacian (LeviCivita circleRoundMetric) circleRoundMetric f
    (circleDiffeomorph (t : AddCircle (1 : ℝ))) =
      ΔG circleRoundMetric f (circleDiffeomorph (t : AddCircle (1 : ℝ))) at hright
  rw [hright, heig] at hp
  have hs : (2 * Real.pi)^2 ≠ 0 := ne_of_gt (sq_pos_of_pos (by positivity))
  field_simp [hs] at hp
  nlinarith [hp]

end DFLCircleRound
