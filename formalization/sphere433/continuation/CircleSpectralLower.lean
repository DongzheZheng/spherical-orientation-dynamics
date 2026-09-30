import continuation.CircleRoundMetric
import continuation.CircleFourierFrequency

/-! The actual positive spectrum of the round unit circle has lower bound
one, derived from its computed periodic ODE and proved Fourier completeness. -/
noncomputable section
open Bundle Manifold Metric Module Set Complex
open scoped Manifold Topology ContDiff RealInnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator

namespace DFLCircleRound

abbrev SmoothCircleReal := C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯

def realParameterDerivative (F : SmoothCircleReal) : SmoothCircleReal :=
  ⟨fun z => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) F z (AddCircle.parameterTangent z),
    AddCircle.contMDiff_mfderiv_parameterTangent F.contMDiff (by simp) le_rfl⟩

def complexification (F : SmoothCircleReal) : DFLCircleFourier.SmoothCircleComplex :=
  ⟨fun z => (F z : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp F.contMDiff⟩

private theorem hasDerivAt_real_comp_coe (F : SmoothCircleReal) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (s : AddCircle (1 : ℝ)))
      (realParameterDerivative F (t : AddCircle (1 : ℝ))) t := by
  have hs := (F.contMDiff.comp AddCircle.contMDiff_coe).contDiff
  have hd := (hs.differentiable (by simp)).differentiableAt.hasDerivAt (x := t)
  change HasDerivAt (fun s : ℝ => F (s : AddCircle (1 : ℝ)))
    (deriv (fun s : ℝ => F (s : AddCircle (1 : ℝ))) t) t at hd
  rw [AddCircle.deriv_comp_coe (F.contMDiff.mdifferentiableAt (by simp))] at hd
  exact hd

theorem parameterDerivative_complexification (F : SmoothCircleReal) :
    DFLCircleFourier.parameterDerivative (complexification F) =
      complexification (realParameterDerivative F) := by
  ext z
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [DFLCircleFourier.parameterDerivative_coe]
  change deriv (fun s : ℝ => (F (s : AddCircle (1 : ℝ)) : ℂ)) t =
    (realParameterDerivative F (t : AddCircle (1 : ℝ)) : ℂ)
  exact (hasDerivAt_real_comp_coe F t).ofReal_comp.deriv

private theorem realParameterDerivative_twice_coe (F : SmoothCircleReal) (t : ℝ) :
    realParameterDerivative (realParameterDerivative F) (t : AddCircle (1 : ℝ)) =
      deriv (deriv (fun s : ℝ => F (s : AddCircle (1 : ℝ)))) t := by
  exact (AddCircle.deriv_deriv_comp_coe (F.contMDiff.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)) t).symm

/-- The genuine round-circle positive eigenvalue lower bound. The only
state hypotheses are smoothness, its pointwise eigen-equation and nonzero. -/
theorem circle_positive_eigenvalue_ge_one
    (f : C^∞⟮𝓡 1, UnitRoundCircle; ℝ⟯) (lam : ℝ) (hlam : 0 < lam)
    (hf : ∃ x, f x ≠ 0) (heig : ∀ x, ΔG circleRoundMetric f x = -lam * f x) :
    1 ≤ lam := by
  let F : SmoothCircleReal :=
    ⟨fun z => f (circleDiffeomorph z), f.contMDiff.comp circleDiffeomorph.contMDiff⟩
  apply DFLCircleFourier.periodic_eigenvalue_ge_one (complexification F) lam hlam
  · obtain ⟨x, hx⟩ := hf
    refine ⟨circleDiffeomorph.symm x, ?_⟩
    change (f (circleDiffeomorph (circleDiffeomorph.symm x)) : ℂ) ≠ 0
    rw [circleDiffeomorph.apply_symm_apply]
    exact Complex.ofReal_ne_zero.mpr hx
  · intro z
    rw [parameterDerivative_complexification, parameterDerivative_complexification]
    change (realParameterDerivative (realParameterDerivative F) z : ℂ) =
      -((2 * Real.pi)^2 * lam : ℝ) * (F z : ℂ)
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [realParameterDerivative_twice_coe]
    have ho := circle_eigenfunction_periodic_ode f lam heig t
    change deriv (deriv (fun s : ℝ => F (s : AddCircle (1 : ℝ)))) t =
      -((2 * Real.pi)^2 * lam) * F (t : AddCircle (1 : ℝ)) at ho
    rw [ho]
    push_cast
    rfl

end DFLCircleRound
