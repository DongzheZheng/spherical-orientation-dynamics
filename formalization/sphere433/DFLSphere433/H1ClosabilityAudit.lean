import DifferentialGeometry.Analysis.Elliptic.Operator.SmoothBridge

/-!
Standalone upstream Lean 4.33.1 compatibility experiment.
This is not imported by the pinned DFL Lean 4.29.0 project.
The theorem fills the full value-injectivity bridge of upstream's
actual smooth H¹ completion using its proved integration by parts.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DFLSpectralUpstreamAudit

open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem H1ComplToLp_injective (g : SmoothRiemannianMetric I M) :
    Function.Injective (H1ComplToLp (I := I) (M := M) g) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have hcomp :
      (fun w : H1Compl g => ⟪w, u⟫_ℝ) ∘
        (smoothToH1Compl (I := I) (M := M) g) =
      (fun _ : SmoothScalar g => (0 : ℝ)) := by
    funext v
    change ⟪smoothToH1Compl (I := I) (M := M) g v, u⟫_ℝ = 0
    rw [smoothToH1Compl_eq_resolvent_oneSubLap,
      resolvent_inner_eq_lpFunctional, hu, inner_zero_left]
  have hall : (fun w : H1Compl g => ⟪w, u⟫_ℝ) =
      (fun _ : H1Compl g => (0 : ℝ)) :=
    (denseRange_smoothToH1Compl (I := I) (M := M) g).equalizer
      (continuous_id.inner continuous_const) continuous_const hcomp
  have hself : ⟪u, u⟫_ℝ = 0 := congrFun hall u
  exact inner_self_eq_zero.mp hself

end DFLSpectralUpstreamAudit

#print axioms DFLSpectralUpstreamAudit.H1ComplToLp_injective

