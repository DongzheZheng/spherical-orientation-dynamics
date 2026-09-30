import continuation.CompactC2WeakH1
import DFLSphere433.RoundSpherePotentialGround

/-! A genuine smooth classical Schrödinger eigenfunction satisfies the
actual full H¹ variational equation. The upstream smooth bridge already
extends the one-minus-Laplacian identity to every completion test. -/
noncomputable section
open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DFLSphere

namespace DFLClassicalPotentialWeak
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Actual classical PDE implies the full original variational identity,
for the actual bounded multiplication operator and every H¹ test. -/
theorem smooth_classical_potential_eigen_weak (g : SmoothRiemannianMetric I M)
    (V : M → ℝ) (hV : MemLp V ∞ (riemannianVolumeMeasure I M g))
    (lam : ℝ) (s : SmoothScalar g)
    (heig : ∀ x, -ΔG g s.toContMDiffMap x+V x*s.toFun x=lam*s.toFun x) :
    ∀ W : H1Compl g,
      potentialForm (H1ComplToLp g) (boundedPotentialMultiplication V hV)
        (smoothToH1Compl g s) W = lam*⟪H1ComplToLp g (smoothToH1Compl g s),H1ComplToLp g W⟫_ℝ := by
  let J := H1ComplToLp g
  let P := boundedPotentialMultiplication V hV
  have hL : smoothToLp g s.oneSubLapClassical =
      (1+lam) • smoothToLp g s-P (smoothToLp g s) := by
    apply Lp.ext
    filter_upwards [s.oneSubLapClassical.memLp_two.coeFn_toLp,s.memLp_two.coeFn_toLp,
      boundedPotentialMultiplication_ae V hV (smoothToLp g s),
      Lp.coeFn_sub ((1+lam) • smoothToLp g s) (P (smoothToLp g s)),
      Lp.coeFn_smul (1+lam) (smoothToLp g s)] with x hx hs hp hsub hsmul
    have hs' : (smoothToLp g s : M → ℝ) x = s.toFun x := hs
    have hx' : (smoothToLp g s.oneSubLapClassical : M → ℝ) x =
        s.oneSubLapClassical.toFun x := hx
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hsmul,hp]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hs',hx']
    change s.toFun x-ΔG g s.toContMDiffMap x = (1+lam)*s.toFun x-V x*s.toFun x
    linarith [heig x]
  intro W
  have hh := smoothToH1Compl_bilin_eq_lpFunctional s W
  rw [lpFunctionalCLM_apply,hL] at hh
  change ⟪smoothToH1Compl g s,W⟫_ℝ =
    ⟪J W,(1+lam) • smoothToLp g s-P (smoothToLp g s)⟫_ℝ at hh
  rw [inner_sub_right,real_inner_smul_right] at hh
  unfold potentialForm
  rw [H1ComplToLp_smoothToH1Compl,hh,real_inner_comm (J W) (smoothToLp g s),
    real_inner_comm (J W) (P (smoothToLp g s))]
  ring

end DFLClassicalPotentialWeak
