import continuation.RoundCirclePoincare
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared

/-! Unified sharp Poincare constant n on the actual unit round S^n,
for every n≥1 and every full H1 or distributional weak H1 state.
The circle case uses the proved periodic Fourier endpoint; n≥2 uses
actual Ricci curvature and the proved closed-manifold Lichnerowicz theorem. -/
noncomputable section
open Bundle Manifold MeasureTheory Set Filter Metric Module
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp DFLWeakH1Completion

namespace DFLGenericRound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

abbrev roundVolume :=
  riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))

/-- Actual full H1 form on a generic unit round sphere, including S¹. -/
theorem round_sphere_h1_poincare (hn : 1 ≤ n)
    (U : H1Compl (roundMetric (E := E) (n := n)))
    (hmean : (∫ x : sphere (0 : E) 1,
      (H1ComplToLp (roundMetric (E := E) (n := n)) U) x ∂(roundVolume (E := E) (n := n))) = 0) :
    (n : ℝ) * ‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖ ^ 2 ≤
      ‖U‖ ^ 2 - ‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖ ^ 2 := by
  by_cases heq : n = 1
  · subst n
    simpa only [Nat.cast_one, one_mul] using DFLRoundCircle.round_circle_h1_poincare U hmean
  have hn2 : 2 ≤ n := by omega
  let _ : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := ⟨by simp; omega⟩
  let _ : ConnectedSpace (sphere (0 : E) 1) := by
    apply Subtype.connectedSpace
    apply isConnected_sphere _ _ (by norm_num : (0 : ℝ) ≤ 1)
    rw [← Module.finrank_eq_rank, (Fact.out : finrank ℝ E = n + 1)]
    exact_mod_cast (show 1 < n + 1 by omega)
  have hRic : ∀ x : sphere (0 : E) 1, ∀ X : TangentSpace (𝓡 n) x,
      ((finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1) * 1 *
        (roundMetric (E := E) (n := n)).inner x X X ≤
      ricciTensor (I := 𝓡 n) (roundMetric (E := E) (n := n)) x X X := by
    intro x X
    rw [ricciTensor_roundSphere]
    simp
  have hdim : 2 ≤ finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simpa using hn2
  simpa only [finrank_euclideanSpace, Fintype.card_fin, mul_one] using
    DFLSphere.h1_poincare_of_positive_ricci (roundMetric (E := E) (n := n)) hdim 1
      (by norm_num) hRic U hmean

/-- Distributional weak H1 with the actual given intrinsic L2 gradient. -/
theorem round_sphere_weakH1_poincare (hn : 1 ≤ n) (u : sphere (0 : E) 1 → ℝ)
    (hu : MemLp u 2 (roundVolume (E := E) (n := n)))
    (G : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (hG : HasWeakRiemannianGradLp (roundMetric (E := E) (n := n)) u G)
    (hGn : MemLp (metricNorm (roundMetric (E := E) (n := n)) G) 2 (roundVolume (E := E) (n := n)))
    (hmean : (∫ x, u x ∂(roundVolume (E := E) (n := n))) = 0) :
    (n : ℝ) * (∫ x, u x ^ 2 ∂(roundVolume (E := E) (n := n))) ≤
      ∫ x, (roundMetric (E := E) (n := n)).inner x (G x) (G x) ∂(roundVolume (E := E) (n := n)) := by
  let _ : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := ⟨by simp; omega⟩
  let g := roundMetric (E := E) (n := n)
  obtain ⟨U, hU, hE⟩ := weakH1_function_exists_completion_energy g u hu G hG hGn
  have hm : (∫ x, (H1ComplToLp g U) x ∂(roundVolume (E := E) (n := n))) = 0 :=
    (integral_congr_ae hU).trans hmean
  have hnorm : ‖H1ComplToLp g U‖ ^ 2 = ∫ x, u x ^ 2 ∂(roundVolume (E := E) (n := n)) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hU] with x hx
    rw [hx, Real.inner_apply, pow_two]
  have h := round_sphere_h1_poincare hn U hm
  rw [hE, hnorm] at h
  exact h

/-- Smooth version with the ordinary actual angular gradient energy. -/
theorem round_sphere_smooth_poincare (hn : 1 ≤ n)
    (f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯)
    (hmean : (∫ x, f x ∂(roundVolume (E := E) (n := n))) = 0) :
    (n : ℝ) * (∫ x, (f x)^2 ∂(roundVolume (E := E) (n := n))) ≤
      ∫ x, normGradSqFun (roundMetric (E := E) (n := n)) f x ∂(roundVolume (E := E) (n := n)) := by
  let g := roundMetric (E := E) (n := n)
  let s : SmoothScalar g := ⟨f, f.contMDiff⟩
  have hm : (∫ x, (H1ComplToLp g (smoothToH1Compl g s)) x ∂(roundVolume (E := E) (n := n))) = 0 := by
    rw [H1ComplToLp_smoothToH1Compl]
    exact (integral_congr_ae (MemLp.coeFn_toLp s.memLp_two)).trans hmean
  have he := DFLSphere.h1_smooth_energy g s
  have hnorm : ‖H1ComplToLp g (smoothToH1Compl g s)‖ ^ 2 =
      ∫ x, (f x)^2 ∂(roundVolume (E := E) (n := n)) := by
    rw [H1ComplToLp_smoothToH1Compl]
    calc
      _ = ∫ x, f x * f x ∂(roundVolume (E := E) (n := n)) := s.norm_smoothToLp_sq
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
  have h := round_sphere_h1_poincare hn (smoothToH1Compl g s) hm
  rw [he, hnorm] at h
  exact h

end DFLGenericRound
