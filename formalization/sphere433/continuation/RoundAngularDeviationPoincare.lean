import continuation.GenericRoundPoincare
import continuation.AngularMeanProjection

/-! The original angular projection's coercivity on genuine round fibers.
The transverse deviation is the actual angular mean subtraction of a
smooth product state. No full-sphere extension of this deviation is required. -/
noncomputable section
open Bundle Manifold MeasureTheory Set Filter Metric Module
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

namespace DFLGenericRound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- True Poincare coercivity on every angular slice of a smooth product
state, including the genuine circle fiber. -/
theorem round_product_slice_poincare (hn : 1 ≤ n)
    (F : C^∞⟮(𝓡 n).prod 𝓘(ℝ, ℝ), sphere (0 : E) 1 × ℝ; ℝ⟯) (s : ℝ)
    (hmean : (∫ y : sphere (0 : E) 1, F (y,s)
      ∂roundVolume (E := E) (n := n)) = 0) :
    (n : ℝ) * (∫ y : sphere (0 : E) 1, (F (y,s))^2
      ∂roundVolume (E := E) (n := n)) ≤
      ∫ y : sphere (0 : E) 1,
        normGradSqFun (roundMetric (E := E) (n := n))
          (fun z : sphere (0 : E) 1 => F (z,s)) y
        ∂roundVolume (E := E) (n := n) := by
  let f : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯ :=
    ⟨fun y => F (y,s), F.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)⟩
  exact round_sphere_smooth_poincare hn f hmean

/-- The actual angular mean subtraction automatically lies in the
transverse fiber, so the original angular energy controls its full L2 norm.
There is no zero-mean premise and no projected full-sphere regularity premise. -/
theorem round_angular_deviation_poincare (hn : 1 ≤ n)
    (F : C^∞⟮(𝓡 n).prod 𝓘(ℝ, ℝ), sphere (0 : E) 1 × ℝ; ℝ⟯) (s : ℝ) :
    (n : ℝ) * (∫ y : sphere (0 : E) 1,
      (DFLAngularMean.angularDeviation (roundMetric (E := E) (n := n)) F (y,s))^2
      ∂roundVolume (E := E) (n := n)) ≤
      ∫ y : sphere (0 : E) 1,
        normGradSqFun (roundMetric (E := E) (n := n))
          (fun z : sphere (0 : E) 1 => F (z,s)) y
        ∂roundVolume (E := E) (n := n) := by
  let _ : Nontrivial E := nontrivial_of_finrank_pos (R := ℝ) (by
    rw [(Fact.out : finrank ℝ E = n+1)]
    omega)
  let _ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).coe_sort
  let g := roundMetric (E := E) (n := n)
  have hmean := DFLAngularMean.angularDeviation_mean_zero g F s
  have hp := round_product_slice_poincare hn (DFLAngularMean.angularDeviation g F) s hmean
  apply hp.trans_eq
  apply integral_congr_ae
  filter_upwards [] with y
  have hg := DFLAngularMean.angularDeviation_gradient g F s y
  change gradFun g (fun z : sphere (0 : E) 1 =>
    DFLAngularMean.angularDeviation g F (z,s)) y =
      gradFun g (fun z : sphere (0 : E) 1 => F (z,s)) y at hg
  simp only [normGradSqFun_def]
  rw [hg]

end DFLGenericRound
