import continuation.PhysicalWeightedGap
import continuation.GenericRoundPoincare

/-! The zero-field lower bound on the same actual physical weighted gap,
including the true S¹ endpoint. -/
noncomputable section
open Bundle Manifold Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
namespace DFLPhysicalGap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)] [NeZero n]

/-- At zero field the original physical gap is at least the dimension,
from the actual sharp full H¹ round Poincaré theorem. -/
theorem actual_weighted_gap_zero_ge_dimension (p : E) (hp : ‖p‖=1) :
    (n : ℝ) ≤ weightedGap (n := n) p 0 := by
  obtain ⟨_,u,hM,hm,hE,_,_,_⟩ := actual_weighted_gap_spec (n := n) p hp 0
  have hmean : (∫ x,u x ∂DFLGenericRound.roundVolume (E := E) (n := n))=0 := by
    simpa only [weightedMean,zero_mul,Real.exp_zero,one_mul] using hm
  have hmass : (∫ x,(u x)^2 ∂DFLGenericRound.roundVolume (E := E) (n := n))=1 := by
    simpa only [weightedMass,zero_mul,Real.exp_zero,one_mul] using hM
  have henergy : (∫ x,normGradSqFun (roundMetric (E := E) (n := n)) u x
    ∂DFLGenericRound.roundVolume (E := E) (n := n))=weightedGap (n := n) p 0 := by
    simpa only [weightedEnergy,zero_mul,Real.exp_zero,one_mul] using hE
  have h := DFLGenericRound.round_sphere_smooth_poincare (by have := NeZero.pos n; omega) u hmean
  rw [hmass,henergy,mul_one] at h
  exact h
end DFLPhysicalGap
