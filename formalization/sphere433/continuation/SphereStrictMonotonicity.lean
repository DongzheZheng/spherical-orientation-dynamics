import continuation.SphereGroundMoments
import continuation.TiltEvenness
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Reflection and strict field monotonicity of the actual full-domain
minimum. The rate theorem comes from the same normalized positive ground
in the variational HF formula and the original weighted flux identity. -/

noncomputable section
open Set
open scoped RealInnerProductSpace InnerProductSpace

namespace DFLSphere

/-- Antipodal reflection also makes the actual minimum even in the field. -/
theorem roundTiltMinimum_even_r (k : ℕ) (lam0 r a : ℝ) :
    roundTiltMinimum k lam0 (-r) a = roundTiltMinimum k lam0 r a := by
  have hV : roundTiltPotential k lam0 (-r) a = roundTiltPotential k lam0 r (-a) := by
    funext x
    unfold roundTiltPotential
    ring
  change roundPotentialMinimum k (roundTiltPotential k lam0 (-r) a) = _
  rw [hV]
  exact roundTiltMinimum_even k lam0 r a

/-- Reflection exchanges the two original drift parameters `b` and `M-b`. -/
theorem roundTiltMinimum_drift_reflection (k : ℕ) (lam0 r b : ℝ) :
    roundTiltMinimum k lam0 r (((k+2 : ℕ) : ℝ)/2-b) =
      roundTiltMinimum k lam0 r (((k+2 : ℕ) : ℝ)/2-(((k+2 : ℕ) : ℝ)-b)) := by
  have ha : ((k+2 : ℕ) : ℝ)/2-(((k+2 : ℕ) : ℝ)-b) =
      -(((k+2 : ℕ) : ℝ)/2-b) := by ring
  rw [ha, roundTiltMinimum_even]

/-- The genuine spectral rate is positive throughout `0<b<M`, with no
assumed eigenbranch, differentiability, or moment sign. -/
theorem roundTiltMinimum_deriv_r_pos_full (k : ℕ) (lam0 b r : ℝ)
    (hb : 0 < b) (hbM : b < ((k+2 : ℕ) : ℝ)) (hr : 0 < r) :
    0 < deriv (fun s => roundTiltMinimum k lam0 s (((k+2 : ℕ) : ℝ)/2-b)) r := by
  by_cases hhalf : 2*b ≤ ((k+2 : ℕ) : ℝ)
  · exact roundTiltMinimum_deriv_r_pos k lam0 b r hb hhalf hr
  · have hfunc : (fun s => roundTiltMinimum k lam0 s (((k+2 : ℕ) : ℝ)/2-b)) =
        (fun s => roundTiltMinimum k lam0 s (((k+2 : ℕ) : ℝ)/2-(((k+2 : ℕ) : ℝ)-b))) := by
      funext s
      exact roundTiltMinimum_drift_reflection k lam0 s b
    rw [hfunc]
    exact roundTiltMinimum_deriv_r_pos k lam0 (((k+2 : ℕ) : ℝ)-b) r
      (by linarith) (by linarith) hr

/-- The actual even, differentiable spectral minimum has zero rate at zero. -/
theorem roundTiltMinimum_deriv_r_zero (k : ℕ) (lam0 a : ℝ) :
    deriv (fun s => roundTiltMinimum k lam0 s a) 0 = 0 := by
  let f : ℝ → ℝ := fun s => roundTiltMinimum k lam0 s a
  have h0 : HasDerivAt f (deriv f 0) 0 :=
    (roundTiltMinimum_differentiable_r k lam0 a 0).hasDerivAt
  have h0' : HasDerivAt f (deriv f 0) (-(0 : ℝ)) := by simpa using h0
  have hnid : HasDerivAt (fun x : ℝ => -x) (-1) 0 := hasDerivAt_neg' 0
  have hc := h0'.comp 0 hnid
  have hf : (fun x => f (-x)) = f := by
    funext x
    exact roundTiltMinimum_even_r k lam0 x a
  have hneg : HasDerivAt f (-(deriv f 0)) 0 := by
    simpa only [Function.comp_def, neg_zero, mul_neg_one, hf] using hc
  have he := h0.unique hneg
  change deriv f 0 = 0
  linarith

/-- Strict field monotonicity includes the zero-field endpoint. -/
theorem roundTiltMinimum_strictMonoOn_nonnegative_r (k : ℕ) (lam0 b : ℝ)
    (hb : 0 < b) (hbM : b < ((k+2 : ℕ) : ℝ)) :
    StrictMonoOn (fun r => roundTiltMinimum k lam0 r (((k+2 : ℕ) : ℝ)/2-b)) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact (roundTiltMinimum_differentiable_r k lam0 (((k+2 : ℕ) : ℝ)/2-b)).continuous.continuousOn
  · intro r hr
    rw [interior_Ici] at hr
    exact roundTiltMinimum_deriv_r_pos_full k lam0 b r hb hbM hr

/-- The manuscript's physical transverse parameters satisfy the strict
field monotonicity theorem in every sphere dimension. -/
theorem roundTiltMinimum_physical_strictMonoOn (k : ℕ) (lam0 : ℝ) :
    StrictMonoOn (fun r => roundTiltMinimum k lam0 r ((k : ℝ)/2)) (Ici 0) := by
  have he : ((k+2 : ℕ) : ℝ)/2-1 = (k : ℝ)/2 := by push_cast; ring
  simpa only [he] using roundTiltMinimum_strictMonoOn_nonnegative_r k lam0 1
    (by norm_num) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])

end DFLSphere
