import continuation.GenericRoundPoincare
import continuation.CotSphereBochnerEnergy

/-! Actual angular slice coercivity in the manuscript's cot coordinates.
Each slice is the restriction of a true smooth full-sphere state along the
proved cot sphere parametrization. The angular metric and measure are genuine
round-sphere objects, and the sharp n coefficient is proved for every n≥1. -/
noncomputable section
open Bundle Manifold MeasureTheory Set Filter Metric Module
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 2)]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩

abbrev cotAngularVolume (p : sphere (0 : E) 1) :=
  riemannianVolumeMeasure (𝓡 n) (PolarDir p)
    (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))

/-- The actual smooth angular sphere state at every fixed cot height. -/
def cotAngularSlice (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (s : ℝ) :
    C^∞⟮𝓡 n, PolarDir p; ℝ⟯ :=
  ⟨fun y => u (cotSpherePD (n := n) p (y,s)),
    (u.contMDiff.comp (cotSpherePD_smooth (n := n) p)).comp
      (contMDiff_id.prodMk contMDiff_const)⟩

/-- True angular sharp Poincare inequality on each physical slice,
including the circle fiber n=1. No angular spectral inequality is assumed. -/
theorem cot_angular_slice_poincare (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (s : ℝ)
    (hmean : (∫ y : PolarDir p, u (cotSpherePD (n := n) p (y,s))
      ∂cotAngularVolume (n := n) p) = 0) :
    (n : ℝ) * (∫ y : PolarDir p, (u (cotSpherePD (n := n) p (y,s)))^2
      ∂cotAngularVolume (n := n) p) ≤
      ∫ y : PolarDir p,
        normGradSqFun (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
          (fun z : PolarDir p => u (cotSpherePD (n := n) p (z,s))) y
        ∂cotAngularVolume (n := n) p :=
  DFLGenericRound.round_sphere_smooth_poincare (E := (ℝ ∙ (p : E))ᗮ)
    (n := n) hn (cotAngularSlice p u s) hmean

/-- The manuscript's true angular energy coefficient at fixed cot height. -/
theorem cot_angular_slice_scaled_poincare (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (s : ℝ)
    (hmean : (∫ y : PolarDir p, u (cotSpherePD (n := n) p (y,s))
      ∂cotAngularVolume (n := n) p) = 0) :
    ((cotAngularScale s^2)⁻¹ * (n : ℝ)) *
      (∫ y : PolarDir p, (u (cotSpherePD (n := n) p (y,s)))^2
        ∂cotAngularVolume (n := n) p) ≤
      ∫ y : PolarDir p, (cotAngularScale s^2)⁻¹ *
        normGradSqFun (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
          (fun z : PolarDir p => u (cotSpherePD (n := n) p (z,s))) y
        ∂cotAngularVolume (n := n) p := by
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (cot_angular_slice_poincare hn p u s hmean)
    (inv_nonneg.mpr (sq_nonneg (cotAngularScale s)))
  simpa only [mul_assoc] using h

/-- The same actual slice inequality with the original axial physical weight. -/
theorem cot_angular_slice_weighted_poincare (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ)
    (hmean : (∫ y : PolarDir p, u (cotSpherePD (n := n) p (y,s))
      ∂cotAngularVolume (n := n) p) = 0) :
    (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
      ((cotAngularScale s^2)⁻¹ * (n : ℝ))*
        (∫ y : PolarDir p, (u (cotSpherePD (n := n) p (y,s)))^2
          ∂cotAngularVolume (n := n) p) ≤
      ∫ y : PolarDir p,
        (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
          (cotAngularScale s^2)⁻¹ *
            normGradSqFun (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
              (fun z : PolarDir p => u (cotSpherePD (n := n) p (z,s))) y
        ∂cotAngularVolume (n := n) p := by
  rw [integral_const_mul]
  have hweight : 0 ≤ cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)) :=
    (mul_pos (mul_pos (pow_pos (cotAngularScale_pos s) n) (cotLineScale_pos s))
      (Real.exp_pos _)).le
  have h := mul_le_mul_of_nonneg_left (cot_angular_slice_poincare hn p u s hmean)
    (mul_nonneg hweight (inv_nonneg.mpr (sq_nonneg (cotAngularScale s))))
  simpa only [mul_assoc] using h

end DFLCotSphere
