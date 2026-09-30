import continuation.WarpedProductVolume
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual angular/latitude Tonelli disintegration of the separated
Riemannian volume, from the proved Gram determinant and product measure. -/
noncomputable section
open Bundle Manifold MeasureTheory Metric Module Set
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry DifferentialGeometry.Integral.Measure
namespace DFLSeparatedFubini

private theorem lintegral_cast_measure {X : Type*} {m₁ m₂ : MeasurableSpace X}
    (hm : m₁ = m₂) (mu : @Measure X m₁) (F : X → ℝ≥0∞) :
    @lintegral X m₂
      (cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) mu) F =
      @lintegral X m₁ mu F := by
  cases hm
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace (M × ℝ) := borel (M × ℝ)
private local instance : BorelSpace (M × ℝ) := ⟨rfl⟩

/-- Genuine iterated integral in the angular variable and latitude
parameter. No disintegration or volume formula is supplied as a premise. -/
theorem separated_lintegral
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (f b : ℝ → ℝ) (hf : ∀ s, 0 < f s) (hb : ∀ s, 0 < b s)
    (hfC : Continuous f) (hbC : Continuous b)
    (hsep : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y,s) (v,a) (w,c) = (f s)^2*h.inner y v w+(b s)^2*a*c)
    (F : M × ℝ → ℝ≥0∞) (hF : Continuous F) :
    (∫⁻ x, F x ∂riemannianVolumeMeasure (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) gP) =
      ∫⁻ s : ℝ, ∫⁻ y : M, ENNReal.ofReal ((f s)^finrank ℝ E*b s)*F (y,s)
        ∂riemannianVolumeMeasure I M h ∂volume := by
  have hd : Continuous (fun x : M × ℝ => ENNReal.ofReal ((f x.2)^finrank ℝ E*b x.2)) :=
    ENNReal.continuous_ofReal.comp (((hfC.comp continuous_snd).pow _).mul
      (hbC.comp continuous_snd))
  rw [DFLWarpedVolume.separated_riemannianVolumeMeasure_product h gP f b hf hb hsep,
    lintegral_withDensity_eq_lintegral_mul _ hd.measurable hF.measurable]
  rw [lintegral_cast_measure (@BorelSpace.measurable_eq (M × ℝ) _
    (@Prod.instMeasurableSpace M ℝ _ _) Prod.borelSpace)]
  let _ : SigmaFinite (riemannianVolumeMeasure I M h) :=
    riemannianVolumeMeasure_sigmaFinite h
  have hg : @Measurable (M × ℝ) ℝ≥0∞ (@Prod.instMeasurableSpace M ℝ _ _)
      ENNReal.measurableSpace ((fun x => ENNReal.ofReal ((f x.2)^finrank ℝ E*b x.2))*F) := by
    rw [@BorelSpace.measurable_eq (M × ℝ) _ (@Prod.instMeasurableSpace M ℝ _ _) Prod.borelSpace]
    exact hd.measurable.mul hF.measurable
  exact lintegral_prod_symm' _ hg

end DFLSeparatedFubini
