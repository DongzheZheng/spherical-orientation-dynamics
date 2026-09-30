import continuation.SeparatedMeasureFubini
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The real angular/latitude integral and integrability equivalence for
the actual separated Riemannian metric. The density is derived from the
metric, rather than supplied as a change-of-variables premise. -/
noncomputable section
open Bundle Manifold MeasureTheory Metric Module Set
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry DifferentialGeometry.Integral.Measure
namespace DFLSeparatedBochner

private theorem integral_cast_measure {X : Type*} {m₁ m₂ : MeasurableSpace X}
    (hm : m₁ = m₂) (mu : @Measure X m₁) (F : X → ℝ) :
    @MeasureTheory.integral X ℝ _ _ m₂
      (cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) mu) F =
      @MeasureTheory.integral X ℝ _ _ m₁ mu F := by
  cases hm
  rfl

private theorem integrable_cast_measure {X : Type*} {m₁ m₂ : MeasurableSpace X}
    (hm : m₁ = m₂) (mu : @Measure X m₁) (F : X → ℝ) :
    @MeasureTheory.Integrable ℝ _ _ X m₂
      F (cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) mu) ↔
      @MeasureTheory.Integrable ℝ _ _ X m₁ F mu := by
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

variable (h : SmoothRiemannianMetric I M)
  (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
  (f b : ℝ → ℝ) (hf : ∀ s, 0 < f s) (hb : ∀ s, 0 < b s)
  (hfC : Continuous f) (hbC : Continuous b)
  (hsep : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
    gP.inner (y,s) (v,a) (w,c) = (f s)^2*h.inner y v w+(b s)^2*a*c)

include hf hb hfC hbC hsep

/-- The true real integral is the angular-times-line product integral
with its derived density. -/
theorem separated_integral_product (F : M × ℝ → ℝ) :
    (∫ x, F x ∂riemannianVolumeMeasure (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) gP) =
      @MeasureTheory.integral (M × ℝ) ℝ _ _ (@Prod.instMeasurableSpace M ℝ _ _)
        ((riemannianVolumeMeasure I M h).prod (volume : Measure ℝ))
        (fun x => (f x.2)^finrank ℝ E*b x.2*F x) := by
  have hd : Continuous (fun x : M × ℝ => ENNReal.ofReal ((f x.2)^finrank ℝ E*b x.2)) :=
    ENNReal.continuous_ofReal.comp (((hfC.comp continuous_snd).pow _).mul
      (hbC.comp continuous_snd))
  rw [DFLWarpedVolume.separated_riemannianVolumeMeasure_product h gP f b hf hb hsep,
    integral_withDensity_eq_integral_toReal_smul hd.measurable
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (le_of_lt (mul_pos (pow_pos (hf _) _) (hb _))),
    smul_eq_mul]
  exact integral_cast_measure (@BorelSpace.measurable_eq (M × ℝ) _
    (@Prod.instMeasurableSpace M ℝ _ _) Prod.borelSpace) _ _

/-- Actual separated-volume integrability is equivalent to integrability
of the derived density times the function for the product measure. -/
theorem separated_integrable_product (F : M × ℝ → ℝ) :
    Integrable F (riemannianVolumeMeasure (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) gP) ↔
      @MeasureTheory.Integrable ℝ _ _ (M × ℝ) (@Prod.instMeasurableSpace M ℝ _ _)
        (fun x => (f x.2)^finrank ℝ E*b x.2*F x)
        ((riemannianVolumeMeasure I M h).prod (volume : Measure ℝ)) := by
  have hd : Continuous (fun x : M × ℝ => ENNReal.ofReal ((f x.2)^finrank ℝ E*b x.2)) :=
    ENNReal.continuous_ofReal.comp (((hfC.comp continuous_snd).pow _).mul
      (hbC.comp continuous_snd))
  rw [DFLWarpedVolume.separated_riemannianVolumeMeasure_product h gP f b hf hb hsep,
    integrable_withDensity_iff_integrable_smul' hd.measurable
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (le_of_lt (mul_pos (pow_pos (hf _) _) (hb _))),
    smul_eq_mul]
  exact integrable_cast_measure (@BorelSpace.measurable_eq (M × ℝ) _
    (@Prod.instMeasurableSpace M ℝ _ _) Prod.borelSpace) _ _

/-- Original angular/latitude Fubini formula for every genuinely
integrable real function, with the integrability condition retained. -/
theorem separated_integral (F : M × ℝ → ℝ)
    (hF : Integrable F (riemannianVolumeMeasure (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) gP)) :
    (∫ x, F x ∂riemannianVolumeMeasure (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) gP) =
      ∫ s : ℝ, ∫ y : M, (f s)^finrank ℝ E*b s*F (y,s)
        ∂riemannianVolumeMeasure I M h ∂volume := by
  rw [separated_integral_product h gP f b hf hb hfC hbC hsep F]
  let _ : SigmaFinite (riemannianVolumeMeasure I M h) :=
    riemannianVolumeMeasure_sigmaFinite h
  exact integral_prod_symm _
    ((separated_integrable_product h gP f b hf hb hfC hbC hsep F).1 hF)

end DFLSeparatedBochner
