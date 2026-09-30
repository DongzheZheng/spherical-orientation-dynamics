import DifferentialGeometry.Geometry.Measure.Product
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity

/-! The original separated volume element: an angular metric multiplied
by f(s)² and a line metric multiplied by b(s)² have density f(s)^n b(s).
The statement uses the actual Riemannian volume and derives its density
from the actual chart Gram determinant. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold MeasureTheory Metric Module Set
open scoped Manifold ContDiff ENNReal Matrix
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DFLWarpedVolume
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace (M × ℝ) := borel (M × ℝ)
private local instance : BorelSpace (M × ℝ) := ⟨rfl⟩

private theorem sqrt_square_power (c : ℝ) (hc : 0 < c) (n : ℕ) :
    Real.sqrt ((c^2)^n) = c^n := by
  rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, Real.sqrt_sq_eq_abs,
    abs_of_pos (pow_pos hc n)]

omit [SigmaCompactSpace M] in
/-- Actual chart density of the separated angular/line metric. -/
theorem separated_chartDensity
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (f b : ℝ → ℝ) (hf : ∀ s, 0 < f s) (hb : ∀ s, 0 < b s)
    (hsep : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y,s) (v,a) (w,c) = (f s)^2*h.inner y v w+(b s)^2*a*c)
    (p z : M × ℝ)
    (hz : z ∈ (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) p).baseSet) :
    chartDensity gP p z = (f z.2)^finrank ℝ E*b z.2*
      chartDensity (h.prod (euclideanMetric (E := ℝ))) p z := by
  let q := h.prod (euclideanMetric (E := ℝ))
  let hs := scaleMetric ((f z.2/b z.2)^2) (sq_pos_of_pos (div_pos (hf z.2) (hb z.2))) h
  let qs := hs.prod (euclideanMetric (E := ℝ))
  let gs := scaleMetric ((b z.2)^2) (sq_pos_of_pos (hb z.2)) qs
  have hinner : ∀ v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) z,
      gP.inner z v w = gs.inner z v w := by
    intro v w
    have hzsep := hsep z.1 z.2 v.1 w.1 v.2 w.2
    change gP.inner z v w = _ at hzsep
    rw [hzsep]
    have hg := scaleMetric_inner ((b z.2)^2) (sq_pos_of_pos (hb z.2)) qs z v w
    change gs.inner z v w = _ at hg
    rw [hg]
    have hp := SmoothRiemannianMetric.prod_inner (I := I) (J := 𝓘(ℝ, ℝ))
      (g := hs) (h := euclideanMetric (E := ℝ)) (x := z) v w
    change qs.inner z v w = hs.inner z.1 v.1 w.1+inner ℝ v.2 w.2 at hp
    rw [hp]
    have hh := scaleMetric_inner ((f z.2/b z.2)^2)
      (sq_pos_of_pos (div_pos (hf z.2) (hb z.2))) h z.1 v.1 w.1
    change hs.inner z.1 v.1 w.1 = _ at hh
    rw [hh,Real.inner_apply]
    field_simp [ne_of_gt (hb z.2)]
  have hgram : Tensor.Coordinates.chartGramMatrix gP p z =
      Tensor.Coordinates.chartGramMatrix gs p z := by
    ext i j
    simp only [Tensor.Coordinates.chartGramMatrix_apply]
    exact hinner _ _
  have hcd : chartDensity gP p z = chartDensity gs p z := by
    unfold chartDensity
    rw [hgram]
  have hq : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      q.inner (y,s) (v,a) (w,c) = h.inner y v w+a*c := by
    intro y s v w a c
    have hp := SmoothRiemannianMetric.prod_inner (I := I) (J := 𝓘(ℝ, ℝ))
      (g := h) (h := euclideanMetric (E := ℝ)) (x := (y,s)) (v,a) (w,c)
    change q.inner (y,s) (v,a) (w,c) = h.inner y v w+inner ℝ a c at hp
    simpa only [Real.inner_apply,mul_comm] using hp
  have hqs : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      qs.inner (y,s) (v,a) (w,c) = hs.inner y v w+a*c := by
    intro y s v w a c
    have hp := SmoothRiemannianMetric.prod_inner (I := I) (J := 𝓘(ℝ, ℝ))
      (g := hs) (h := euclideanMetric (E := ℝ)) (x := (y,s)) (v,a) (w,c)
    change qs.inner (y,s) (v,a) (w,c) = hs.inner y v w+inner ℝ a c at hp
    simpa only [Real.inner_apply,mul_comm] using hp
  rw [hcd,chartDensity_scale,chartDensity_prod_eq hs qs hqs p z hz,
    chartDensity_scale,chartDensity_prod_eq h q hq p z hz]
  simp only [finrank_prod,finrank_self,sqrt_square_power _ (hb z.2),
    sqrt_square_power _ (div_pos (hf z.2) (hb z.2))]
  have hp : (b z.2)^(finrank ℝ E+1)*(f z.2/b z.2)^finrank ℝ E =
      (f z.2)^finrank ℝ E*b z.2 := by
    calc
      _ = ((b z.2)^finrank ℝ E*((f z.2)^finrank ℝ E/(b z.2)^finrank ℝ E))*b z.2 := by
        rw [pow_succ,div_pow]
        ring
      _ = _ := by rw [mul_div_cancel₀ _ (pow_ne_zero _ (ne_of_gt (hb z.2))) ]
  linear_combination (|((Tensor.Coordinates.chartModelBasis E).prod
    (Tensor.Coordinates.chartModelBasis ℝ)).det
      ((Tensor.Coordinates.chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E)))| *
    chartDensity h p.1 z.1*chartDensity (euclideanMetric (E := ℝ)) p.2 z.2)*hp

/-- The separated volume density relative to the ordinary product metric
is derived pointwise, without a supplied Jacobian formula. -/
theorem separated_riemannianVolumeDensity
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (f b : ℝ → ℝ) (hf : ∀ s, 0 < f s) (hb : ∀ s, 0 < b s)
    (hsep : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y,s) (v,a) (w,c) = (f s)^2*h.inner y v w+(b s)^2*a*c)
    (x : M × ℝ) :
    riemannianVolumeDensity (h.prod (euclideanMetric (E := ℝ))) gP x =
      (f x.2)^finrank ℝ E*b x.2 := by
  rw [riemannianVolumeDensity_apply_of_mem_chart_source _ _ x
    (mem_chart_source _ x),separated_chartDensity h gP f b hf hb hsep x x
      (mem_chart_source _ x)]
  exact mul_div_cancel_right₀ _ (ne_of_gt (chartDensity_pos _ x (mem_chart_source _ x)))

/-- True separated Riemannian measure equals the product measure with the
computed density. The only input is the actual pointwise metric formula. -/
theorem separated_riemannianVolumeMeasure
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (f b : ℝ → ℝ) (hf : ∀ s, 0 < f s) (hb : ∀ s, 0 < b s)
    (hsep : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y,s) (v,a) (w,c) = (f s)^2*h.inner y v w+(b s)^2*a*c) :
    riemannianVolumeMeasure (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) gP =
      (riemannianVolumeMeasure (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)
        (h.prod (euclideanMetric (E := ℝ)))).withDensity
          (fun x => ENNReal.ofReal ((f x.2)^finrank ℝ E*b x.2)) := by
  rw [riemannianVolumeMeasure_eq_withDensity (h.prod (euclideanMetric (E := ℝ))) gP]
  congr 1
  funext x
  rw [separated_riemannianVolumeDensity h gP f b hf hb hsep x]

/-- The computed volume is the angular-times-line product measure with
its original separated density. -/
theorem separated_riemannianVolumeMeasure_product
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (f b : ℝ → ℝ) (hf : ∀ s, 0 < f s) (hb : ∀ s, 0 < b s)
    (hsep : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y,s) (v,a) (w,c) = (f s)^2*h.inner y v w+(b s)^2*a*c) :
    riemannianVolumeMeasure (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) gP =
      (cast
        (congrArg (fun m : MeasurableSpace (M × ℝ) => @Measure (M × ℝ) m)
          (@BorelSpace.measurable_eq (M × ℝ) _
            (@Prod.instMeasurableSpace M ℝ _ _) Prod.borelSpace))
        ((riemannianVolumeMeasure I M h).prod (volume : Measure ℝ))).withDensity
          (fun x => ENNReal.ofReal ((f x.2)^finrank ℝ E*b x.2)) := by
  rw [separated_riemannianVolumeMeasure h gP f b hf hb hsep]
  congr 1
  apply riemannianVolumeMeasure_product_real_of_inner_eq h
  intro y s v w a c
  have hp := SmoothRiemannianMetric.prod_inner (I := I) (J := 𝓘(ℝ, ℝ))
    (g := h) (h := euclideanMetric (E := ℝ)) (x := (y,s)) (v,a) (w,c)
  change (h.prod (euclideanMetric (E := ℝ))).inner (y,s) (v,a) (w,c) =
    h.inner y v w+inner ℝ a c at hp
  simpa only [Real.inner_apply,mul_comm] using hp

end DFLWarpedVolume
