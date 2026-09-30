import continuation.CotSphereMetric
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtype

/-! True volume change of variables for the original cot sphere map.
The metric is the actual round pullback. Its volume density follows from
the proved metric formula, and its pushforward is the actual round volume
restricted to the sphere with the two poles removed. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold Metric Module Set Filter MeasureTheory
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+2)]
variable [FiniteDimensional ℝ E]

private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p × ℝ) := borel (PolarDir p × ℝ)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p × ℝ) := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (cotSphereTarget (n := n) p) :=
  borel (cotSphereTarget (n := n) p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (cotSphereTarget (n := n) p) := ⟨rfl⟩

/-- The actual cot-coordinate density relative to the ordinary angular
round sphere times the Euclidean line. -/
theorem cotProductMetric_volumeDensity (p : sphere (0 : E) 1) (q : PolarDir p × ℝ) :
    riemannianVolumeDensity
      ((roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)).prod (euclideanMetric (E := ℝ)))
      (cotProductMetric (n := n) p) q = cotAngularScale q.2^n*cotLineScale q.2 := by
  simpa using DFLWarpedVolume.separated_riemannianVolumeDensity
    (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotProductMetric (n := n) p)
    cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
    (cotProductMetric_separated p) q

/-- Ordinary angular round volume times Lebesgue measure, expressed in
the actual product manifold's Borel measurable space. -/
def cotProductReferenceMeasure (p : sphere (0 : E) 1) : Measure (PolarDir p × ℝ) :=
  cast
    (congrArg (fun m : MeasurableSpace (PolarDir p × ℝ) => @Measure (PolarDir p × ℝ) m)
      (@BorelSpace.measurable_eq (PolarDir p × ℝ) _
        (@Prod.instMeasurableSpace (PolarDir p) ℝ _ _) Prod.borelSpace))
    ((riemannianVolumeMeasure (𝓡 n) (PolarDir p)
      (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))).prod (volume : Measure ℝ))

/-- Actual cot-coordinate volume, with its density derived from the true
round metric rather than supplied as a Jacobian hypothesis. -/
theorem cotProductMetric_volume_product (p : sphere (0 : E) 1) :
    riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ, ℝ)) (PolarDir p × ℝ)
      (cotProductMetric (n := n) p) =
      (cotProductReferenceMeasure (n := n) p).withDensity
        (fun q => ENNReal.ofReal (cotAngularScale q.2^n*cotLineScale q.2)) := by
  simpa only [cotProductReferenceMeasure,finrank_euclideanSpace,Fintype.card_fin] using
    DFLWarpedVolume.separated_riemannianVolumeMeasure_product
      (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotProductMetric (n := n) p)
      cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
      (cotProductMetric_separated p)

/-- The true global diffeomorphism transports the actual round volume of
the open target to the actual cot-product metric volume. -/
theorem cotProductMetric_volume_pullback (p : sphere (0 : E) 1) :
    letI : SigmaCompactSpace (cotSphereTarget (n := n) p) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen (𝓡 (n+1)) (cotSphereTarget (n := n) p).isOpen)
    riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ, ℝ)) (PolarDir p × ℝ)
      (cotProductMetric (n := n) p) =
      Measure.map ((cotSphereDiffeo (n := n) p).symm : cotSphereTarget (n := n) p → PolarDir p × ℝ)
        (riemannianVolumeMeasure (𝓡 (n+1)) (cotSphereTarget (n := n) p)
          ((roundMetric (E := E) (n := n+1)).restrictOpen (cotSphereTarget (n := n) p))) := by
  let : SigmaCompactSpace (cotSphereTarget (n := n) p) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen (𝓡 (n+1)) (cotSphereTarget (n := n) p).isOpen)
  exact riemannianVolumeMeasure_pullback_cross
    ((roundMetric (E := E) (n := n+1)).restrictOpen (cotSphereTarget (n := n) p))
    (cotSphereDiffeo (n := n) p)

/-- Pushing actual cot-product volume along the original sphere map gives
the actual round volume restricted to the sphere minus its two poles. -/
theorem cotProductMetric_volume_pushforward (p : sphere (0 : E) 1) :
    Measure.map (cotSpherePD (n := n) p : PolarDir p × ℝ → sphere (0 : E) 1)
      (riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ, ℝ)) (PolarDir p × ℝ)
        (cotProductMetric (n := n) p)) =
      (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))).restrict (polarTarget p) := by
  let : SigmaCompactSpace (cotSphereTarget (n := n) p) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen (𝓡 (n+1)) (cotSphereTarget (n := n) p).isOpen)
  have hDS := (cotSphereDiffeo (n := n) p).symm.continuous.measurable
  rw [cotProductMetric_volume_pullback,Measure.map_map
    (cotSpherePD_smooth (n := n) p).continuous.measurable hDS]
  have hc : (cotSpherePD (n := n) p : PolarDir p × ℝ → sphere (0 : E) 1) ∘
      ((cotSphereDiffeo (n := n) p).symm : cotSphereTarget (n := n) p → PolarDir p × ℝ) =
      Subtype.val := by
    funext x
    have he := congrArg (Subtype.val : cotSphereTarget (n := n) p → sphere (0 : E) 1)
      ((cotSphereDiffeo (n := n) p).apply_symm_apply x)
    exact he
  rw [hc]
  exact map_riemannianVolumeMeasure_restrictOpen
    (roundMetric (E := E) (n := n+1)) (cotSphereTarget (n := n) p)

/-- Complete original change of variables: the computed angular-times-line
density pushes forward to true round volume away from the two poles. -/
theorem cot_sphere_volume_change_of_variables (p : sphere (0 : E) 1) :
    Measure.map (cotSpherePD (n := n) p : PolarDir p × ℝ → sphere (0 : E) 1)
      ((cotProductReferenceMeasure (n := n) p).withDensity
        (fun q => ENNReal.ofReal (cotAngularScale q.2^n*cotLineScale q.2))) =
      (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))).restrict (polarTarget p) := by
  rw [← cotProductMetric_volume_product]
  exact cotProductMetric_volume_pushforward p

end DFLCotSphere
