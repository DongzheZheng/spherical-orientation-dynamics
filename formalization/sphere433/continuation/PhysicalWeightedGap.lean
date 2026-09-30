import continuation.PhysicalWeightedFirst
import continuation.CircleParity

/-! The manuscript's weighted physical-sphere Rayleigh gap. Its C² core
minimum is attained by an actual smooth eigenstate obtained from the
complete H¹ minimum, rather than a prescribed separated branch. -/
noncomputable section
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Analysis.Laplacian
open DFLPhysicalHalfDensity DFLTransverseSphere DFLSphere
namespace DFLPhysicalGap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

def weightedMass (p : E) (r : ℝ) (f : sphere (0 : E) 1 → ℝ) : ℝ :=
  ∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*(f x)^2
    ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))

def weightedMean (p : E) (r : ℝ) (f : sphere (0 : E) 1 → ℝ) : ℝ :=
  ∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*f x
    ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))

def weightedEnergy (p : E) (r : ℝ) (f : sphere (0 : E) 1 → ℝ) : ℝ :=
  ∫ x, Real.exp (r*⟪p,(x : E)⟫_ℝ)*normGradSqFun (roundMetric (E := E) (n := n)) f x
    ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))

def weightedRayleighValues (p : E) (r : ℝ) : Set ℝ :=
  {a | ∃ f : sphere (0 : E) 1 → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 f ∧
    weightedMass (n := n) p r f=1 ∧ weightedMean (n := n) p r f=0 ∧
    weightedEnergy (n := n) p r f=a}

def weightedGap (p : E) (r : ℝ) : ℝ := sInf (weightedRayleighValues (n := n) p r)

variable [NeZero n]

/-- The original weighted C² Rayleigh core has a genuine positive minimum
and a normalized smooth eigenfunction. Every C² zero-mean observable
satisfies its bound, including observables with nonzero pole values. -/
theorem actual_weighted_gap_spec (p : E) (hp : ‖p‖=1) (r : ℝ) :
    0<weightedGap (n := n) p r ∧
    ∃ f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯,
      weightedMass (n := n) p r f=1 ∧ weightedMean (n := n) p r f=0 ∧
      weightedEnergy (n := n) p r f=weightedGap (n := n) p r ∧
      (∀ x,weightedRoundApply (n := n) p r f x=weightedGap (n := n) p r*f x) ∧
      (∃ x,f x≠0) ∧
      ∀ v : sphere (0 : E) 1 → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 v →
        weightedMean (n := n) p r v=0 →
        weightedGap (n := n) p r*weightedMass (n := n) p r v ≤ weightedEnergy (n := n) p r v := by
  obtain ⟨lam,f,hl,hM,hmean,hE,hpoint,hne,hmin⟩ := actual_weighted_first_positive_exists (n := n) p hp r
  have hmem : lam ∈ weightedRayleighValues (n := n) p r :=
    ⟨f,f.contMDiff.of_le (by decide),hM,hmean,hE⟩
  have hleast : ∀ a ∈ weightedRayleighValues (n := n) p r,lam≤a := by
    intro a ha
    obtain ⟨v,hv,hvM,hvm,hva⟩ := ha
    have hh := hmin v hv hvm
    change lam*weightedMass (n := n) p r v ≤ weightedEnergy (n := n) p r v at hh
    simpa only [hvM,hva,mul_one] using hh
  have hgap : weightedGap (n := n) p r=lam :=
    le_antisymm (csInf_le ⟨lam,hleast⟩ hmem) (le_csInf ⟨lam,hmem⟩ hleast)
  rw [hgap]
  exact ⟨hl,f,hM,hmean,hE,hpoint,hne,hmin⟩

/-- Any actual smooth attained normalized minimum identifies the same
physical gap; the construction of the minimizer does not affect the value. -/
theorem weighted_minimizer_identifies_gap (p : E) (hp : ‖p‖=1) (r lam : ℝ)
    (f : sphere (0 : E) 1 → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 f)
    (hM : weightedMass (n := n) p r f=1) (hm : weightedMean (n := n) p r f=0)
    (hE : weightedEnergy (n := n) p r f=lam)
    (hmin : ∀ v : sphere (0 : E) 1 → ℝ,ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) 2 v →
      weightedMean (n := n) p r v=0 →
      lam*weightedMass (n := n) p r v ≤ weightedEnergy (n := n) p r v) :
    weightedGap (n := n) p r=lam := by
  obtain ⟨_,u,huM,hum,huE,_,_,huMin⟩ := actual_weighted_gap_spec (n := n) p hp r
  have h1 := huMin f hf hm
  have h2 := hmin u (u.contMDiff.of_le (by decide)) hum
  rw [hM,hE,mul_one] at h1
  rw [huM,huE,mul_one] at h2
  exact le_antisymm h1 h2

/-- The genuine circle Rayleigh gap is at least the original transverse
minimum. This is the actual circle parity proof, valid for every real field. -/
theorem actual_circle_gap_ge_transverse (r : ℝ) :
    roundTiltMinimum 1 1 r (1/2) ≤
      weightedGap (n := 1) DFLCircleOdd.circleAxis r := by
  obtain ⟨hl,u,_,_,_,heig,hne,_⟩ :=
    actual_weighted_gap_spec (n := 1) DFLCircleOdd.circleAxis (by simp [DFLCircleOdd.circleAxis]) r
  exact DFLCircleOdd.actual_circle_positive_eigenvalue_ge_transverse_ground r _ hl u heig hne

end DFLPhysicalGap
