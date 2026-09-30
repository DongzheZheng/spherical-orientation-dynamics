import continuation.RoundCirclePoincare
import DFLSphere433.RoundSphereCoordinates

/-! Exact full H1 spectral gap one on the actual round S¹, with an
actual ambient linear coordinate attaining the mean-zero Rayleigh infimum. -/
noncomputable section
open Bundle Manifold MeasureTheory Set Filter Metric Module
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DFLSpectralCoordinates

namespace DFLRoundCircle
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 1 + 1)]
private instance : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin 1))) := ⟨by simp⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

def firstCoordinateVector : E := complexPlaneIsometry (1 : ℂ)

private theorem firstCoordinateVector_norm : ‖firstCoordinateVector (E := E)‖ = 1 := by
  rw [firstCoordinateVector, (complexPlaneIsometry (E := E)).norm_map]
  norm_num

def circleCoordinate : SmoothScalar (roundMetric (E := E) (n := 1)) :=
  ⟨innerCoordFun (E := E) (n := 1) firstCoordinateVector,
    (innerCoordFun (E := E) (n := 1) firstCoordinateVector).contMDiff⟩

theorem circleCoordinate_eigen (x : sphere (0 : E) 1) :
    ΔG (roundMetric (E := E) (n := 1)) circleCoordinate.toContMDiffMap x =
      -circleCoordinate.toFun x := by
  have hm : circleCoordinate.toContMDiffMap = innerCoordFun (E := E) (n := 1)
      firstCoordinateVector := by ext x; rfl
  rw [hm]
  change ΔG (roundMetric (E := E) (n := 1))
    (innerCoordFun (E := E) (n := 1) firstCoordinateVector) x =
      -⟪firstCoordinateVector (E := E), (x : E)⟫_ℝ
  simpa only [Nat.cast_one, neg_one_mul] using
    coordinate_laplacian (E := E) (n := 1) x firstCoordinateVector

theorem circleCoordinate_mean_zero :
    (∫ x : sphere (0 : E) 1, circleCoordinate.toFun x ∂circleVolume) = 0 := by
  have hz := integral_divergence_eq_zero_of_compact (roundMetric (E := E) (n := 1))
    (gradG (roundMetric (E := E) (n := 1)) circleCoordinate.toContMDiffMap)
  change (∫ x : sphere (0 : E) 1,
    ΔG (roundMetric (E := E) (n := 1)) circleCoordinate.toContMDiffMap x ∂circleVolume) = 0 at hz
  simp_rw [circleCoordinate_eigen] at hz
  rw [integral_neg, neg_eq_zero] at hz
  exact hz

private theorem circleCoordinate_nonzero : circleCoordinate (E := E) ≠ 0 := by
  let p : sphere (0 : E) 1 := ⟨firstCoordinateVector, by
    rw [mem_sphere_zero_iff_norm, firstCoordinateVector_norm]⟩
  intro h
  have he := congrArg (fun f : SmoothScalar (roundMetric (E := E) (n := 1)) => f.toFun p) h
  change ⟪firstCoordinateVector (E := E), firstCoordinateVector (E := E)⟫_ℝ = 0 at he
  rw [real_inner_self_eq_norm_sq, firstCoordinateVector_norm] at he
  norm_num at he

theorem circleCoordinate_L2_norm_pos :
    0 < ‖smoothToLp (roundMetric (E := E) (n := 1)) circleCoordinate‖ := by
  apply norm_pos_iff.mpr
  intro h
  apply circleCoordinate_nonzero (E := E)
  exact smoothToLp_injective (roundMetric (E := E) (n := 1))
    (h.trans ((smoothToLp (roundMetric (E := E) (n := 1))).map_zero).symm)

theorem circleCoordinate_energy_exact :
    ‖smoothToH1Compl (roundMetric (E := E) (n := 1)) circleCoordinate‖ ^ 2 -
      ‖H1ComplToLp (roundMetric (E := E) (n := 1))
        (smoothToH1Compl (roundMetric (E := E) (n := 1)) circleCoordinate)‖ ^ 2 =
      ‖smoothToLp (roundMetric (E := E) (n := 1)) circleCoordinate‖ ^ 2 := by
  let g := roundMetric (E := E) (n := 1)
  let f : SmoothScalar g := circleCoordinate
  have hg : (∫ x : sphere (0 : E) 1, g.inner x
      (gradFun g f.toFun x) (gradFun g f.toFun x) ∂circleVolume) =
      -∫ x, f.toFun x * ΔG g f.toContMDiffMap x ∂circleVolume :=
    green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
      g f.smooth f.smooth (HasCompactSupport.of_compactSpace _)
  have hn : ‖smoothToLp g f‖ ^ 2 = ∫ x, f.toFun x * f.toFun x ∂circleVolume :=
    f.norm_smoothToLp_sq
  rw [DFLSphere.h1_smooth_energy, hg, hn]
  have he : (fun x : sphere (0 : E) 1 => f.toFun x * ΔG g f.toContMDiffMap x) =
      fun x => -(f.toFun x * f.toFun x) := by
    funext x
    rw [circleCoordinate_eigen]
    ring
  rw [he, integral_neg, neg_neg]

def circleH1Rayleigh (U : H1Compl (roundMetric (E := E) (n := 1))) : ℝ :=
  (‖U‖ ^ 2 - ‖H1ComplToLp (roundMetric (E := E) (n := 1)) U‖ ^ 2) /
    ‖H1ComplToLp (roundMetric (E := E) (n := 1)) U‖ ^ 2

def circleH1RayleighValues : Set ℝ :=
  {q | ∃ U : H1Compl (roundMetric (E := E) (n := 1)),
    (∫ x : sphere (0 : E) 1,
      (H1ComplToLp (roundMetric (E := E) (n := 1)) U) x ∂circleVolume) = 0 ∧
    0 < ‖H1ComplToLp (roundMetric (E := E) (n := 1)) U‖ ∧ q = circleH1Rayleigh U}

def circleH1Gap : ℝ := sInf (circleH1RayleighValues (E := E))

theorem circleH1Rayleigh_lower (U : H1Compl (roundMetric (E := E) (n := 1)))
    (hmean : (∫ x : sphere (0 : E) 1,
      (H1ComplToLp (roundMetric (E := E) (n := 1)) U) x ∂circleVolume) = 0)
    (hU : 0 < ‖H1ComplToLp (roundMetric (E := E) (n := 1)) U‖) :
    1 ≤ circleH1Rayleigh U := by
  apply (le_div_iff₀ (sq_pos_of_pos hU)).mpr
  simpa only [one_mul] using round_circle_h1_poincare U hmean

theorem circleCoordinate_Rayleigh :
    circleH1Rayleigh (smoothToH1Compl (roundMetric (E := E) (n := 1)) circleCoordinate) = 1 := by
  unfold circleH1Rayleigh
  rw [circleCoordinate_energy_exact, H1ComplToLp_smoothToH1Compl]
  exact div_self (pow_ne_zero 2 (ne_of_gt (circleCoordinate_L2_norm_pos (E := E))))

theorem one_mem_circleH1RayleighValues : 1 ∈ circleH1RayleighValues (E := E) := by
  refine ⟨smoothToH1Compl (roundMetric (E := E) (n := 1)) circleCoordinate, ?_, ?_, ?_⟩
  · rw [H1ComplToLp_smoothToH1Compl]
    exact (integral_congr_ae (MemLp.coeFn_toLp circleCoordinate.memLp_two)).trans
      circleCoordinate_mean_zero
  · rw [H1ComplToLp_smoothToH1Compl]
    exact circleCoordinate_L2_norm_pos
  · exact circleCoordinate_Rayleigh.symm

/-- Exact global spectral gap of the original full round S¹ H1 form. -/
theorem circleH1Gap_eq_one : circleH1Gap (E := E) = 1 := by
  have hlower : 1 ∈ lowerBounds (circleH1RayleighValues (E := E)) := by
    rintro q ⟨U, hmean, hU, rfl⟩
    exact circleH1Rayleigh_lower U hmean hU
  have hne : (circleH1RayleighValues (E := E)).Nonempty :=
    ⟨1, one_mem_circleH1RayleighValues⟩
  unfold circleH1Gap
  exact le_antisymm (csInf_le ⟨1, hlower⟩ one_mem_circleH1RayleighValues)
    (le_csInf hne hlower)

end DFLRoundCircle
