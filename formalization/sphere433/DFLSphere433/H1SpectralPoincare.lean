import DifferentialGeometry.Analysis.Spectral.Scalar.EigenBasis
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
The source's compact-manifold H¹ form obeys a genuine global Poincaré
estimate when its actual spectral eigenvalues obey a positive lower
bound. The application to the true round sphere supplies that bound
from proved Ricci curvature and Lichnerowicz, separately.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DFLSphere

open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

abbrev ScalarIndex (g : SmoothRiemannianMetric I M) :=
  Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
    Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val))

def h1SpectralVector (g : SmoothRiemannianMetric I M) (i : ScalarIndex g) : H1Compl g :=
  (Real.sqrt i.1.val)⁻¹ • resolvent (I := I) (M := M) g
    (resolventEigenbasisSigma (I := I) (M := M) g i)

theorem h1SpectralVector_inner (g : SmoothRiemannianMetric I M)
    (i : ScalarIndex g) (u : H1Compl g) :
    ⟪h1SpectralVector g i, u⟫_ℝ = (Real.sqrt i.1.val)⁻¹ *
      ⟪resolventEigenbasisSigma (I := I) (M := M) g i,
        H1ComplToLp (I := I) (M := M) g u⟫_ℝ := by
  rw [h1SpectralVector, real_inner_smul_left, resolvent_inner_eq_lpFunctional,
    real_inner_comm]

theorem h1SpectralVector_orthonormal (g : SmoothRiemannianMetric I M) :
    Orthonormal ℝ (h1SpectralVector g) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hi := nonzeroResolventEigenvalue_pos i.1
  have hj := nonzeroResolventEigenvalue_pos j.1
  have hb := resolventEigenbasisVec_orthonormal (I := I) (M := M) g
  have hb' : ⟪resolventEigenbasisSigma (I := I) (M := M) g i,
      resolventEigenbasisSigma (I := I) (M := M) g j⟫_ℝ = if i = j then 1 else 0 := by
    rw [resolventEigenbasisSigma_eq_resolventEigenbasisVec,
      resolventEigenbasisSigma_eq_resolventEigenbasisVec]
    exact orthonormal_iff_ite.mp hb i j
  rw [h1SpectralVector_inner, h1SpectralVector,
    (H1ComplToLp (I := I) (M := M) g).map_smul, ← resolventL2_apply,
    resolventL2_apply_resolventEigenbasisSigma, real_inner_smul_right,
    real_inner_smul_right, hb']
  split_ifs with hij
  · subst j
    have hs := Real.sq_sqrt hi.le
    have hsn := (Real.sqrt_pos.mpr hi).ne'
    field_simp
    nlinarith
  · ring

theorem h1SpectralVector_inner_sq (g : SmoothRiemannianMetric I M)
    (i : ScalarIndex g) (u : H1Compl g) :
    ‖⟪h1SpectralVector g i, u⟫_ℝ‖ ^ 2 = i.1.val⁻¹ *
      (⟪resolventEigenbasisSigma (I := I) (M := M) g i,
        H1ComplToLp (I := I) (M := M) g u⟫_ℝ) ^ 2 := by
  rw [h1SpectralVector_inner, Real.norm_eq_abs, sq_abs, mul_pow,
    inv_pow, Real.sq_sqrt (nonzeroResolventEigenvalue_pos i.1).le]

omit [NeZero (Module.finrank ℝ E)] in
theorem inverse_resolventEigenvalue (g : SmoothRiemannianMetric I M)
    (i : ScalarIndex g) : i.1.val⁻¹ = 1 + laplacianEigenvalueOf i.1.val := by
  unfold laplacianEigenvalueOf
  field_simp [i.1.val_ne_zero]
  ring

/-- All H¹ vectors, not only operator-domain eigenfunctions or radial
tests. The zero-eigenvalue orthogonality is the general mean-zero
condition; the round-sphere application derives it from harmonic
rigidity and the ordinary zero integral. -/
theorem h1_poincare_of_actual_spectral_lower (g : SmoothRiemannianMetric I M)
    (C : ℝ)
    (hgap : ∀ i : ScalarIndex g, 0 < laplacianEigenvalueOf i.1.val →
      C ≤ laplacianEigenvalueOf i.1.val)
    (u : H1Compl g)
    (hzero : ∀ i : ScalarIndex g, laplacianEigenvalueOf i.1.val = 0 →
      ⟪resolventEigenbasisSigma (I := I) (M := M) g i,
        H1ComplToLp (I := I) (M := M) g u⟫_ℝ = 0) :
    C * ‖H1ComplToLp (I := I) (M := M) g u‖ ^ 2 ≤
      ‖u‖ ^ 2 - ‖H1ComplToLp (I := I) (M := M) g u‖ ^ 2 := by
  classical
  let b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  let Ju := H1ComplToLp (I := I) (M := M) g u
  let c : ScalarIndex g → ℝ := fun i => ⟪b i, Ju⟫_ℝ
  have hc : Summable (fun i => (c i) ^ 2) := by
    simpa only [c, sq, real_inner_comm] using b.summable_inner_mul_inner Ju Ju
  have hcSum : (∑' i, (c i) ^ 2) = ‖Ju‖ ^ 2 := by
    simpa only [c, sq, real_inner_comm, real_inner_self_eq_norm_sq] using
      b.tsum_inner_mul_inner Ju Ju
  have hvec := h1SpectralVector_orthonormal g
  have he := hvec.inner_products_summable u
  have hpoint (i : ScalarIndex g) :
      (C + 1) * (c i) ^ 2 ≤ ‖⟪h1SpectralVector g i, u⟫_ℝ‖ ^ 2 := by
    rw [h1SpectralVector_inner_sq, inverse_resolventEigenvalue]
    change (C + 1) * (c i) ^ 2 ≤ (1 + laplacianEigenvalueOf i.1.val) * (c i) ^ 2
    by_cases h0 : laplacianEigenvalueOf i.1.val = 0
    · have hz : c i = 0 := hzero i h0
      rw [hz]
      simp
    · have hp : 0 < laplacianEigenvalueOf i.1.val :=
        lt_of_le_of_ne (laplacianEigenvalueOf_nonneg i.1) (Ne.symm h0)
      exact mul_le_mul_of_nonneg_right (by linarith [hgap i hp]) (sq_nonneg _)
  have hsum := Summable.tsum_le_tsum hpoint (hc.mul_left (C + 1)) he
  rw [tsum_mul_left, hcSum] at hsum
  have hbessel := hvec.tsum_inner_products_le u
  have hle := hsum.trans hbessel
  dsimp only [Ju] at hle
  nlinarith

end DFLSphere

#print axioms DFLSphere.h1_poincare_of_actual_spectral_lower
