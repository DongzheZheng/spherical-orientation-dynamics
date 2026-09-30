import Mathlib

/-!
# The original sphere and von Mises--Fisher weight

These definitions keep the ambient sphere in the target.  They are not a
one-dimensional substitute for the weighted `H¹(Sᵈ)` Rayleigh problem.
The cone-induced surface measure from `Measure.toSphere` is a constant
multiple of geometric area measure; that identification is not yet proved
in this project, so no spectral conjecture is claimed here.
-/

namespace DFL.Spectral

open MeasureTheory
open Metric

noncomputable section

/-- Original ambient Euclidean space `ℝ^(d+1)`. -/
abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

/-- The unit sphere `Sᵈ` as an actual subspace of `ℝ^(d+1)`. -/
abbrev SpherePoint (d : ℕ) := sphere (0 : Ambient d) 1

/-- The surface measure obtained from ambient Lebesgue measure by polar
decomposition.  It is finite and positive on nonempty open sets. -/
def surfaceMeasure (d : ℕ) : Measure (SpherePoint d) :=
  (volume : Measure (Ambient d)).toSphere

/-- Coordinate along the imposed field, after rotating the field to `e₀`. -/
def fieldCoordinate (d : ℕ) (x : SpherePoint d) : ℝ := x.1 0

/-- The exact von Mises--Fisher density of the original spherical problem. -/
def fieldWeight (d : ℕ) (r : ℝ) (x : SpherePoint d) : ℝ :=
  Real.exp (r * fieldCoordinate d x)

theorem fieldWeight_pos (d : ℕ) (r : ℝ) (x : SpherePoint d) :
    0 < fieldWeight d r x := by
  exact Real.exp_pos _

/-- The original field coordinate lies in `[-1,1]` on the unit sphere. -/
theorem fieldCoordinate_abs_le_one (d : ℕ) (x : SpherePoint d) :
    |fieldCoordinate d x| ≤ 1 := by
  have hx : ‖(x.1 : Ambient d)‖ = 1 := by
    simp at x ⊢
  calc
    |fieldCoordinate d x| = ‖fieldCoordinate d x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖(x.1 : Ambient d)‖ := PiLp.norm_apply_le x.1 0
    _ = 1 := hx

/-- Uniform positive comparison of the actual spherical field density to
the zero-field density, for each finite field strength. -/
theorem fieldWeight_bounds (d : ℕ) (r : ℝ) (x : SpherePoint d) :
    Real.exp (-|r|) ≤ fieldWeight d r x ∧
    fieldWeight d r x ≤ Real.exp |r| := by
  have hcoord := fieldCoordinate_abs_le_one d x
  have hprod : |r * fieldCoordinate d x| ≤ |r| := by
    calc
      |r * fieldCoordinate d x| = |r| * |fieldCoordinate d x| := abs_mul _ _
      _ ≤ |r| * 1 := mul_le_mul_of_nonneg_left hcoord (abs_nonneg r)
      _ = |r| := mul_one _
  obtain ⟨hlo, hhi⟩ := abs_le.mp hprod
  constructor
  · exact Real.exp_le_exp.mpr hlo
  · exact Real.exp_le_exp.mpr hhi

theorem fieldCoordinate_continuous (d : ℕ) :
    Continuous (fieldCoordinate d) := by
  unfold fieldCoordinate
  fun_prop

theorem fieldWeight_continuous (d : ℕ) (r : ℝ) :
    Continuous (fieldWeight d r) := by
  unfold fieldWeight
  exact Real.continuous_exp.comp (continuous_const.mul (fieldCoordinate_continuous d))

/-- The physical exponential weight is integrable on the original compact
sphere for every finite field strength. -/
theorem fieldWeight_integrable (d : ℕ) (r : ℝ) :
    Integrable (fieldWeight d r) (surfaceMeasure d) := by
  have : IsFiniteMeasure (surfaceMeasure d) := by
    change IsFiniteMeasure ((volume : Measure (Ambient d)).toSphere)
    infer_instance
  refine Integrable.of_bound (fieldWeight_continuous d r).aestronglyMeasurable
    (Real.exp |r|) ?_
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (fieldWeight_pos d r x)]
    exact (fieldWeight_bounds d r x).2)

/-- The original normalized von Mises--Fisher law is Mathlib's exponential
tilt of surface measure. -/
def alignedMeasure (d : ℕ) (r : ℝ) : Measure (SpherePoint d) :=
  (surfaceMeasure d).tilted (fun x => r * fieldCoordinate d x)

theorem surfaceMeasure_ne_zero (d : ℕ) : surfaceMeasure d ≠ 0 := by
  unfold surfaceMeasure
  exact Measure.toSphere_ne_zero (volume : Measure (Ambient d))

/-- The original von Mises--Fisher law has total mass one, without an
integrability or normalization hypothesis inserted into the theorem. -/
theorem alignedMeasure_probability (d : ℕ) (r : ℝ) :
    IsProbabilityMeasure (alignedMeasure d r) := by
  let _ : NeZero (surfaceMeasure d) := ⟨surfaceMeasure_ne_zero d⟩
  exact MeasureTheory.isProbabilityMeasure_tilted (fieldWeight_integrable d r)

/-- At zero field, the physical law is the normalized cone-induced surface
measure on the same unit sphere. -/
theorem alignedMeasure_zero (d : ℕ) :
    alignedMeasure d 0 = ((surfaceMeasure d) Set.univ)⁻¹ • surfaceMeasure d := by
  simp [alignedMeasure]

/-- Null sets of the weighted and unweighted original sphere agree.  This
is one necessary ingredient for keeping the physical form domain fixed. -/
theorem alignedMeasure_equivalent (d : ℕ) (r : ℝ) :
    alignedMeasure d r ≪ surfaceMeasure d ∧
    surfaceMeasure d ≪ alignedMeasure d r := by
  constructor
  · exact MeasureTheory.tilted_absolutelyContinuous _ _
  · exact MeasureTheory.absolutelyContinuous_tilted (fieldWeight_integrable d r)

/-- A measurable scalar field is integrable for the weighted original sphere
if and only if it is integrable for the unweighted sphere. This uses the
actual uniformly bounded positive vMF density, not an assumed domain bridge. -/
theorem integrable_aligned_iff (d : ℕ) (r : ℝ)
    (g : SpherePoint d → ℝ)
    (hg : AEStronglyMeasurable g (surfaceMeasure d)) :
    Integrable g (alignedMeasure d r) ↔
      Integrable g (surfaceMeasure d) := by
  rw [alignedMeasure, integrable_tilted_iff (fieldWeight_integrable d r) g]
  change Integrable (fun x => fieldWeight d r x * g x) (surfaceMeasure d) ↔
    Integrable g (surfaceMeasure d)
  constructor
  · intro hweighted
    have hdom : ∀ᵐ x ∂surfaceMeasure d,
        ‖g x‖ ≤ ‖Real.exp |r| * (fieldWeight d r x * g x)‖ :=
      ae_of_all _ (fun x => by
        have hcoeff : 1 ≤ Real.exp |r| * fieldWeight d r x := calc
          1 = Real.exp |r| * Real.exp (-|r|) := by
            rw [← Real.exp_add]
            simp
          _ ≤ Real.exp |r| * fieldWeight d r x :=
            mul_le_mul_of_nonneg_left (fieldWeight_bounds d r x).1
              (Real.exp_pos _).le
        calc
          ‖g x‖ = 1 * ‖g x‖ := by ring
          _ ≤ (Real.exp |r| * fieldWeight d r x) * ‖g x‖ :=
            mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
          _ = ‖Real.exp |r| * (fieldWeight d r x * g x)‖ := by
            simp [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              abs_of_pos (fieldWeight_pos d r x), mul_assoc])
    exact Integrable.mono (hweighted.const_mul (Real.exp |r|)) hg hdom
  · intro hplain
    have hmeas : AEStronglyMeasurable (fun x => fieldWeight d r x * g x)
        (surfaceMeasure d) :=
      (fieldWeight_continuous d r).aestronglyMeasurable.mul hg
    have hdom : ∀ᵐ x ∂surfaceMeasure d,
        ‖fieldWeight d r x * g x‖ ≤ ‖Real.exp |r| * g x‖ :=
      ae_of_all _ (fun x => by
        have h := mul_le_mul_of_nonneg_right (fieldWeight_bounds d r x).2
          (abs_nonneg (g x))
        simpa [norm_mul, Real.norm_eq_abs,
          abs_of_pos (fieldWeight_pos d r x), abs_of_pos (Real.exp_pos _)] using h)
    exact Integrable.mono (hplain.const_mul (Real.exp |r|)) hmeas hdom

/-- The `L²` admissibility of a measurable scalar field is independent of
the finite field strength.  The same statement applies to any measurable
tangential-gradient norm once that gradient is defined on the original
sphere. -/
theorem square_integrable_aligned_iff (d : ℕ) (r : ℝ)
    (g : SpherePoint d → ℝ)
    (hg : AEStronglyMeasurable g (surfaceMeasure d)) :
    Integrable (fun x => (g x) ^ 2) (alignedMeasure d r) ↔
      Integrable (fun x => (g x) ^ 2) (surfaceMeasure d) := by
  simpa only [pow_two] using
    integrable_aligned_iff d r (fun x => g x * g x) (hg.mul hg)

end

end DFL.Spectral
