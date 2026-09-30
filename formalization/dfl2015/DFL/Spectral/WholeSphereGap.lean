import DFL.Spectral.CoreCoordinate

/-!
# A global original-sphere smooth-core Rayleigh infimum

The infimum here ranges over every ambient `C¹` function restricted to the
actual unit sphere, with the projected tangent gradient and exact vMF law.
It is not yet identified with the full closed `H¹(Sᵈ)` spectral gap from
Degond--Frouvelle--Liu Conjecture A.1.
-/

namespace DFL.Spectral

open MeasureTheory

noncomputable section

/-- Rayleigh quotient on the full physical sphere for one smooth test. -/
def coreRayleigh (d : ℕ) (r : ℝ) (f : SphereC1Core d) : ℝ :=
  coreEnergy d r f / sphereVariance d r (coreValue d f)

/-- All nonconstant smooth-core Rayleigh values of the complete sphere. -/
def coreRayleighValues (d : ℕ) (r : ℝ) : Set ℝ :=
  {q | ∃ f : SphereC1Core d,
    0 < sphereVariance d r (coreValue d f) ∧ q = coreRayleigh d r f}

/-- The global smooth-core infimum. Its equality with the closed `H¹`
spectral gap needs a density/completion theorem. -/
def coreGap (d : ℕ) (r : ℝ) : ℝ := sInf (coreRayleighValues d r)

theorem coreEnergy_nonneg (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    0 ≤ coreEnergy d r f := by
  unfold coreEnergy
  exact integral_nonneg (fun x => sq_nonneg _)

theorem coreRayleigh_nonneg (d : ℕ) (r : ℝ) (f : SphereC1Core d)
    (hvar : 0 < sphereVariance d r (coreValue d f)) :
    0 ≤ coreRayleigh d r f :=
  div_nonneg (coreEnergy_nonneg d r f) hvar.le

theorem coordinateCore_variance_zero (d : ℕ) (i : Fin (d + 1)) :
    sphereVariance d 0 (coreValue d (coordinateCore d i)) =
      1 / (d + 1 : ℝ) := by
  change sphereVariance d 0 (sphereCoordinate d i) = _
  exact sphereCoordinate_variance_zero d i

theorem coordinateCore_variance_pos (d : ℕ) (r : ℝ)
    (i : Fin (d + 1)) :
    0 < sphereVariance d r (coreValue d (coordinateCore d i)) := by
  have h0 : 0 < sphereVariance d 0 (coreValue d (coordinateCore d i)) := by
    rw [coordinateCore_variance_zero]
    positivity
  have hb := (coreVariance_bounds d r (coordinateCore d i)).1
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) h0) hb

theorem coreRayleighValues_nonempty (d : ℕ) (r : ℝ) :
    (coreRayleighValues d r).Nonempty := by
  refine ⟨coreRayleigh d r (coordinateCore d 0),
    coordinateCore d 0, coordinateCore_variance_pos d r 0, rfl⟩

theorem coreRayleighValues_bddBelow (d : ℕ) (r : ℝ) :
    BddBelow (coreRayleighValues d r) := by
  refine ⟨0, ?_⟩
  intro q hq
  rcases hq with ⟨f, hvar, rfl⟩
  exact coreRayleigh_nonneg d r f hvar

/-- The actual whole-sphere smooth-core Rayleigh infimum is a finite
nonnegative real number for every finite vMF field. -/
theorem coreGap_nonneg (d : ℕ) (r : ℝ) : 0 ≤ coreGap d r := by
  unfold coreGap
  apply le_csInf (coreRayleighValues_nonempty d r)
  intro q hq
  rcases hq with ⟨f, hvar, rfl⟩
  exact coreRayleigh_nonneg d r f hvar

theorem coreRayleigh_coordinate_zero (d : ℕ) (i : Fin (d + 1)) :
    coreRayleigh d 0 (coordinateCore d i) = d := by
  rw [coreRayleigh, coordinateCore_energy_zero,
    coordinateCore_variance_zero]
  have h : (d + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- A proper global variational upper bound at zero field, now for a
defined whole-sphere smooth-core infimum rather than an isolated ratio. -/
theorem coreGap_zero_le_dimension (d : ℕ) : coreGap d 0 ≤ d := by
  have hmem : (d : ℝ) ∈ coreRayleighValues d 0 := by
    refine ⟨coordinateCore d 0, coordinateCore_variance_pos d 0 0, ?_⟩
    exact (coreRayleigh_coordinate_zero d 0).symm
  exact csInf_le (coreRayleighValues_bddBelow d 0) hmem

/-- Every nonconstant smooth test has a finite-field Rayleigh ratio bounded
below by its zero-field ratio times `exp(-4|r|)`. This is a statement about
the *same original-sphere test function* on both sides. -/
theorem coreRayleigh_field_lower (d : ℕ) (r : ℝ)
    (f : SphereC1Core d)
    (hv0 : 0 < sphereVariance d 0 (coreValue d f)) :
    (Real.exp (-2 * |r|)) ^ 2 * coreRayleigh d 0 f ≤
      coreRayleigh d r f := by
  let b : ℝ := Real.exp (-2 * |r|)
  let a : ℝ := Real.exp (2 * |r|)
  have hba : b * a = 1 := by
    dsimp [b, a]
    rw [← Real.exp_add]
    have h : -2 * |r| + 2 * |r| = 0 := by ring
    rw [h, Real.exp_zero]
  have hE0 : 0 ≤ coreEnergy d 0 f := coreEnergy_nonneg d 0 f
  have hE := (coreEnergy_bounds d r f).1
  have hV := coreVariance_bounds d r f
  have hvr : 0 < sphereVariance d r (coreValue d f) :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) hv0) hV.1
  have hmain :
      (b ^ 2 * coreEnergy d 0 f) /
          sphereVariance d 0 (coreValue d f) ≤
        coreEnergy d r f / sphereVariance d r (coreValue d f) := by
    apply (div_le_div_iff₀ hv0 hvr).2
    calc
      (b ^ 2 * coreEnergy d 0 f) * sphereVariance d r (coreValue d f) ≤
          (b ^ 2 * coreEnergy d 0 f) *
            (a * sphereVariance d 0 (coreValue d f)) :=
        mul_le_mul_of_nonneg_left hV.2
          (mul_nonneg (sq_nonneg _) hE0)
      _ = (b * a) *
          (b * coreEnergy d 0 f * sphereVariance d 0 (coreValue d f)) := by ring
      _ = b * coreEnergy d 0 f * sphereVariance d 0 (coreValue d f) := by
        rw [hba, one_mul]
      _ ≤ coreEnergy d r f * sphereVariance d 0 (coreValue d f) :=
        mul_le_mul_of_nonneg_right hE hv0.le
  simpa only [coreRayleigh, b, mul_div_assoc] using hmain

/-- The complete smooth-core Rayleigh infimum cannot decrease faster than
`exp(-4|r|)` relative to zero field. This is a global all-test theorem,
not the strict increase asserted by Conjecture A.1. -/
theorem coreGap_field_lower (d : ℕ) (r : ℝ) :
    (Real.exp (-2 * |r|)) ^ 2 * coreGap d 0 ≤ coreGap d r := by
  unfold coreGap
  apply le_csInf (coreRayleighValues_nonempty d r)
  intro q hq
  rcases hq with ⟨f, hvr, rfl⟩
  have hV := (coreVariance_bounds d r f).2
  have hv0 : 0 < sphereVariance d 0 (coreValue d f) := by
    by_contra hn
    have hnonpos : sphereVariance d 0 (coreValue d f) ≤ 0 := le_of_not_gt hn
    have hmul : Real.exp (2 * |r|) *
        sphereVariance d 0 (coreValue d f) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hnonpos
    exact (not_lt_of_ge (le_trans hV hmul)) hvr
  have h0mem : coreRayleigh d 0 f ∈ coreRayleighValues d 0 :=
    ⟨f, hv0, rfl⟩
  calc
    (Real.exp (-2 * |r|)) ^ 2 * sInf (coreRayleighValues d 0) ≤
        (Real.exp (-2 * |r|)) ^ 2 * coreRayleigh d 0 f :=
      mul_le_mul_of_nonneg_left
        (csInf_le (coreRayleighValues_bddBelow d 0) h0mem)
        (sq_nonneg _)
    _ ≤ coreRayleigh d r f := coreRayleigh_field_lower d r f hv0

end

end DFL.Spectral
