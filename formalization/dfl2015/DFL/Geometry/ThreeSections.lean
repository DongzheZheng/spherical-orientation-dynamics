import DFL.Geometry.ThreeFubini

/-!
# Disk sections of the three-dimensional cap cone

The cone is taken from the actual Measure.toSphere source. The following
two sections are the geometric core of Archimedes' spherical-band formula.
-/

namespace DFL.Geometry

open MeasureTheory

noncomputable section

private theorem radius_small_sq {t s : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (s * Real.sqrt (1 - t ^ 2) / t) ^ 2 =
      s ^ 2 * (1 - t ^ 2) / t ^ 2 := by
  have hrad : 0 ≤ 1 - t ^ 2 := by nlinarith
  rw [div_pow, mul_pow, Real.sq_sqrt hrad]

private theorem radius_small_pos {t s : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hs : 0 < s) : 0 < s * Real.sqrt (1 - t ^ 2) / t := by
  have hrad : 0 < 1 - t ^ 2 := by nlinarith
  positivity

private theorem norm_splitThree_symm_pos {s : ℝ} (hs : 0 < s) (y : Ambient 2) :
    0 < ‖splitThree.symm (s, y)‖ := by
  have h := splitThree_symm_norm_sq s y
  nlinarith [sq_nonneg ‖y‖, norm_nonneg (splitThree.symm (s, y))]

theorem coneCapThree_section_small (t s : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (hs : 0 < s) (hst : s < t) :
    {y : Ambient 2 | splitThree.symm (s, y) ∈ coneCapThree t} =
      Metric.ball 0 (s * Real.sqrt (1 - t ^ 2) / t) := by
  ext y
  let N : ℝ := ‖splitThree.symm (s, y)‖
  let u : ℝ := ‖y‖
  let R : ℝ := s * Real.sqrt (1 - t ^ 2) / t
  have hN2 : N ^ 2 = s ^ 2 + u ^ 2 := splitThree_symm_norm_sq s y
  have hR2 : R ^ 2 = s ^ 2 * (1 - t ^ 2) / t ^ 2 :=
    radius_small_sq ht ht1
  have htne : t ≠ 0 := ne_of_gt ht
  have hR2mul : t ^ 2 * R ^ 2 = s ^ 2 * (1 - t ^ 2) := by
    rw [hR2]
    field_simp
  have hN2mul : t ^ 2 * N ^ 2 = t ^ 2 * s ^ 2 + t ^ 2 * u ^ 2 := by
    rw [hN2]
    ring
  have hRpos : 0 < R := radius_small_pos ht ht1 hs
  have hNpos : 0 < N := norm_splitThree_symm_pos hs y
  have hupos : 0 ≤ u := norm_nonneg y
  simp only [Set.mem_setOf_eq, mem_coneCapThree_iff, splitThree_symm_fst,
    Metric.mem_ball, dist_zero_right]
  change (0 < N ∧ N < 1 ∧ t * N < s) ↔ u < R
  constructor
  · rintro ⟨_, _, hcap⟩
    have hcap2 : t ^ 2 * N ^ 2 < s ^ 2 := by
      simpa only [mul_pow] using
        (sq_lt_sq₀ (mul_nonneg ht.le hNpos.le) hs.le).2 hcap
    have hu2 : u ^ 2 < R ^ 2 := by
      have htu : t ^ 2 * u ^ 2 < s ^ 2 * (1 - t ^ 2) := by
        nlinarith [hN2mul]
      nlinarith [hR2mul, sq_pos_of_pos ht]
    nlinarith
  · intro huy
    have hu2 : u ^ 2 < R ^ 2 := by nlinarith
    have htu : t ^ 2 * u ^ 2 < s ^ 2 * (1 - t ^ 2) := by
      nlinarith [hR2mul, sq_pos_of_pos ht]
    have hcap2 : t ^ 2 * N ^ 2 < s ^ 2 := by
      nlinarith [hN2mul]
    have hcap : t * N < s := by nlinarith
    have hball : N < 1 := by nlinarith
    exact ⟨hNpos, hball, hcap⟩

theorem coneCapThree_section_large (t s : ℝ)
    (ht : 0 < t) (hts : t ≤ s) (hs1 : s < 1) :
    {y : Ambient 2 | splitThree.symm (s, y) ∈ coneCapThree t} =
      Metric.ball 0 (Real.sqrt (1 - s ^ 2)) := by
  ext y
  let N : ℝ := ‖splitThree.symm (s, y)‖
  let u : ℝ := ‖y‖
  let R : ℝ := Real.sqrt (1 - s ^ 2)
  have hs : 0 < s := lt_of_lt_of_le ht hts
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hRpos : 0 < R := Real.sqrt_pos.2 hrad
  have hR2 : R ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hrad.le
  have hN2 : N ^ 2 = s ^ 2 + u ^ 2 := splitThree_symm_norm_sq s y
  have hNpos : 0 < N := norm_splitThree_symm_pos hs y
  simp only [Set.mem_setOf_eq, mem_coneCapThree_iff, splitThree_symm_fst,
    Metric.mem_ball, dist_zero_right]
  change (0 < N ∧ N < 1 ∧ t * N < s) ↔ u < R
  constructor
  · rintro ⟨_, hball, _⟩
    nlinarith [norm_nonneg y]
  · intro huy
    have huy2 : u ^ 2 < R ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg y) hRpos.le).2 huy
    have hball2 : N ^ 2 < (1 : ℝ) ^ 2 := by nlinarith
    have hball : N < 1 :=
      (sq_lt_sq₀ hNpos.le (by norm_num)).1 hball2
    have hcap : t * N < s := by nlinarith
    exact ⟨hNpos, hball, hcap⟩

theorem coneCapThree_section_empty_of_nonpos (t s : ℝ)
    (ht : 0 < t) (hs : s ≤ 0) :
    {y : Ambient 2 | splitThree.symm (s, y) ∈ coneCapThree t} = ∅ := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hy
  obtain ⟨hN, _, hcap⟩ := (mem_coneCapThree_iff t _).1 hy
  rw [splitThree_symm_fst] at hcap
  nlinarith [mul_pos ht hN]

theorem coneCapThree_section_empty_of_one_le (t s : ℝ)
    (hs : 1 ≤ s) :
    {y : Ambient 2 | splitThree.symm (s, y) ∈ coneCapThree t} = ∅ := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hy
  obtain ⟨_, hN, _⟩ := (mem_coneCapThree_iff t _).1 hy
  have hNsq := splitThree_symm_norm_sq s y
  nlinarith [sq_nonneg ‖y‖, norm_nonneg (splitThree.symm (s, y))]

end

end DFL.Geometry
