import DFL.Geometry.SuccCapSections

/-!
# Explicit Fubini integrand for actual spherical caps in all dimensions

The formula identifies the true Euclidean section volume pointwise. It does
not claim that the final one-dimensional beta integral has been evaluated.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped ENNReal

noncomputable section

def capSliceVolume (m : ℕ) (t s : ℝ) : ℝ≥0∞ :=
  if 0 < s ∧ s < t then
    volume (Metric.ball (0 : Ambient m)
      (s * Real.sqrt (1 - t ^ 2) / t))
  else if t ≤ s ∧ s < 1 then
    volume (Metric.ball (0 : Ambient m) (Real.sqrt (1 - s ^ 2)))
  else 0

/-- The exact transverse-ball volume factor for a positive integer
dimension, expressed with mathlib's Gamma normalization. -/
def transverseBallVolume (m : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal r ^ m *
    ENNReal.ofReal (Real.sqrt Real.pi ^ m /
      Real.Gamma ((m : ℝ) / 2 + 1))

theorem ambient_ball_volume (m : ℕ) (hm : 0 < m) (r : ℝ) :
    volume (Metric.ball (0 : Ambient m) r) =
      transverseBallVolume m r := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  simpa [transverseBallVolume] using
    EuclideanSpace.volume_ball (Fin m) (0 : Ambient m) r

def scalarCapKernel (m : ℕ) (t s : ℝ) : ℝ≥0∞ :=
  if 0 < s ∧ s < t then
    transverseBallVolume m (s * Real.sqrt (1 - t ^ 2) / t)
  else if t ≤ s ∧ s < 1 then
    transverseBallVolume m (Real.sqrt (1 - s ^ 2))
  else 0

theorem capSliceVolume_eq_scalarCapKernel
    (m : ℕ) (hm : 0 < m) (t s : ℝ) :
    capSliceVolume m t s = scalarCapKernel m t s := by
  simp [capSliceVolume, scalarCapKernel, ambient_ball_volume m hm]

theorem coneCapSucc_section_volume (m : ℕ) (t s : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    volume {y : Ambient m |
      (splitSucc m).symm (s, y) ∈ coneCapSucc m t} =
        capSliceVolume m t s := by
  by_cases hs : 0 < s
  · by_cases hst : s < t
    · rw [coneCapSucc_section_small m t s ht ht1 hs hst]
      simp [capSliceVolume, hs, hst]
    · have hts : t ≤ s := le_of_not_gt hst
      by_cases hs1 : s < 1
      · rw [coneCapSucc_section_large m t s ht hts hs1]
        simp [capSliceVolume, hst, hts, hs1]
      · have h1s : 1 ≤ s := le_of_not_gt hs1
        rw [coneCapSucc_section_empty_of_one_le m t s h1s]
        simp [capSliceVolume, hst, hs1]
  · have hs0 : s ≤ 0 := le_of_not_gt hs
    rw [coneCapSucc_section_empty_of_nonpos m t s ht hs0]
    have hts : ¬t ≤ s := by linarith
    simp [capSliceVolume, hs, hts]

/-- An exact scalar Lebesgue integral for the volume of the cone over the
original spherical cap in dimension `m+1`. -/
theorem coneCapSucc_volume_scalar (m : ℕ) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    volume (coneCapSucc m t) = ∫⁻ s : ℝ, capSliceVolume m t s := by
  rw [coneCapSucc_volume_fubini]
  simp_rw [coneCapSucc_section_volume m t _ ht ht1]

/-- General `n=m+1≥2` cap-volume reduction with every geometric section
replaced by its explicit Gamma-normalized Euclidean ball volume. The
remaining integration is a real-variable beta integral. -/
theorem coneCapSucc_volume_gamma (m : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    volume (coneCapSucc m t) = ∫⁻ s : ℝ, scalarCapKernel m t s := by
  rw [coneCapSucc_volume_scalar m t ht ht1]
  simp_rw [capSliceVolume_eq_scalarCapKernel m hm t]

theorem area_sphereCapSucc_gamma (m : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    area (m + 1) (sphereCapSucc m t) =
      (m + 1 : ℝ≥0∞) * ∫⁻ s : ℝ, scalarCapKernel m t s := by
  rw [area_sphereCapSucc, coneCapSucc_volume_gamma m hm t ht ht1]

/-- The genuine first-coordinate law itself, rather than a surrogate
measure, has the Gamma-ball Fubini formula on every positive strict tail. -/
theorem coordinateLaw_succ_Ioi_gamma (m : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    coordinateLaw (m + 1) (by omega) (Set.Ioi t) =
      (m + 1 : ℝ≥0∞) * ∫⁻ s : ℝ, scalarCapKernel m t s := by
  rw [coordinateLaw, Measure.map_apply
    (continuous_coordinate (m + 1) (by omega)).measurable
      measurableSet_Ioi]
  change area (m + 1) (sphereCapSucc m t) = _
  exact area_sphereCapSucc_gamma m hm t ht ht1

end

end DFL.Geometry
