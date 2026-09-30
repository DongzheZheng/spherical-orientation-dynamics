import DFLSphere433.OriginalLatitude.SphereMeasure

/-!
# Algebraic ordering of the original sphere's angular penalties

The coefficient `ℓ(ℓ+d-2)` is the eigenvalue of `-Δ_{S^(d-1)}` in the
`ℓ`th angular sector.  The result below is the pointwise coercivity
calculation used by the manuscript.  It does **not** prove that every
`H¹(Sᵈ)` function decomposes into these sectors, nor does it identify the
first eigenvalue of the full diffusion operator.
-/

namespace DFL.Spectral

open Set
open MeasureTheory
open scoped Interval

noncomputable section

def angularCoefficient (d ℓ : ℕ) : ℝ :=
  (ℓ : ℝ) * ((ℓ : ℝ) + (d : ℝ) - 2)

theorem angularCoefficient_difference (d ℓ : ℕ) :
    angularCoefficient d ℓ - angularCoefficient d 1 =
      ((ℓ : ℝ) - 1) * ((ℓ : ℝ) + (d : ℝ) - 1) := by
  unfold angularCoefficient
  ring

theorem higher_angular_pointwise
    (d ℓ : ℕ) (hd : 2 ≤ d) (hℓ : 2 ≤ ℓ)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (y : ℝ) :
    ((ℓ : ℝ) - 1) * ((ℓ : ℝ) + (d : ℝ) - 1) * y ^ 2 ≤
      ((angularCoefficient d ℓ - angularCoefficient d 1) / (1 - t ^ 2)) * y ^ 2 := by
  let δ : ℝ := ((ℓ : ℝ) - 1) * ((ℓ : ℝ) + (d : ℝ) - 1)
  have hℓ' : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact mul_nonneg (by linarith) (by linarith)
  have hwpos : 0 < 1 - t ^ 2 := by
    rcases ht with ⟨htl, htr⟩
    nlinarith
  have hwle : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  have hδw : δ ≤ δ / (1 - t ^ 2) := by
    apply (le_div_iff₀ hwpos).2
    nlinarith [mul_le_mul_of_nonneg_left hwle hδ]
  simpa [δ, angularCoefficient_difference] using
    mul_le_mul_of_nonneg_right hδw (sq_nonneg y)

theorem higher_angular_pointwise_strict
    (d ℓ : ℕ) (hd : 2 ≤ d) (hℓ : 2 ≤ ℓ)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) {y : ℝ} (hy : y ≠ 0) :
    0 < ((angularCoefficient d ℓ - angularCoefficient d 1) / (1 - t ^ 2)) * y ^ 2 := by
  have hℓ' : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hδ : 0 < ((ℓ : ℝ) - 1) * ((ℓ : ℝ) + (d : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  have hwpos : 0 < 1 - t ^ 2 := by
    rcases ht with ⟨htl, htr⟩
    nlinarith
  rw [angularCoefficient_difference]
  exact mul_pos (div_pos hδ hwpos) (sq_pos_of_ne_zero hy)

/-- Exact latitude weight of the original `Sᵈ` angular decomposition. -/
def radialWeight (d : ℕ) (r t : ℝ) : ℝ :=
  Real.exp (r * t) * Real.rpow (1 - t ^ 2) (((d : ℝ) - 2) / 2)

theorem radialWeight_pos (d : ℕ) (r : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < radialWeight d r t := by
  have hwpos : 0 < 1 - t ^ 2 := by
    rcases ht with ⟨htl, htr⟩
    nlinarith
  unfold radialWeight
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hwpos _)

/-- The angular penalty difference pays at least the explicit sector gap
pointwise with the exact original latitude weight. -/
theorem weighted_higher_angular_pointwise
    (d ℓ : ℕ) (hd : 2 ≤ d) (hℓ : 2 ≤ ℓ) (r : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (y : ℝ) :
    radialWeight d r t *
      (((ℓ : ℝ) - 1) * ((ℓ : ℝ) + (d : ℝ) - 1) * y ^ 2) ≤
    radialWeight d r t *
      (((angularCoefficient d ℓ - angularCoefficient d 1) / (1 - t ^ 2)) * y ^ 2) := by
  exact mul_le_mul_of_nonneg_left (higher_angular_pointwise d ℓ hd hℓ ht y)
    (radialWeight_pos d r ht).le

/-- Integrated version on the common original latitude interval.  The two
integrability hypotheses are explicit here; identifying them with the
`H¹(Sᵈ)` angular form domains remains a separate geometric theorem. -/
theorem weighted_higher_angular_integral
    (d ℓ : ℕ) (hd : 2 ≤ d) (hℓ : 2 ≤ ℓ) (r : ℝ) (y : ℝ → ℝ)
    (hleft : IntervalIntegrable
      (fun t : ℝ => radialWeight d r t *
        (((ℓ : ℝ) - 1) * ((ℓ : ℝ) + (d : ℝ) - 1) * (y t) ^ 2))
      volume (-1 : ℝ) 1)
    (hright : IntervalIntegrable
      (fun t : ℝ => radialWeight d r t *
        (((angularCoefficient d ℓ - angularCoefficient d 1) / (1 - t ^ 2)) *
          (y t) ^ 2))
      volume (-1 : ℝ) 1) :
    (∫ t in (-1 : ℝ)..1, radialWeight d r t *
      (((ℓ : ℝ) - 1) * ((ℓ : ℝ) + (d : ℝ) - 1) * (y t) ^ 2)) ≤
    (∫ t in (-1 : ℝ)..1, radialWeight d r t *
      (((angularCoefficient d ℓ - angularCoefficient d 1) / (1 - t ^ 2)) *
        (y t) ^ 2)) := by
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hleft hright
  intro t ht
  exact weighted_higher_angular_pointwise d ℓ hd hℓ r ht (y t)

end

end DFL.Spectral
