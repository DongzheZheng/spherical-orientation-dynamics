import Mathlib

/-!
# Strict reverse covariance under a nonatomic probability law

This is the measure-theoretic comparison used in the DFL GCI coefficient
argument.  The pointwise reversal is stated almost everywhere relative to
the *actual* probability measure, so applications must still construct the
law and prove monotonicity of the weak solution on its support.
-/

namespace DFL.Probability

open MeasureTheory

noncomputable section

/-- If a response is strictly opposite to the coordinate about its mean,
then its covariance with that coordinate is strictly negative. -/
theorem strict_reverse_covariance
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    (h : ℝ → ℝ)
    (hx : Integrable (fun x : ℝ => x) μ)
    (hh : Integrable h μ)
    (hxh : Integrable (fun x : ℝ => x * h x) μ)
    (hreversal : ∀ᵐ x ∂μ,
      x ≠ ∫ y, y ∂μ →
        0 < ((∫ y, y ∂μ) - x) * (h x - h (∫ y, y ∂μ))) :
    (∫ x, x * h x ∂μ) <
      (∫ x, x ∂μ) * (∫ x, h x ∂μ) := by
  let m : ℝ := ∫ x, x ∂μ
  let F : ℝ → ℝ := fun x => (m - x) * (h x - h m)
  have hi₁ : Integrable (fun x : ℝ => m * h x) μ := hh.const_mul m
  have hi₂ : Integrable (fun x : ℝ => x * h x) μ := hxh
  have hi₃ : Integrable (fun _ : ℝ => m * h m) μ := integrable_const _
  have hi₄ : Integrable (fun x : ℝ => x * h m) μ := hx.mul_const (h m)
  have hiF : Integrable F μ := by
    convert ((hi₁.sub hi₂).sub hi₃).add hi₄ using 1
    ext x
    dsimp [F]
    ring
  have hae_pos : ∀ᵐ x ∂μ, 0 < F x := by
    filter_upwards [μ.ae_ne m, hreversal] with x hxne hrev
    exact hrev hxne
  have hae_nonneg : 0 ≤ᵐ[μ] F := hae_pos.mono (fun _ hxpos => le_of_lt hxpos)
  have hsupport_pos : 0 < μ (Function.support F) := by
    by_contra h
    have hzero : μ (Function.support F) = 0 := le_antisymm (le_of_not_gt h) bot_le
    have hae_zero : ∀ᵐ x ∂μ, F x = 0 := by
      simpa only [ae_iff, Function.mem_support, not_not] using hzero
    obtain ⟨x, hxpos, hxzero⟩ := (hae_pos.and hae_zero).exists
    exact (ne_of_gt hxpos) hxzero
  have hIntpos : 0 < ∫ x, F x ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hae_nonneg hiF).2 hsupport_pos
  have hFexpr : F = fun x => m * h x - x * h x - m * h m + x * h m := by
    funext x
    dsimp [F]
    ring
  have hIntEq : (∫ x, F x ∂μ) =
      m * (∫ x, h x ∂μ) - (∫ x, x * h x ∂μ) := by
    rw [hFexpr]
    have hsum :
        (∫ x, m * h x - x * h x - m * h m + x * h m ∂μ) =
          (∫ x, m * h x - x * h x - m * h m ∂μ) +
            (∫ x, x * h m ∂μ) := by
      simpa only [Pi.sub_apply] using
        (integral_add ((hi₁.sub hi₂).sub hi₃) hi₄)
    have hsub₁ :
        (∫ x, m * h x - x * h x - m * h m ∂μ) =
          (∫ x, m * h x - x * h x ∂μ) -
            (∫ _ : ℝ, m * h m ∂μ) := by
      simpa only [Pi.sub_apply] using
        (integral_sub (hi₁.sub hi₂) hi₃)
    have hsub₂ :
        (∫ x, m * h x - x * h x ∂μ) =
          (∫ x, m * h x ∂μ) - (∫ x, x * h x ∂μ) := by
      simpa only [Pi.sub_apply] using (integral_sub hi₁ hi₂)
    rw [hsum, hsub₁, hsub₂, integral_const_mul, integral_const, integral_mul_const]
    simp only [probReal_univ, one_smul]
    dsimp [m]
    ring
  rw [hIntEq] at hIntpos
  exact sub_pos.mp hIntpos

/-- A convenient application form: strict decrease on the support interval
implies strict negative covariance. The mean must be in the same interval. -/
theorem strict_reverse_covariance_of_strictAntiOn
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    (h : ℝ → ℝ) (S : Set ℝ)
    (hx : Integrable (fun x : ℝ => x) μ)
    (hh : Integrable h μ)
    (hxh : Integrable (fun x : ℝ => x * h x) μ)
    (hS : ∀ᵐ x ∂μ, x ∈ S)
    (hm : (∫ x, x ∂μ) ∈ S)
    (hanti : StrictAntiOn h S) :
    (∫ x, x * h x ∂μ) <
      (∫ x, x ∂μ) * (∫ x, h x ∂μ) := by
  apply strict_reverse_covariance μ h hx hh hxh
  filter_upwards [hS] with x hxS hxne
  rcases lt_or_gt_of_ne hxne with hlt | hgt
  · have hhgt : h (∫ y, y ∂μ) < h x := hanti hxS hm hlt
    exact mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hhgt)
  · have hhlt : h x < h (∫ y, y ∂μ) := hanti hm hxS hgt
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hgt) (sub_neg.mpr hhlt)

end

end DFL.Probability
