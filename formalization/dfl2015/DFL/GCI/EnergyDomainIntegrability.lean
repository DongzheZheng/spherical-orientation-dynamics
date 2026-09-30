import DFL.GCI.AngularMomentAll
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finiteness of the original form on its represented energy domain

The original domain controls `u'` and `u / sin`, where
`u = sin^((n-2)/2) g`.  This file verifies the actual bilinear form,
source, and coefficient integrals for all admissible representatives.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def angularIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.uIoc (0 : ℝ) Real.pi)

def singularRepresentative (s : AngularState) (θ : ℝ) : ℝ :=
  momentPrimitive s θ / Real.sin θ

theorem scaledDerivative_memLp_two (n : ℕ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    MemLp s.scaledDerivative 2 angularIntervalMeasure := by
  simpa only [angularIntervalMeasure, Set.uIoc_of_le Real.pi_pos.le] using
    (memLp_two_iff_integrable_sq hs.1.1.aestronglyMeasurable).2 hs.2.1.1

theorem singularRepresentative_eq (n : ℕ) (s : AngularState)
    (hs : AngularEnergyDomain n s) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    singularRepresentative s θ =
      Real.rpow (Real.sin θ) (halfPower n - 1) * s.g θ := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hp : Real.rpow (Real.sin θ) (halfPower n) =
      Real.rpow (Real.sin θ) (halfPower n - 1) * Real.sin θ := by
    have ha : halfPower n - 1 + 1 = halfPower n := by ring
    rw [← ha]
    simpa using Real.rpow_add_one hsin.ne' (halfPower n - 1)
  unfold singularRepresentative
  rw [← moment_reconstruction n s hs θ ⟨hθ.1.le, hθ.2.le⟩]
  rw [hp]
  field_simp [hsin.ne']

theorem singularRepresentative_memLp_two
    (n : ℕ) (hn : 3 ≤ n) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    MemLp (singularRepresentative s) 2 angularIntervalMeasure := by
  have hu : AEStronglyMeasurable (momentPrimitive s) angularIntervalMeasure := by
    exact ((momentPrimitive_continuousOn n s hs).mono
      (by intro x hx; rw [Set.uIoc_of_le Real.pi_pos.le] at hx
          exact ⟨hx.1.le, hx.2⟩)).aestronglyMeasurable
      measurableSet_uIoc
  have hb : AEStronglyMeasurable (singularRepresentative s) angularIntervalMeasure := by
    exact (hu.aemeasurable.div Real.continuous_sin.measurable.aemeasurable).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hb).2
  have hnr : (n : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hi := hs.2.2.2.2.1
  have hdiv := hi.div_const (((n : ℝ) - 2) ^ 2)
  have hdiv' : Integrable
      (fun θ => (((n : ℝ) - 2) * Real.rpow (Real.sin θ)
        (((n : ℝ) - 4) / 2) * s.g θ) ^ 2 / ((n : ℝ) - 2) ^ 2)
      angularIntervalMeasure := by
    simpa only [angularIntervalMeasure, Set.uIoc_of_le Real.pi_pos.le] using hdiv
  apply hdiv'.congr
  filter_upwards [moment_ae_interior] with θ hθ
  rw [singularRepresentative_eq n s hs θ hθ]
  have he : ((n : ℝ) - 4) / 2 = halfPower n - 1 := by
    unfold halfPower
    ring
  rw [he]
  field_simp [hnr]

theorem formIntegrand_scaled_density
    (n : ℕ) (s v : AngularState)
    (hs : AngularEnergyDomain n s) (hv : AngularEnergyDomain n v)
    (r θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    formIntegrand n r s v θ =
      Real.exp (r * Real.cos θ) *
        ((s.scaledDerivative θ - halfPower n * Real.cos θ * singularRepresentative s θ) *
          (v.scaledDerivative θ - halfPower n * Real.cos θ * singularRepresentative v θ) +
          ((n : ℝ) - 2) * singularRepresentative s θ * singularRepresentative v θ) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hb : Real.rpow (Real.sin θ) (halfPower n - 1) * Real.sin θ =
      Real.rpow (Real.sin θ) (halfPower n) := by
    simpa using (Real.rpow_add_one hsin.ne' (halfPower n - 1)).symm
  have hpow : Real.rpow (Real.sin θ) ((n : ℝ) - 2) =
      Real.rpow (Real.sin θ) (halfPower n) ^ 2 := by
    have hsum : halfPower n + halfPower n = (n : ℝ) - 2 := by
      unfold halfPower
      ring
    rw [← hsum]
    change (Real.sin θ) ^ (halfPower n + halfPower n) =
      ((Real.sin θ) ^ halfPower n) ^ 2
    rw [Real.rpow_add hsin]
    ring
  have hbne : Real.rpow (Real.sin θ) (halfPower n - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hsin _).ne'
  rw [singularRepresentative_eq n s hs θ hθ,
    singularRepresentative_eq n v hv θ hθ]
  unfold formIntegrand angularWeight angularPotential angularDerivative
  rw [hpow]
  have hpoweq : Real.rpow (Real.sin θ) (halfPower n) =
      Real.rpow (Real.sin θ) (halfPower n - 1) * Real.sin θ := hb.symm
  rw [hpoweq]
  field_simp [hsin.ne', hbne]

private theorem intervalIntegrable_of_L2_product
    {f g : ℝ → ℝ} (hf : MemLp f 2 angularIntervalMeasure)
    (hg : MemLp g 2 angularIntervalMeasure) :
    IntervalIntegrable (fun θ => f θ * g θ) volume (0 : ℝ) Real.pi := by
  exact intervalIntegrable_iff.mpr (hf.integrable_mul hg)

/-- The full original bilinear form is finite for every pair in its
represented source domain, including the singular three-dimensional case. -/
theorem formIntegrand_intervalIntegrable_of_energyDomain
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (s v : AngularState)
    (hs : AngularEnergyDomain n s) (hv : AngularEnergyDomain n v) :
    IntervalIntegrable (formIntegrand n r s v) volume (0 : ℝ) Real.pi := by
  have hq := scaledDerivative_memLp_two n s hs
  have hvq := scaledDerivative_memLp_two n v hv
  have hqq := intervalIntegrable_of_L2_product hq hvq
  have hw : Continuous (fun θ : ℝ => Real.exp (r * Real.cos θ)) := by fun_prop
  by_cases hn2 : n = 2
  · subst n
    have hi := hqq.continuousOn_mul hw.continuousOn
    apply hi.congr
    intro θ _
    norm_num [formIntegrand, angularWeight, angularPotential,
      angularDerivative, halfPower]
  · have hn3 : 3 ≤ n := by omega
    have hb := singularRepresentative_memLp_two n hn3 s hs
    have hvb := singularRepresentative_memLp_two n hn3 v hv
    have hqb := intervalIntegrable_of_L2_product hq hvb
    have hbq := intervalIntegrable_of_L2_product hb hvq
    have hbb := intervalIntegrable_of_L2_product hb hvb
    have h0 := hqq.continuousOn_mul hw.continuousOn
    have h1 := hqb.continuousOn_mul
      (by fun_prop : Continuous (fun θ : ℝ => halfPower n *
        Real.exp (r * Real.cos θ) * Real.cos θ)).continuousOn
    have h2 := hbq.continuousOn_mul
      (by fun_prop : Continuous (fun θ : ℝ => halfPower n *
        Real.exp (r * Real.cos θ) * Real.cos θ)).continuousOn
    have h3 := hbb.continuousOn_mul
      (by fun_prop : Continuous (fun θ : ℝ => Real.exp (r * Real.cos θ) *
        ((halfPower n) ^ 2 * (Real.cos θ) ^ 2 + ((n : ℝ) - 2)))).continuousOn
    apply (((h0.sub h1).sub h2).add h3).congr_ae
    filter_upwards [moment_ae_interior] with θ hθ
    rw [formIntegrand_scaled_density n s v hs hv r θ hθ]
    ring

/-- A finite continuous proxy for the original hydrodynamic denominator. -/
theorem denominator_density_eq_scaled
    (n : ℕ) (s : AngularState) (hs : AngularEnergyDomain n s)
    (r θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    s.g θ * Real.exp (r * Real.cos θ) *
      Real.rpow (Real.sin θ) ((n : ℝ) - 1) =
    momentDenominatorWeight n r θ * momentPrimitive s θ := by
  have hrec := moment_reconstruction n s hs θ ⟨hθ.1.le, hθ.2.le⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hsum : halfPower n + 1 + halfPower n = (n : ℝ) - 1 := by
    unfold halfPower
    ring
  have hpow : Real.rpow (Real.sin θ) ((n : ℝ) - 1) =
      Real.rpow (Real.sin θ) (halfPower n + 1) *
      Real.rpow (Real.sin θ) (halfPower n) := by
    rw [← hsum]
    exact Real.rpow_add hsin _ _
  rw [← hrec, hpow]
  unfold momentDenominatorWeight
  ring

theorem denominator_intervalIntegrable_of_energyDomain
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    IntervalIntegrable (fun θ => s.g θ * Real.exp (r * Real.cos θ) *
      Real.rpow (Real.sin θ) ((n : ℝ) - 1)) volume (0 : ℝ) Real.pi := by
  have hp : 0 ≤ halfPower n + 1 := by
    unfold halfPower
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hw : Continuous (momentDenominatorWeight n r) := by
    unfold momentDenominatorWeight
    exact (by fun_prop : Continuous (fun θ : ℝ => Real.exp (r * Real.cos θ))).mul
      ((Real.continuous_rpow_const hp).comp Real.continuous_sin)
  have hi : IntervalIntegrable
      (fun θ => momentDenominatorWeight n r θ * momentPrimitive s θ)
      volume (0 : ℝ) Real.pi := (hw.continuousOn.mul
    (momentPrimitive_continuousOn n s hs)).intervalIntegrable_of_Icc Real.pi_pos.le
  apply hi.congr_ae
  filter_upwards [moment_ae_interior] with θ hθ
  exact (denominator_density_eq_scaled n s hs r θ hθ).symm

theorem source_intervalIntegrable_of_energyDomain
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    IntervalIntegrable (fun θ => angularWeight n r θ * Real.sin θ * s.g θ)
      volume (0 : ℝ) Real.pi := by
  have hi := denominator_intervalIntegrable_of_energyDomain n hn r s hs
  apply hi.congr_ae
  filter_upwards [moment_ae_interior] with θ hθ
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  have hp : (n : ℝ) - 2 + 1 = (n : ℝ) - 1 := by ring
  unfold angularWeight
  have hpow : Real.rpow (Real.sin θ) ((n : ℝ) - 1) =
      Real.rpow (Real.sin θ) ((n : ℝ) - 2) * Real.sin θ := by
    rw [← hp]
    exact Real.rpow_add_one hsin.ne' _
  rw [hpow]
  ring

theorem numerator_intervalIntegrable_of_energyDomain
    (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    IntervalIntegrable (fun θ => Real.cos θ * s.g θ * Real.exp (r * Real.cos θ) *
      Real.rpow (Real.sin θ) ((n : ℝ) - 1)) volume (0 : ℝ) Real.pi := by
  have hi := (denominator_intervalIntegrable_of_energyDomain n hn r s hs).continuousOn_mul
    Real.continuous_cos.continuousOn
  apply hi.congr
  intro θ _
  ring

end

end DFL.GCI
