import DifferentialGeometry.Analysis.Spectral.Scalar.Compactness
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.MeasureTheory.Function.Holder

/-! True lowest-value attainment for a compact form embedding and a bounded
self-adjoint zeroth-order operator. This is the shifted Lax--Milgram / compact
positive-resolvent argument used for the manuscript's fixed form domain. -/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace DFLSphere

variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L]

/-- Original gradient-plus-potential form, when the H norm is mass plus energy. -/
def potentialForm (J : H →L[ℝ] L) (P : L →L[ℝ] L) (u v : H) : ℝ :=
  ⟪u,v⟫_ℝ - ⟪J u,J v⟫_ℝ + ⟪P (J u),J v⟫_ℝ

private def shiftedFormOperator (J : H →L[ℝ] L) (P : L →L[ℝ] L) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H + J.adjoint.comp
    ((P + ‖P‖ • ContinuousLinearMap.id ℝ L).comp J)

private def shiftedPotentialForm (J : H →L[ℝ] L) (P : L →L[ℝ] L) : H →L[ℝ] H →L[ℝ] ℝ :=
  (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).comp (shiftedFormOperator J P)

private theorem shiftedPotentialForm_apply (J : H →L[ℝ] L) (P : L →L[ℝ] L) (u v : H) :
    shiftedPotentialForm J P u v = ⟪u,v⟫_ℝ + ⟪P (J u),J v⟫_ℝ + ‖P‖*⟪J u,J v⟫_ℝ := by
  unfold shiftedPotentialForm shiftedFormOperator
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    real_inner_smul_left]
  ring

private theorem shiftedPotentialForm_symm (J : H →L[ℝ] L) (P : L →L[ℝ] L)
    (hP : P.IsSymmetric) (u v : H) :
    shiftedPotentialForm J P u v = shiftedPotentialForm J P v u := by
  rw [shiftedPotentialForm_apply, shiftedPotentialForm_apply]
  have hp : ⟪P (J u),J v⟫_ℝ = ⟪P (J v),J u⟫_ℝ := (hP (J u) (J v)).trans (real_inner_comm _ _)
  rw [hp]
  congr 2
  · exact real_inner_comm _ _
  · exact real_inner_comm _ _

omit [CompleteSpace L] in
private theorem operator_inner_bound (P : L →L[ℝ] L) (x : L) :
    |⟪P x,x⟫_ℝ| ≤ ‖P‖*‖x‖^2 := by
  calc
    _ ≤ ‖P x‖*‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖P‖*‖x‖)*‖x‖ := mul_le_mul_of_nonneg_right (P.le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

private theorem shiftedPotentialForm_lower (J : H →L[ℝ] L) (P : L →L[ℝ] L) (u : H) :
    ‖u‖^2 ≤ shiftedPotentialForm J P u u := by
  rw [shiftedPotentialForm_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hh := (abs_le.mp (operator_inner_bound P (J u))).1
  linarith

private theorem shiftedPotentialForm_coercive (J : H →L[ℝ] L) (P : L →L[ℝ] L) :
    IsCoercive (shiftedPotentialForm J P) := by
  refine ⟨1,zero_lt_one,?_⟩
  intro u
  have hh := shiftedPotentialForm_lower J P u
  nlinarith

private theorem positive_compact_norm_eigenvector [Nontrivial L]
    (S : L →L[ℝ] L) (hS : IsCompactOperator S) (hs : S.IsSymmetric)
    (hn : ∀ x : L, 0 ≤ ⟪S x,x⟫_ℝ) (h0 : S ≠ 0) :
    ∃ w : L, ‖w‖ = 1 ∧ S w = ‖S‖ • w := by
  have hnorm : 0 < ‖S‖ := norm_pos_iff.mpr h0
  have hspec : ‖S‖ ∈ spectrum ℝ S := by
    by_contra hnot
    have hres : ‖S‖ ∈ resolventSet ℝ S := by simpa only [spectrum, Set.mem_compl_iff, not_not] using hnot
    obtain ⟨ε,hε,hbound⟩ := S.rayleighQuotient_le_of_norm_mem_resolventSet hres
    have hq : ∀ x : L, 0 ≤ S.rayleighQuotient x := by
      intro x
      simp only [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real]
      exact div_nonneg (hn x) (sq_nonneg _)
    have hh : ‖S‖ ≤ ‖S‖-ε := by
      calc
        ‖S‖ = ⨆ x, |S.rayleighQuotient x| := S.norm_eq_iSup_rayleighQuotient hs
        _ ≤ ‖S‖-ε := by
          apply ciSup_le
          intro x
          rw [abs_of_nonneg (hq x)]
          exact hbound x
    linarith
  have heig := (hS.hasEigenvalue_iff_mem_spectrum (ne_of_gt hnorm)).2 hspec
  obtain ⟨w,hw,hw0⟩ := heig.exists_hasEigenvector
  have hwe : S w = ‖S‖ • w := by
    have hh := Module.End.mem_genEigenspace_one.mp hw
    change S w = ‖S‖ • w at hh
    exact hh
  refine ⟨‖w‖⁻¹ • w,?_,?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hw0))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)
  · rw [map_smul, hwe]
    module

omit [CompleteSpace H] in
private theorem nonnegative_bilinear_cauchy (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hs : ∀ u v : H, B u v = B v u) (hn : ∀ u : H, 0 ≤ B u u)
    (u v : H) : (B u v)^2 ≤ B u u*B v v := by
  have hp (t : ℝ) : 0 ≤ B u u+2*t*B u v+t^2*B v v := by
    have hh := hn (u+t • v)
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hs v u] at hh
    convert hh using 1; ring
  by_cases hv : B v v = 0
  · have hb : B u v = 0 := by
      by_contra hb
      have hh := hp (-(B u u+1)/(2*B u v))
      rw [hv] at hh
      have hid : B u u+2*(-(B u u+1)/(2*B u v))*B u v+
          (-(B u u+1)/(2*B u v))^2*0 = -1 := by field_simp; ring
      rw [hid] at hh
      norm_num at hh
    norm_num [hb, hv]
  · have hvp : 0 < B v v := lt_of_le_of_ne (hn v) (Ne.symm hv)
    have hh := hp (-B u v/B v v)
    have hid : B u u+2*(-B u v/B v v)*B u v+(-B u v/B v v)^2*B v v =
        (B u u*B v v-(B u v)^2)/B v v := by field_simp; ring
    rw [hid] at hh
    have hh0 := (div_nonneg_iff.mp hh).resolve_right (by intro h; linarith)
    exact sub_nonneg.mp hh0.1

/-- A true minimum in the full form space, derived from compact embedding
and a bounded symmetric potential; no minimum or eigenfunction premise. -/
theorem compact_potential_form_ground_exists (J : H →L[ℝ] L)
    (hJ : IsCompactOperator J) (hJ0 : ∃ v : H, J v ≠ 0)
    (P : L →L[ℝ] L) (hP : P.IsSymmetric) :
    ∃ (lam : ℝ) (u : H), ‖J u‖ = 1 ∧
      (∀ v : H, potentialForm J P u v = lam*⟪J u,J v⟫_ℝ) ∧
      (∀ v : H, lam*‖J v‖^2 ≤ potentialForm J P v v) := by
  let B := shiftedPotentialForm J P
  have hs : ∀ u v : H, B u v = B v u := shiftedPotentialForm_symm J P hP
  have hco : IsCoercive B := shiftedPotentialForm_coercive J P
  let T := hco.continuousLinearEquivOfBilin
  let R : L →L[ℝ] H := T.symm.toContinuousLinearMap.comp J.adjoint
  let S : L →L[ℝ] L := J.comp R
  have hR (f : L) (v : H) : B (R f) v = ⟪f,J v⟫_ℝ := by
    have hh := IsCoercive.continuousLinearEquivOfBilin_apply hco (R f) v
    have hTR : T (R f) = J.adjoint f := by
      dsimp [R]; exact T.apply_symm_apply _
    change ⟪T (R f),v⟫_ℝ = B (R f) v at hh
    rw [hTR, ContinuousLinearMap.adjoint_inner_left] at hh
    exact hh.symm
  have hScompact : IsCompactOperator S := hJ.comp_clm R
  have hSsymm : S.IsSymmetric := by
    intro f g
    have hf := hR f (R g)
    have hg := hR g (R f)
    change ⟪J (R f),g⟫_ℝ = ⟪f,J (R g)⟫_ℝ
    rw [← hf, hs]
    exact (hg.trans (real_inner_comm _ _)).symm
  have hSnonneg (f : L) : 0 ≤ ⟪S f,f⟫_ℝ := by
    have hh := shiftedPotentialForm_lower J P (R f)
    have he := hR f (R f)
    change ‖R f‖^2 ≤ B (R f) (R f) at hh
    change 0 ≤ ⟪J (R f),f⟫_ℝ
    calc
      0 ≤ B (R f) (R f) := (sq_nonneg _).trans hh
      _ = ⟪f,J (R f)⟫_ℝ := he
      _ = ⟪J (R f),f⟫_ℝ := real_inner_comm _ _
  obtain ⟨v0,hv0⟩ := hJ0
  have hS0 : S ≠ 0 := by
    intro hz
    have he := hR (J v0) (R (J v0))
    have hjR : J (R (J v0)) = 0 := by change S (J v0) = 0; rw [hz]; rfl
    rw [hjR, inner_zero_right] at he
    have hl := shiftedPotentialForm_lower J P (R (J v0))
    change ‖R (J v0)‖^2 ≤ B (R (J v0)) (R (J v0)) at hl
    rw [he] at hl
    have hR0 : R (J v0) = 0 := by
      have hn : ‖R (J v0)‖ = 0 := by nlinarith [norm_nonneg (R (J v0))]
      exact norm_eq_zero.mp hn
    have hev := hR (J v0) v0
    rw [hR0] at hev
    have hb0 : B 0 v0 = 0 := by simp
    rw [hb0, real_inner_self_eq_norm_sq] at hev
    have hn : ‖J v0‖ = 0 := by nlinarith [norm_nonneg (J v0)]
    exact hv0 (norm_eq_zero.mp hn)
  let : Nontrivial L := ⟨⟨J v0,0,hv0⟩⟩
  obtain ⟨w,hw,hwe⟩ := positive_compact_norm_eigenvector S hScompact hSsymm hSnonneg hS0
  have hμ : 0 < ‖S‖ := norm_pos_iff.mpr hS0
  let u : H := ‖S‖⁻¹ • R w
  have hJu : J u = w := by
    dsimp [u]
    rw [map_smul]
    change ‖S‖⁻¹ • S w = w
    rw [hwe, smul_smul, inv_mul_cancel₀ (ne_of_gt hμ), one_smul]
  have hBu (v : H) : B u v = ‖S‖⁻¹*⟪J u,J v⟫_ℝ := by
    rw [hJu]
    change B (‖S‖⁻¹ • R w) v = _
    rw [map_smul, smul_apply, smul_eq_mul, hR w v]
  have hmass_lower (v : H) : ‖J v‖^2 ≤ ‖S‖*B v v := by
    have hcross := nonnegative_bilinear_cauchy B hs
      (fun q => (sq_nonneg ‖q‖).trans (shiftedPotentialForm_lower J P q)) (R (J v)) v
    rw [hR (J v) v, real_inner_self_eq_norm_sq] at hcross
    have hBr := hR (J v) (R (J v))
    have hbound : B (R (J v)) (R (J v)) ≤ ‖S‖*‖J v‖^2 := by
      rw [hBr]
      change ⟪J v,S (J v)⟫_ℝ ≤ ‖S‖*‖J v‖^2
      have hh := (abs_le.mp (operator_inner_bound S (J v))).2
      simpa only [real_inner_comm] using hh
    have hBv : 0 ≤ B v v := (sq_nonneg _).trans (shiftedPotentialForm_lower J P v)
    have hh := mul_le_mul_of_nonneg_right hbound hBv
    by_cases hv : J v = 0
    · simpa only [hv, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
        mul_nonneg hμ.le hBv
    · have hp : 0 < ‖J v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
      nlinarith
  refine ⟨‖S‖⁻¹-(‖P‖+1),u,by rw [hJu]; exact hw,?_,?_⟩
  · intro v
    have hh := hBu v
    change shiftedPotentialForm J P u v = _ at hh
    rw [shiftedPotentialForm_apply] at hh
    unfold potentialForm
    linarith
  · intro v
    have hh := hmass_lower v
    have hdiv : ‖S‖⁻¹*‖J v‖^2 ≤ B v v := by
      apply (inv_mul_le_iff₀ hμ).2
      simpa only [mul_comm] using hh
    change ‖S‖⁻¹*‖J v‖^2 ≤ shiftedPotentialForm J P v v at hdiv
    rw [shiftedPotentialForm_apply] at hdiv
    simp only [real_inner_self_eq_norm_sq] at hdiv
    unfold potentialForm
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    nlinarith

end DFLSphere
