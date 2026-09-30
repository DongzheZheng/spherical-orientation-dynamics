import DFLSphere433.CompactFormGround

/-! The original compact-form minimization on the orthogonal complement
of the actual equilibrium ground. Constrained tests are extended to every
full form-domain test by subtracting its genuine ground component. -/
noncomputable section
set_option maxHeartbeats 800000
open InnerProductSpace
open scoped RealInnerProductSpace
namespace DFLSphere
variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L]

omit [CompleteSpace H] [CompleteSpace L] in
private theorem potentialForm_symm (J : H →L[ℝ] L) (P : L →L[ℝ] L)
    (hP : P.IsSymmetric) (u v : H) : potentialForm J P u v = potentialForm J P v u := by
  have hp : ⟪P (J u),J v⟫_ℝ = ⟪P (J v),J u⟫_ℝ :=
    (hP (J u) (J v)).trans (real_inner_comm _ _)
  simp only [potentialForm,hp,real_inner_comm u v,real_inner_comm (J u) (J v)]

omit [CompleteSpace H] [CompleteSpace L] in
private theorem potentialForm_sub_smul_right (J : H →L[ℝ] L) (P : L →L[ℝ] L)
    (u v e : H) (c : ℝ) :
    potentialForm J P u (v-c • e) = potentialForm J P u v-c*potentialForm J P u e := by
  simp only [potentialForm,map_sub,map_smul,inner_sub_right,real_inner_smul_right]
  ring

/-- Actual first positive minimum on the ground-orthogonal closed form
space, derived from compactness and the proved ground properties. The
conclusion is a weak eigenstate against every full-domain test. -/
theorem compact_potential_first_positive_exists
    (J : H →L[ℝ] L) (hJ : IsCompactOperator J)
    (P : L →L[ℝ] L) (hP : P.IsSymmetric)
    (e : H) (he : ‖J e‖ = 1)
    (heq : ∀ v : H, potentialForm J P e v = 0)
    (hnonneg : ∀ v : H, 0 ≤ potentialForm J P v v)
    (hsimple : ∀ u : H, (∀ v : H, potentialForm J P u v = 0) →
      ∃ c : ℝ, J u = c • J e)
    (horth : ∃ v : H, J v ≠ 0 ∧ ⟪J v,J e⟫_ℝ = 0) :
    ∃ (lam : ℝ) (u : H), 0 < lam ∧ ‖J u‖ = 1 ∧ ⟪J u,J e⟫_ℝ = 0 ∧
      (∀ v : H, potentialForm J P u v = lam*⟪J u,J v⟫_ℝ) ∧
      (∀ v : H, ⟪J v,J e⟫_ℝ = 0 → lam*‖J v‖^2 ≤ potentialForm J P v v) := by
  let ell : H →L[ℝ] ℝ := (innerSL ℝ (J e)).comp J
  let K : Submodule ℝ H := ell.ker
  let _ : CompleteSpace K := ell.isClosed_ker.completeSpace_coe
  let JK : K →L[ℝ] L := J.comp K.subtypeL
  have hJK : IsCompactOperator JK := hJ.comp_clm K.subtypeL
  have hmem (v : H) : v ∈ K ↔ ⟪J v,J e⟫_ℝ = 0 := by
    change ell v = 0 ↔ _
    simp only [ell,ContinuousLinearMap.comp_apply,innerSL_apply_apply,real_inner_comm (J e)]
  have hJK0 : ∃ v : K, JK v ≠ 0 := by
    obtain ⟨v,hv,hm⟩ := horth
    exact ⟨⟨v,(hmem v).2 hm⟩,hv⟩
  obtain ⟨lam,u,hu,hweak,hlower⟩ :=
    compact_potential_form_ground_exists JK hJK hJK0 P hP
  let U : H := u
  have hU : ‖J U‖ = 1 := hu
  have hUm : ⟪J U,J e⟫_ℝ = 0 := (hmem U).1 u.property
  have hUe : potentialForm J P U e = 0 :=
    (potentialForm_symm J P hP U e).trans (heq U)
  have heinner : ⟪J e,J e⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq,he]
    norm_num
  have hfull (v : H) : potentialForm J P U v = lam*⟪J U,J v⟫_ℝ := by
    let c : ℝ := ⟪J v,J e⟫_ℝ
    have hm : v-c • e ∈ K := by
      apply (hmem _).2
      rw [map_sub,map_smul,inner_sub_left,real_inner_smul_left,heinner]
      change c-c*1 = 0
      ring
    let vK : K := ⟨v-c • e,hm⟩
    have hw := hweak vK
    change potentialForm J P U (v-c • e) = lam*⟪J U,J (v-c • e)⟫_ℝ at hw
    rw [potentialForm_sub_smul_right,hUe,map_sub,map_smul,inner_sub_right,
      real_inner_smul_right,hUm,mul_zero,sub_zero] at hw
    simpa only [mul_zero,sub_zero] using hw
  have hlam : 0 ≤ lam := by
    have hh := hfull U
    rw [real_inner_self_eq_norm_sq,hU] at hh
    norm_num at hh
    exact hh ▸ hnonneg U
  have hlam0 : lam ≠ 0 := by
    intro hz
    obtain ⟨c,hc⟩ := hsimple U (fun v => by simpa only [hz,zero_mul] using hfull v)
    have hc0 : c = 0 := by
      rw [hc,real_inner_smul_left,heinner,mul_one] at hUm
      exact hUm
    rw [hc,hc0,zero_smul,norm_zero] at hU
    norm_num at hU
  refine ⟨lam,U,lt_of_le_of_ne hlam hlam0.symm,hU,hUm,hfull,?_⟩
  intro v hv
  exact hlower ⟨v,(hmem v).2 hv⟩

end DFLSphere
