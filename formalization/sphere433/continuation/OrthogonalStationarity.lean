import continuation.CompactPotentialGround

/-! The original constrained Euler equation. An attained Rayleigh bound
on the equilibrium-orthogonal space is stationary against the full form
domain after subtracting the actual zero-ground component of each test. -/
noncomputable section
set_option maxHeartbeats 800000
open InnerProductSpace
open scoped RealInnerProductSpace
namespace DFLSphere
variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L]

/-- Equality in the actual constrained Rayleigh bound implies the complete
weak eigenidentity. No eigenstate or stationarity premise is used. -/
theorem orthogonal_potential_minimizer_weak (J : H →L[ℝ] L) (P : L →L[ℝ] L)
    (hP : P.IsSymmetric) (e u : H) (he : ‖J e‖ = 1)
    (heq : ∀ v : H, potentialForm J P e v = 0) (hu : ⟪J u,J e⟫_ℝ = 0)
    (lam : ℝ) (heqU : potentialForm J P u u = lam*‖J u‖^2)
    (hmin : ∀ v : H, ⟪J v,J e⟫_ℝ = 0 →
      lam*‖J v‖^2 ≤ potentialForm J P v v) :
    ∀ v : H, potentialForm J P u v = lam*⟪J u,J v⟫_ℝ := by
  let ell : H →L[ℝ] ℝ := (innerSL ℝ (J e)).comp J
  let K : Submodule ℝ H := ell.ker
  let JK : K →L[ℝ] L := J.comp K.subtypeL
  have hmem (v : H) : v ∈ K ↔ ⟪J v,J e⟫_ℝ = 0 := by
    change ell v = 0 ↔ _
    simp only [ell,ContinuousLinearMap.comp_apply,innerSL_apply_apply,real_inner_comm (J e)]
  let uK : K := ⟨u,(hmem u).2 hu⟩
  have hw := potentialForm_minimizer_weak JK P hP lam uK heqU
    (fun v => hmin v ((hmem v).1 v.property))
  have hUe : potentialForm J P u e = 0 := by
    have hp : ⟪P (J u),J e⟫_ℝ = ⟪P (J e),J u⟫_ℝ :=
      (hP (J u) (J e)).trans (real_inner_comm _ _)
    have hs : potentialForm J P u e = potentialForm J P e u := by
      simp only [potentialForm,hp,real_inner_comm u e,real_inner_comm (J u) (J e)]
    exact hs.trans (heq u)
  have heinner : ⟪J e,J e⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq,he]
    norm_num
  intro v
  let c := ⟪J v,J e⟫_ℝ
  have hm : v-c • e ∈ K := by
    apply (hmem _).2
    rw [map_sub,map_smul,inner_sub_left,real_inner_smul_left,heinner]
    change c-c*1 = 0
    ring
  have hh := hw ⟨v-c • e,hm⟩
  change potentialForm J P u (v-c • e) = lam*⟪J u,J (v-c • e)⟫_ℝ at hh
  have hsplit : potentialForm J P u (v-c • e) =
      potentialForm J P u v-c*potentialForm J P u e := by
    simp only [potentialForm,map_sub,map_smul,inner_sub_right,real_inner_smul_right]
    ring
  rw [hsplit,hUe,map_sub,map_smul,inner_sub_right,real_inner_smul_right,hu,
    mul_zero,sub_zero] at hh
  simpa only [mul_zero,sub_zero] using hh
end DFLSphere
