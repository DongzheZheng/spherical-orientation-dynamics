import DifferentialGeometry.Geometry.Metric.Sphere.Polar.PartialDiffeomorphism
import DifferentialGeometry.Bundle.PartialMfderiv.Composition
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus

/-! Actual differential and round metric in the original polar coordinates.
No metric or separated energy identity is assumed. The pointwise formula is
valid even at degenerate polar angles; its positive warped metric restriction
belongs on the open interval (0, pi), rather than on the whole real line. -/

noncomputable section
open Bundle Manifold Metric Module Set
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator

namespace DFLPolarRound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 2)]

def directionAmbient (p : sphere (0 : E) 1) (w : PolarDir p) : E :=
  ((w : (ℝ ∙ (p : E))ᗮ) : E)

private theorem directionAmbient_smooth (p : sphere (0 : E) 1) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (directionAmbient p) :=
  (ℝ ∙ (p : E))ᗮ.subtypeL.contDiff.contMDiff.comp
    (contMDiff_coe_sphere (E := (ℝ ∙ (p : E))ᗮ) (n := n))

private theorem directionAmbient_derivative (p : sphere (0 : E) 1) (w : PolarDir p)
    (v : TangentSpace (𝓡 n) w) :
    mvfderiv (𝓡 n) (directionAmbient p) w v =
      ((dIncl (n := n) w v : (ℝ ∙ (p : E))ᗮ) : E) := by
  let K := (ℝ ∙ (p : E))ᗮ
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, K) ((↑) : PolarDir p → K) w :=
    contMDiff_coe_sphere.contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hL : MDifferentiableAt 𝓘(ℝ, K) 𝓘(ℝ, E) K.subtypeL (w : K) :=
    K.subtypeL.contDiff.contMDiff.contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have he := hL.mvfderiv_comp_apply hι v
  have hLK : mvfderiv 𝓘(ℝ, K) K.subtypeL (w : K) = K.subtypeL := by
    simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    with_unfolding_all rfl
  rw [hLK] at he
  with_unfolding_all exact he

private def polarAmbient (p : sphere (0 : E) 1) (q : ℝ × PolarDir p) : E :=
  Real.cos q.1 • (p : E) + Real.sin q.1 • directionAmbient p q.2

/-- The existing true polar partial diffeomorphism has the exact original
ambient parametrization. -/
theorem spherePolarPD_ambient (p : sphere (0 : E) 1) (q : ℝ × PolarDir p) :
    (spherePolarPD (n := n) p q : E) =
      Real.cos q.1 • (p : E) + Real.sin q.1 • directionAmbient p q.2 := rfl

private theorem polarAmbient_smooth (p : sphere (0 : E) 1) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) ∞ (polarAmbient p) :=
  ((Real.contDiff_cos.contMDiff.comp contMDiff_fst).smul contMDiff_const).add
    ((Real.contDiff_sin.contMDiff.comp contMDiff_fst).smul
      ((directionAmbient_smooth p).comp contMDiff_snd))

/-- Although its inverse exists only away from the poles, the actual polar
parametrization itself is globally smooth. -/
theorem spherePolarPD_smooth (p : sphere (0 : E) 1) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ (spherePolarPD (n := n) p) := by
  exact ContMDiff.codRestrict_sphere (polarAmbient_smooth p)
    (fun q => (spherePolarPD (n := n) p q).property)

private theorem polar_cos_derivative (p : sphere (0 : E) 1) (q : ℝ × PolarDir p)
    (v : ℝ × TangentSpace (𝓡 n) q.2) :
    mvfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (fun a : ℝ × PolarDir p => Real.cos a.1) q v =
      -Real.sin q.1 * v.1 := by
  have hf : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) Prod.fst q :=
    contMDiff_fst.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hg : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.cos q.1 :=
    Real.contDiff_cos.contMDiff.contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hc := hg.mvfderiv_comp_apply hf v
  rw [mfderiv_fst] at hc
  change mvfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (fun a : ℝ × PolarDir p => Real.cos a.1) q v =
    mvfderiv 𝓘(ℝ, ℝ) Real.cos q.1 v.1 at hc
  have hL : mvfderiv 𝓘(ℝ, ℝ) Real.cos q.1 =
      (1 : ℝ →L[ℝ] ℝ).smulRight (-Real.sin q.1) := by
    simp only [mvfderiv, mfderiv_eq_fderiv,
      (Real.hasDerivAt_cos q.1).hasFDerivAt.fderiv]
    with_unfolding_all rfl
  calc
    _ = mvfderiv 𝓘(ℝ, ℝ) Real.cos q.1 v.1 := hc
    _ = -Real.sin q.1 * v.1 := by
      have he := congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) q.1 →L[ℝ] ℝ => L v.1) hL
      exact he.trans (by change v.1 * -Real.sin q.1 = _; ring)

private theorem polar_sin_derivative (p : sphere (0 : E) 1) (q : ℝ × PolarDir p)
    (v : ℝ × TangentSpace (𝓡 n) q.2) :
    mvfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (fun a : ℝ × PolarDir p => Real.sin a.1) q v =
      Real.cos q.1 * v.1 := by
  have hf : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) Prod.fst q :=
    contMDiff_fst.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hg : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.sin q.1 :=
    Real.contDiff_sin.contMDiff.contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hc := hg.mvfderiv_comp_apply hf v
  rw [mfderiv_fst] at hc
  change mvfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (fun a : ℝ × PolarDir p => Real.sin a.1) q v =
    mvfderiv 𝓘(ℝ, ℝ) Real.sin q.1 v.1 at hc
  have hL : mvfderiv 𝓘(ℝ, ℝ) Real.sin q.1 =
      (1 : ℝ →L[ℝ] ℝ).smulRight (Real.cos q.1) := by
    simp only [mvfderiv, mfderiv_eq_fderiv,
      (Real.hasDerivAt_sin q.1).hasFDerivAt.fderiv]
    with_unfolding_all rfl
  calc
    _ = mvfderiv 𝓘(ℝ, ℝ) Real.sin q.1 v.1 := hc
    _ = Real.cos q.1 * v.1 := by
      have he := congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) q.1 →L[ℝ] ℝ => L v.1) hL
      exact he.trans (by change v.1 * Real.cos q.1 = _; ring)

private theorem polarAmbient_derivative (p : sphere (0 : E) 1) (q : ℝ × PolarDir p)
    (v : ℝ × TangentSpace (𝓡 n) q.2) :
    mvfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (polarAmbient p) q v =
      (-Real.sin q.1 * v.1) • (p : E) + (Real.cos q.1 * v.1) • directionAmbient p q.2 +
        Real.sin q.1 • ((dIncl (n := n) q.2 v.2 : (ℝ ∙ (p : E))ᗮ) : E) := by
  have hcos : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
      (fun a : ℝ × PolarDir p => Real.cos a.1) q :=
    (Real.contDiff_cos.contMDiff.comp contMDiff_fst).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hsin : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
      (fun a : ℝ × PolarDir p => Real.sin a.1) q :=
    (Real.contDiff_sin.contMDiff.comp contMDiff_fst).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hdir : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
      (fun a : ℝ × PolarDir p => directionAmbient p a.2) q :=
    ((directionAmbient_smooth p).comp contMDiff_snd).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hsnd : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n)
      (Prod.snd : ℝ × PolarDir p → PolarDir p) q :=
    (contMDiff_snd : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (Prod.snd : ℝ × PolarDir p → PolarDir p)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hd := ((directionAmbient_smooth (n := n) p).mdifferentiableAt
    (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := q.2)).mvfderiv_comp_apply hsnd v
  rw [mfderiv_snd, directionAmbient_derivative] at hd
  change mvfderiv (𝓘(ℝ, ℝ).prod (𝓡 n))
    (fun a : ℝ × PolarDir p => directionAmbient p a.2) q v =
      ((dIncl (n := n) q.2 v.2 : (ℝ ∙ (p : E))ᗮ) : E) at hd
  unfold polarAmbient
  change mvfderiv (𝓘(ℝ, ℝ).prod (𝓡 n))
    ((fun a : ℝ × PolarDir p => Real.cos a.1) • (fun _ => (p : E)) +
      (fun a : ℝ × PolarDir p => Real.sin a.1) •
        (fun a : ℝ × PolarDir p => directionAmbient p a.2)) q v = _
  rw [mvfderiv_add (hcos.smul mdifferentiableAt_const) (hsin.smul hdir),
    mvfderiv_smul hcos mdifferentiableAt_const, mvfderiv_smul hsin hdir]
  simp only [mvfderiv_const]
  change Real.cos q.1 • (0 : E) +
      mvfderiv (𝓘(ℝ, ℝ).prod (𝓡 n))
        (fun a : ℝ × PolarDir p => Real.cos a.1) q v • (p : E) +
      (Real.sin q.1 • mvfderiv (𝓘(ℝ, ℝ).prod (𝓡 n))
        (fun a : ℝ × PolarDir p => directionAmbient p a.2) q v +
       mvfderiv (𝓘(ℝ, ℝ).prod (𝓡 n))
        (fun a : ℝ × PolarDir p => Real.sin a.1) q v • directionAmbient p q.2) = _
  rw [polar_cos_derivative, polar_sin_derivative, hd]
  simp only [smul_zero, zero_add]
  module

/-- The true tangent differential of the polar sphere parametrization has
one radial component and its actual scaled angular differential. -/
theorem dIncl_spherePolarPD (p : sphere (0 : E) 1) (q : ℝ × PolarDir p)
    (v : ℝ × TangentSpace (𝓡 n) q.2) :
    dIncl (n := n + 1) (spherePolarPD (n := n) p q)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (spherePolarPD (n := n) p) q v) =
      (-Real.sin q.1 * v.1) • (p : E) + (Real.cos q.1 * v.1) • directionAmbient p q.2 +
        Real.sin q.1 • ((dIncl (n := n) q.2 v.2 : (ℝ ∙ (p : E))ᗮ) : E) := by
  have hi : MDifferentiableAt (𝓡 (n + 1)) 𝓘(ℝ, E)
      ((↑) : sphere (0 : E) 1 → E) (spherePolarPD (n := n) p q) :=
    contMDiff_coe_sphere.contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hP := (spherePolarPD_smooth (n := n) p).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := q)
  have hc := hi.mvfderiv_comp_apply hP v
  have he : ((↑) : sphere (0 : E) 1 → E) ∘ spherePolarPD (n := n) p = polarAmbient p := rfl
  rw [he] at hc
  have hkey : dIncl (n := n + 1) (spherePolarPD (n := n) p q)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (spherePolarPD (n := n) p) q v) =
      mvfderiv (𝓡 (n + 1)) ((↑) : sphere (0 : E) 1 → E)
        (spherePolarPD (n := n) p q)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (spherePolarPD (n := n) p) q v) := by
    with_unfolding_all rfl
  rw [hkey, ← hc, polarAmbient_derivative]

private theorem direction_inner_p (p : sphere (0 : E) 1) (w : PolarDir p) :
    ⟪(p : E), directionAmbient p w⟫_ℝ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.1.2

private theorem angularTangent_inner_p (p : sphere (0 : E) 1) (w : PolarDir p)
    (v : TangentSpace (𝓡 n) w) :
    ⟪(p : E), ((dIncl (n := n) w v : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ = 0 := by
  apply Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self (p : E))
  exact (dIncl (n := n) w v).property

private theorem direction_inner_tangent (p : sphere (0 : E) 1) (w : PolarDir p)
    (v : TangentSpace (𝓡 n) w) :
    ⟪directionAmbient p w, ((dIncl (n := n) w v : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ = 0 := by
  change ⟪(w : (ℝ ∙ (p : E))ᗮ), dIncl (n := n) w v⟫_ℝ = 0
  apply Submodule.inner_right_of_mem_orthogonal
    (Submodule.mem_span_singleton_self (w : (ℝ ∙ (p : E))ᗮ))
  rw [← range_mvfderiv_subtypeVal (n := n) w]
  exact ⟨v, rfl⟩

/-- Pulling back the actual round inner product gives exactly the original
polar radial/angular metric expression. No separated metric premise occurs;
the formula also records the angular collapse at either pole. -/
theorem spherePolarPD_round_inner (p : sphere (0 : E) 1) (q : ℝ × PolarDir p)
    (v w : ℝ × TangentSpace (𝓡 n) q.2) :
    (roundMetric (E := E) (n := n + 1)).inner (spherePolarPD (n := n) p q)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (spherePolarPD (n := n) p) q v)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (spherePolarPD (n := n) p) q w) =
      v.1 * w.1 + Real.sin q.1 ^ 2 *
        (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)).inner q.2 v.2 w.2 := by
  have hpp : ⟪(p : E), (p : E)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p]
    norm_num
  have hdd : ⟪directionAmbient p q.2, directionAmbient p q.2⟫_ℝ = 1 := by
    change ⟪(q.2 : (ℝ ∙ (p : E))ᗮ), (q.2 : (ℝ ∙ (p : E))ᗮ)⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere q.2]
    norm_num
  have hpd := direction_inner_p p q.2
  have hdP : ⟪directionAmbient p q.2, (p : E)⟫_ℝ = 0 := by
    rw [real_inner_comm, hpd]
  have hpv := angularTangent_inner_p p q.2 v.2
  have hpw := angularTangent_inner_p p q.2 w.2
  have hvp : ⟪((dIncl (n := n) q.2 v.2 : (ℝ ∙ (p : E))ᗮ) : E), (p : E)⟫_ℝ = 0 := by
    rw [real_inner_comm, hpv]
  have hvd : ⟪((dIncl (n := n) q.2 v.2 : (ℝ ∙ (p : E))ᗮ) : E),
      directionAmbient p q.2⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact direction_inner_tangent (n := n) p q.2 v.2
  have hdw := direction_inner_tangent p q.2 w.2
  rw [roundMetric_inner, dIncl_spherePolarPD, dIncl_spherePolarPD]
  rw [roundMetric_inner (n := n) q.2 v.2 w.2]
  change ⟪(-Real.sin q.1 * v.1) • (p : E) +
      (Real.cos q.1 * v.1) • directionAmbient p q.2 +
        Real.sin q.1 • ((dIncl (n := n) q.2 v.2 : (ℝ ∙ (p : E))ᗮ) : E),
    (-Real.sin q.1 * w.1) • (p : E) + (Real.cos q.1 * w.1) • directionAmbient p q.2 +
      Real.sin q.1 • ((dIncl (n := n) q.2 w.2 : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ =
    v.1 * w.1 + Real.sin q.1 ^ 2 *
      ⟪((dIncl (n := n) q.2 v.2 : (ℝ ∙ (p : E))ᗮ) : E),
        ((dIncl (n := n) q.2 w.2 : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hpp, hdd, hpd, hdP, hpw, hvp, hvd, hdw, mul_zero, mul_one,
    zero_add, add_zero]
  calc
    _ = (Real.sin q.1 ^ 2 + Real.cos q.1 ^ 2) * (v.1 * w.1) +
        Real.sin q.1 ^ 2 *
          ⟪((dIncl (n := n) q.2 v.2 : (ℝ ∙ (p : E))ᗮ) : E),
            ((dIncl (n := n) q.2 w.2 : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

end DFLPolarRound
