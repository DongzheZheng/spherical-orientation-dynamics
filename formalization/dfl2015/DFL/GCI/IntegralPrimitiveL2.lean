import DFL.GCI.OriginalTarget
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The actual Dirichlet primitive as a bounded map on angular `L²`.
The interval is fixed to `[0,π]`; all function equalities in `AngularL2`
are Lebesgue almost-everywhere equalities on that physical interval. -/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def angularLebesgue : Measure ℝ := volume.restrict (Set.Ioc 0 Real.pi)

instance : IsFiniteMeasure angularLebesgue := by
  unfold angularLebesgue
  infer_instance

instance : NoAtoms angularLebesgue := by
  unfold angularLebesgue
  infer_instance

abbrev AngularL2 := Lp ℝ 2 angularLebesgue

def l2Primitive (q : AngularL2) (θ : ℝ) : ℝ :=
  ∫ x in Set.Ioc 0 θ, q x ∂angularLebesgue

theorem angularLebesgue_real_univ : angularLebesgue.real Set.univ = Real.pi := by
  simp [angularLebesgue, Measure.real, Real.pi_pos.le]

theorem l2Primitive_continuousOn (q : AngularL2) :
    ContinuousOn (l2Primitive q) (Set.Icc 0 Real.pi) := by
  exact intervalIntegral.continuousOn_primitive
    (((Lp.memLp q).integrable (by norm_num)).integrableOn)

theorem l2Primitive_eq_interval (q : AngularL2) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 Real.pi) :
    l2Primitive q θ = ∫ x in (0 : ℝ)..θ, q x := by
  unfold l2Primitive angularLebesgue
  rw [Measure.restrict_restrict_of_subset
    (by intro x hx; exact ⟨hx.1, hx.2.trans hθ.2⟩)]
  exact (intervalIntegral.integral_of_le hθ.1).symm

theorem l2Primitive_bound (q : AngularL2) (θ : ℝ) :
    ‖l2Primitive q θ‖ ≤ Real.sqrt Real.pi * ‖q‖ := by
  let s := Set.Ioc (0 : ℝ) θ
  let c : AngularL2 := indicatorConstLp (μ := angularLebesgue) (s := s) 2 measurableSet_Ioc (by finiteness) (1 : ℝ)
  have hc : ‖c‖ ≤ Real.sqrt Real.pi := by
    have hsq : ‖c‖ ^ 2 = angularLebesgue.real s := by
      rw [← real_inner_self_eq_norm_sq]
      simpa [c, s] using
        (L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
          (μ := angularLebesgue) (s := s) (t := s) measurableSet_Ioc measurableSet_Ioc)
    have hm : angularLebesgue.real s ≤ Real.pi := by
      rw [← angularLebesgue_real_univ]
      exact measureReal_mono (Set.subset_univ s)
    have hsqrt := Real.sq_sqrt Real.pi_pos.le
    have hsqrtn := Real.sqrt_nonneg Real.pi
    nlinarith [norm_nonneg c]
  calc
    ‖l2Primitive q θ‖ = ‖inner ℝ c q‖ := by
      change ‖l2Primitive q θ‖ = ‖inner ℝ (indicatorConstLp (μ := angularLebesgue) (s := s) 2 measurableSet_Ioc (by finiteness) (1 : ℝ)) q‖
      congr 1
      exact (L2.inner_indicatorConstLp_one (𝕜 := ℝ) (μ := angularLebesgue)
        (s := s) measurableSet_Ioc (by finiteness) q).symm
    _ ≤ ‖c‖ * ‖q‖ := norm_inner_le_norm c q
    _ ≤ Real.sqrt Real.pi * ‖q‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg q)

theorem l2Primitive_memLp (q : AngularL2) :
    MemLp (l2Primitive q) 2 angularLebesgue := by
  refine MemLp.of_bound ?_ (Real.sqrt Real.pi * ‖q‖) (ae_of_all _ (l2Primitive_bound q))
  exact ((l2Primitive_continuousOn q).mono
      (by intro x hx; exact ⟨hx.1.le, hx.2⟩)).aestronglyMeasurable measurableSet_Ioc

def l2PrimitiveLinear : AngularL2 →ₗ[ℝ] AngularL2 where
  toFun q := (l2Primitive_memLp q).toLp (l2Primitive q)
  map_add' q t := by
    apply Lp.ext
    filter_upwards [(l2Primitive_memLp (q+t)).coeFn_toLp,
      (l2Primitive_memLp q).coeFn_toLp, (l2Primitive_memLp t).coeFn_toLp,
      Lp.coeFn_add ((l2Primitive_memLp q).toLp _) ((l2Primitive_memLp t).toLp _)]
      with θ hsum hq ht hright
    rw [hsum, hright]
    simp only [Pi.add_apply, hq, ht]
    unfold l2Primitive
    rw [← integral_add
      (((Lp.memLp q).integrable (by norm_num)).integrableOn)
      (((Lp.memLp t).integrable (by norm_num)).integrableOn)]
    exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add q t))
  map_smul' a q := by
    apply Lp.ext
    filter_upwards [(l2Primitive_memLp (a • q)).coeFn_toLp,
      (l2Primitive_memLp q).coeFn_toLp,
      Lp.coeFn_smul a ((l2Primitive_memLp q).toLp _)] with θ hleft hq hright
    simp only [RingHom.id_apply]
    rw [hleft, hright]
    simp only [Pi.smul_apply, smul_eq_mul, hq]
    unfold l2Primitive
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul a q)] with x hx
    simpa only [Pi.smul_apply, smul_eq_mul] using hx

theorem l2PrimitiveLinear_bound (q : AngularL2) :
    ‖l2PrimitiveLinear q‖ ≤ Real.pi * ‖q‖ := by
  have h := Lp.norm_le_of_ae_bound
    (f := l2PrimitiveLinear q)
    (C := Real.sqrt Real.pi * ‖q‖)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (by
      filter_upwards [(l2Primitive_memLp q).coeFn_toLp] with θ hθ
      change ‖(((l2Primitive_memLp q).toLp (l2Primitive q)) : ℝ → ℝ) θ‖ ≤ _
      rw [hθ]
      exact l2Primitive_bound q θ)
  have hμ : (measureUnivNNReal angularLebesgue : ℝ) = Real.pi := by
    simpa [measureUnivNNReal, measureReal_def] using angularLebesgue_real_univ
  simpa [hμ, Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add Real.pi_pos,
    show (2 : ENNReal).toReal = 2 by norm_num, show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num] using h

/-- The true primitive, with the quantitative `‖Pq‖₂ ≤ π‖q‖₂` bound. -/
def l2PrimitiveCLM : AngularL2 →L[ℝ] AngularL2 :=
  l2PrimitiveLinear.mkContinuous Real.pi l2PrimitiveLinear_bound

theorem l2PrimitiveCLM_ae (q : AngularL2) :
    (l2PrimitiveCLM q : ℝ → ℝ) =ᵐ[angularLebesgue] l2Primitive q :=
  (l2Primitive_memLp q).coeFn_toLp

end
end DFL.GCI
