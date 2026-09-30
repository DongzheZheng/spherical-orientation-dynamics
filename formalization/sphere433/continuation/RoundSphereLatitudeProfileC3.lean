import continuation.RoundSphereLatitudeProfile
import continuation.EvenSquareFiniteProfile

/-! Actual smooth same-latitude sphere functions have global real C3
profiles through both physical poles. This repeats the original normalized
meridian and closed-set gluing construction, using the next finite-order
Hadamard/Taylor squared-radius profile. No C3 profile is an input. -/
noncomputable section
set_option maxHeartbeats 800000
open Set Filter Function Metric Manifold
open scoped Topology ContDiff Manifold RealInnerProductSpace InnerProductSpace
namespace DFLSphere
open DifferentialGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry
open DFLSpectralCoordinates

private theorem meridian_coordinate_i_C3 (k : ℕ) (i j : Fin (k+3)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    ⟪(EuclideanSpace.single i 1 : RoundAmbient k),
      (meridian k i j hij eps heps r : RoundAmbient k)⟫_ℝ = eps/Real.sqrt (1+r^2) := by
  simp [meridian,meridianAmbient,EuclideanSpace.inner_single_left,hij,div_eq_mul_inv,mul_comm]

private theorem meridian_coordinate_j_C3 (k : ℕ) (i j : Fin (k+3)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    ⟪(EuclideanSpace.single j 1 : RoundAmbient k),
      (meridian k i j hij eps heps r : RoundAmbient k)⟫_ℝ = r/Real.sqrt (1+r^2) := by
  simp [meridian,meridianAmbient,EuclideanSpace.inner_single_left,Ne.symm hij,div_eq_mul_inv,mul_comm]

private theorem roundCoordinate_bounds_C3 (k : ℕ) (x : RoundSphere k) :
    |(roundCoordinate k).toFun x| ≤ 1 := by
  change |⟪(EuclideanSpace.single 0 1 : RoundAmbient k),(x : RoundAmbient k)⟫_ℝ| ≤ 1
  simpa [norm_eq_of_mem_sphere x] using
    (abs_real_inner_le_norm (EuclideanSpace.single 0 1 : RoundAmbient k) (x : RoundAmbient k))

private theorem pole_meridian_latitude_C3 (k : ℕ) (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    (roundCoordinate k).toFun (meridian k 0 1 (by norm_num) eps heps r) =
      eps/Real.sqrt (1+r^2) :=
  meridian_coordinate_i_C3 k 0 1 (by norm_num) eps heps r

private theorem equator_meridian_latitude_C3 (k : ℕ) (r : ℝ) :
    (roundCoordinate k).toFun (meridian k 1 0 (by norm_num) 1 (by norm_num) r) =
      r/Real.sqrt (1+r^2) :=
  meridian_coordinate_j_C3 k 1 0 (by norm_num) 1 (by norm_num) r

private theorem pole_meridian_smooth_even_C3 (k : ℕ)
    (s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (hlat : ConstantOnLatitudes k s)
    (eps : ℝ) (heps : eps^2 = 1) :
    ContDiff ℝ ∞ (fun r => s (meridian k 0 1 (by norm_num) eps heps r)) ∧
      Function.Even (fun r => s (meridian k 0 1 (by norm_num) eps heps r)) := by
  refine ⟨(s.contMDiff.comp (meridian_smooth k 0 1 (by norm_num) eps heps)).contDiff,?_⟩
  intro r
  apply hlat
  rw [pole_meridian_latitude_C3,pole_meridian_latitude_C3,neg_sq]

private theorem inv_square_profile_smooth_C3 (H : ℝ → ℝ) (hH : ContDiff ℝ 3 H)
    (U : Set ℝ) (hU : ∀ t ∈ U, t ≠ 0) :
    ContDiffOn ℝ 3 (fun t => H ((t⁻¹)^2-1)) U := by
  have hi : ContDiffOn ℝ 3 (fun t : ℝ => (t⁻¹)^2-1) U :=
    ((contDiffOn_id.inv hU).pow 2).sub contDiffOn_const
  exact hH.comp_contDiffOn hi

private theorem positive_pole_meridian_inverse_C3 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1/Real.sqrt (1+(Real.sqrt ((t⁻¹)^2-1))^2) = t := by
  have hi : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have hq : 0 ≤ (t⁻¹)^2-1 := by nlinarith
  rw [Real.sq_sqrt hq]
  have heq : 1+((t⁻¹)^2-1) = (t⁻¹)^2 := by ring
  rw [heq,Real.sqrt_sq (inv_nonneg.mpr ht.le)]
  simp

private theorem negative_pole_meridian_inverse_C3 {t : ℝ} (ht : t < 0) (ht1 : -1 ≤ t) :
    -1/Real.sqrt (1+(Real.sqrt ((t⁻¹)^2-1))^2) = t := by
  have hp := positive_pole_meridian_inverse_C3 (t := -t) (neg_pos.mpr ht) (by linarith)
  simp only [inv_neg,neg_sq] at hp
  rw [neg_div]
  linarith

private theorem equator_meridian_inverse_C3 {t : ℝ} (ht : -1 < t) (ht1 : t < 1) :
    (t/Real.sqrt (1-t^2))/Real.sqrt (1+(t/Real.sqrt (1-t^2))^2) = t := by
  have hw : 0 < 1-t^2 := by nlinarith
  have hs : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.mpr hw
  have hss := Real.sq_sqrt hw.le
  have heq : 1+(t/Real.sqrt (1-t^2))^2 = ((Real.sqrt (1-t^2))⁻¹)^2 := by
    field_simp
    nlinarith [hss]
  rw [heq,Real.sqrt_sq (inv_nonneg.mpr hs.le)]
  field_simp

private theorem equator_profile_smooth_C3 (k : ℕ)
    (s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) :
    ContDiffOn ℝ 3
      (fun t => s (meridian k 1 0 (by norm_num) 1 (by norm_num)
        (t/Real.sqrt (1-t^2)))) (Ioo (-1) 1) := by
  have hf : ContDiff ℝ ∞ (fun r => s (meridian k 1 0 (by norm_num) 1 (by norm_num) r)) :=
    (s.contMDiff.comp (meridian_smooth k 1 0 (by norm_num) 1 (by norm_num))).contDiff
  have hw : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < 1-t^2 := by
    intro t ht; nlinarith [ht.1,ht.2]
  have hg : ContDiffOn ℝ 3 (fun t : ℝ => t/Real.sqrt (1-t^2)) (Ioo (-1) 1) :=
    contDiffOn_id.div ((contDiffOn_const.sub (contDiffOn_id.pow 2)).sqrt
      (fun t ht => ne_of_gt (hw t ht))) (fun t ht => ne_of_gt (Real.sqrt_pos.mpr (hw t ht)))
  exact (hf.of_le (by decide : (3 : ℕ∞ω) ≤ ∞)).comp_contDiffOn hg

private theorem round_latitude_local_profile_C3 (k : ℕ)
    (s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (hlat : ConstantOnLatitudes k s)
    (x : RoundSphere k) :
    ∃ U ∈ 𝓝 ((roundCoordinate k).toFun x), ∃ v : ℝ → ℝ,
      ContDiffOn ℝ 3 v U ∧ ∀ y : RoundSphere k,
        (roundCoordinate k).toFun y ∈ U → v ((roundCoordinate k).toFun y) = s y := by
  by_cases hx : 0 < (roundCoordinate k).toFun x
  · obtain ⟨H,hH,hHr⟩ := smooth_even_exists_C3_square_profile
      (fun r => s (meridian k 0 1 (by norm_num) 1 (by norm_num) r))
      (pole_meridian_smooth_even_C3 k s hlat 1 (by norm_num)).1
      (pole_meridian_smooth_even_C3 k s hlat 1 (by norm_num)).2
    refine ⟨Ioi 0,isOpen_Ioi.mem_nhds hx,fun t => H ((t⁻¹)^2-1),
      inv_square_profile_smooth_C3 H hH _ (fun t ht => ne_of_gt ht),?_⟩
    intro y hy
    have hy1 := (abs_le.mp (roundCoordinate_bounds_C3 k y)).2
    have hi : 1 ≤ ((roundCoordinate k).toFun y)⁻¹ := (one_le_inv₀ hy).mpr hy1
    have hq : 0 ≤ (((roundCoordinate k).toFun y)⁻¹)^2-1 := by nlinarith
    dsimp only
    rw [← Real.sq_sqrt hq,hHr]
    apply hlat
    rw [pole_meridian_latitude_C3]
    exact positive_pole_meridian_inverse_C3 hy hy1
  · by_cases hxneg : (roundCoordinate k).toFun x < 0
    · obtain ⟨H,hH,hHr⟩ := smooth_even_exists_C3_square_profile
        (fun r => s (meridian k 0 1 (by norm_num) (-1) (by norm_num) r))
        (pole_meridian_smooth_even_C3 k s hlat (-1) (by norm_num)).1
        (pole_meridian_smooth_even_C3 k s hlat (-1) (by norm_num)).2
      refine ⟨Iio 0,isOpen_Iio.mem_nhds hxneg,fun t => H ((t⁻¹)^2-1),
        inv_square_profile_smooth_C3 H hH _ (fun t ht => ne_of_lt ht),?_⟩
      intro y hy
      have hy1 := (abs_le.mp (roundCoordinate_bounds_C3 k y)).1
      have hi : 1 ≤ (-(roundCoordinate k).toFun y)⁻¹ :=
        (one_le_inv₀ (neg_pos.mpr hy)).mpr (by linarith)
      simp only [inv_neg] at hi
      have hq : 0 ≤ (((roundCoordinate k).toFun y)⁻¹)^2-1 := by nlinarith
      dsimp only
      rw [← Real.sq_sqrt hq,hHr]
      apply hlat
      rw [pole_meridian_latitude_C3]
      exact negative_pole_meridian_inverse_C3 hy hy1
    · have hx0 : (roundCoordinate k).toFun x = 0 := le_antisymm (le_of_not_gt hx) (le_of_not_gt hxneg)
      refine ⟨Ioo (-1) 1,isOpen_Ioo.mem_nhds (by rw [hx0]; constructor <;> norm_num),
        fun t => s (meridian k 1 0 (by norm_num) 1 (by norm_num) (t/Real.sqrt (1-t^2))),
        equator_profile_smooth_C3 k s,?_⟩
      intro y hy
      apply hlat
      rw [equator_meridian_latitude_C3]
      exact equator_meridian_inverse_C3 hy.1 hy.2

/-- Two-pole regularity follows from the actual smooth sphere function and
same-latitude constancy. The resulting profile is C³ on all of ℝ. -/
theorem round_smooth_same_latitude_exists_C3_profile (k : ℕ)
    (s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (hlat : ConstantOnLatitudes k s) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 3 v ∧
      ∀ x : RoundSphere k, s x = v ((roundCoordinate k).toFun x) := by
  have hclosed : IsClosed ((roundCoordinate k).toFun '' (univ : Set (RoundSphere k))) :=
    (isCompact_univ.image (roundCoordinate k).smooth.continuous).isClosed
  obtain ⟨v,hv,hvs⟩ := exists_contDiff_extension_of_local (n := 3)
    (f := (roundCoordinate k).toFun) (g := (s : RoundSphere k → ℝ)) (K := univ) hclosed
    (fun x _ => by
      obtain ⟨U,hU,v,hv,hvs⟩ := round_latitude_local_profile_C3 k s hlat x
      exact ⟨U,hU,v,hv,fun y _ hy => hvs y hy⟩)
  exact ⟨v,hv,fun x => (hvs (mem_univ x)).symm⟩

/-- True positivity of the sphere function transfers to the entire
closed latitude interval, without endpoint assumptions. -/
theorem round_positive_same_latitude_exists_C3_profile (k : ℕ)
    (s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (hlat : ConstantOnLatitudes k s)
    (hpos : ∀ x, 0 < s x) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 3 v ∧
      (∀ x : RoundSphere k, s x = v ((roundCoordinate k).toFun x)) ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t := by
  obtain ⟨v,hv,hvs⟩ := round_smooth_same_latitude_exists_C3_profile k s hlat
  refine ⟨v,hv,hvs,?_⟩
  intro t ht
  obtain ⟨x,hx⟩ := roundCoordinate_surjective_Icc k t ht
  rw [← hx,← hvs x]
  exact hpos x

end DFLSphere
