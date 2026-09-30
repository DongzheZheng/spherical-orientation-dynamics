import continuation.EvenSquareProfile
import DFLSphere433.RoundSphereSharpGap
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Closed

/-! Actual smooth rotationally symmetric sphere functions have C² latitude
profiles at both poles, and a global real C² extension. -/
noncomputable section
set_option maxHeartbeats 800000
open Set Filter Function Metric Manifold
open scoped Topology ContDiff Manifold RealInnerProductSpace InnerProductSpace
namespace DFLSphere
open DifferentialGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry
open DFLSpectralCoordinates

/-- Actual globally smooth normalized meridian in two coordinate directions. -/
def meridianAmbient (k : ℕ) (i j : Fin (k+3)) (eps r : ℝ) : RoundAmbient k :=
  (Real.sqrt (1+r^2))⁻¹ •
    (eps • EuclideanSpace.single i 1 + r • EuclideanSpace.single j 1)

private theorem meridianAmbient_norm (k : ℕ) (i j : Fin (k+3)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    ‖meridianAmbient k i j eps r‖ = 1 := by
  have hp : 0 < 1+r^2 := by positivity
  have hs := Real.sq_sqrt hp.le
  have hsn : Real.sqrt (1+r^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hii : ⟪(EuclideanSpace.single i 1 : RoundAmbient k), EuclideanSpace.single i 1⟫_ℝ = 1 := by simp
  have hjj : ⟪(EuclideanSpace.single j 1 : RoundAmbient k), EuclideanSpace.single j 1⟫_ℝ = 1 := by simp
  have hij0 : ⟪(EuclideanSpace.single i 1 : RoundAmbient k), EuclideanSpace.single j 1⟫_ℝ = 0 := by
    simp [EuclideanSpace.inner_single_left,hij]
  have hji0 : ⟪(EuclideanSpace.single j 1 : RoundAmbient k), EuclideanSpace.single i 1⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact hij0
  have hsq : ‖meridianAmbient k i j eps r‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    unfold meridianAmbient
    simp only [real_inner_smul_left,real_inner_smul_right,inner_add_left,inner_add_right,
      hii,hjj,hij0,hji0,mul_zero,zero_add,add_zero,mul_one]
    field_simp
    nlinarith [hs]
  nlinarith [norm_nonneg (meridianAmbient k i j eps r)]

def meridian (k : ℕ) (i j : Fin (k+3)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) : RoundSphere k :=
  ⟨meridianAmbient k i j eps r, by simpa using meridianAmbient_norm k i j hij eps heps r⟩

theorem meridian_smooth (k : ℕ) (i j : Fin (k+3)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 (k+2)) ∞ (meridian k i j hij eps heps) := by
  have hs : ContDiff ℝ ∞ (fun r : ℝ => Real.sqrt (1+r^2)) :=
    (by fun_prop : ContDiff ℝ ∞ (fun r : ℝ => 1+r^2)).sqrt (by intro r; positivity)
  have ha : ContDiff ℝ ∞ (meridianAmbient k i j eps) :=
    (hs.inv (by intro r; positivity)).smul (contDiff_const.add (contDiff_id.smul contDiff_const))
  exact ha.contMDiff.codRestrict_sphere (fun r => by simpa using meridianAmbient_norm k i j hij eps heps r)

private theorem meridian_coordinate_i (k : ℕ) (i j : Fin (k+3)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    ⟪(EuclideanSpace.single i 1 : RoundAmbient k),
      (meridian k i j hij eps heps r : RoundAmbient k)⟫_ℝ = eps/Real.sqrt (1+r^2) := by
  simp [meridian,meridianAmbient,EuclideanSpace.inner_single_left,hij,div_eq_mul_inv,mul_comm]

private theorem meridian_coordinate_j (k : ℕ) (i j : Fin (k+3)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    ⟪(EuclideanSpace.single j 1 : RoundAmbient k),
      (meridian k i j hij eps heps r : RoundAmbient k)⟫_ℝ = r/Real.sqrt (1+r^2) := by
  simp [meridian,meridianAmbient,EuclideanSpace.inner_single_left,Ne.symm hij,div_eq_mul_inv,mul_comm]

/-- Same-latitude constancy of the actual sphere function. This is the
conclusion of axis-fixed orthogonal invariance, not a profile assumption. -/
def ConstantOnLatitudes (k : ℕ) (s : RoundSphere k → ℝ) : Prop :=
  ∀ x y, (roundCoordinate k).toFun x = (roundCoordinate k).toFun y → s x = s y

private theorem roundCoordinate_bounds (k : ℕ) (x : RoundSphere k) :
    |(roundCoordinate k).toFun x| ≤ 1 := by
  change |⟪(EuclideanSpace.single 0 1 : RoundAmbient k),(x : RoundAmbient k)⟫_ℝ| ≤ 1
  simpa [norm_eq_of_mem_sphere x] using
    (abs_real_inner_le_norm (EuclideanSpace.single 0 1 : RoundAmbient k) (x : RoundAmbient k))

private theorem pole_meridian_latitude (k : ℕ) (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    (roundCoordinate k).toFun (meridian k 0 1 (by norm_num) eps heps r) =
      eps/Real.sqrt (1+r^2) :=
  meridian_coordinate_i k 0 1 (by norm_num) eps heps r

private theorem equator_meridian_latitude (k : ℕ) (r : ℝ) :
    (roundCoordinate k).toFun (meridian k 1 0 (by norm_num) 1 (by norm_num) r) =
      r/Real.sqrt (1+r^2) :=
  meridian_coordinate_j k 1 0 (by norm_num) 1 (by norm_num) r

private theorem pole_meridian_smooth_even (k : ℕ)
    (s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (hlat : ConstantOnLatitudes k s)
    (eps : ℝ) (heps : eps^2 = 1) :
    ContDiff ℝ ∞ (fun r => s (meridian k 0 1 (by norm_num) eps heps r)) ∧
      Function.Even (fun r => s (meridian k 0 1 (by norm_num) eps heps r)) := by
  refine ⟨(s.contMDiff.comp (meridian_smooth k 0 1 (by norm_num) eps heps)).contDiff,?_⟩
  intro r
  apply hlat
  rw [pole_meridian_latitude,pole_meridian_latitude,neg_sq]

private theorem inv_square_profile_smooth (H : ℝ → ℝ) (hH : ContDiff ℝ 2 H)
    (U : Set ℝ) (hU : ∀ t ∈ U, t ≠ 0) :
    ContDiffOn ℝ 2 (fun t => H ((t⁻¹)^2-1)) U := by
  have hi : ContDiffOn ℝ 2 (fun t : ℝ => (t⁻¹)^2-1) U :=
    ((contDiffOn_id.inv hU).pow 2).sub contDiffOn_const
  exact hH.comp_contDiffOn hi

private theorem positive_pole_meridian_inverse {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1/Real.sqrt (1+(Real.sqrt ((t⁻¹)^2-1))^2) = t := by
  have hi : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have hq : 0 ≤ (t⁻¹)^2-1 := by nlinarith
  rw [Real.sq_sqrt hq]
  have heq : 1+((t⁻¹)^2-1) = (t⁻¹)^2 := by ring
  rw [heq,Real.sqrt_sq (inv_nonneg.mpr ht.le)]
  simp

private theorem negative_pole_meridian_inverse {t : ℝ} (ht : t < 0) (ht1 : -1 ≤ t) :
    -1/Real.sqrt (1+(Real.sqrt ((t⁻¹)^2-1))^2) = t := by
  have hp := positive_pole_meridian_inverse (t := -t) (neg_pos.mpr ht) (by linarith)
  simp only [inv_neg,neg_sq] at hp
  rw [neg_div]
  linarith

private theorem equator_meridian_inverse {t : ℝ} (ht : -1 < t) (ht1 : t < 1) :
    (t/Real.sqrt (1-t^2))/Real.sqrt (1+(t/Real.sqrt (1-t^2))^2) = t := by
  have hw : 0 < 1-t^2 := by nlinarith
  have hs : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.mpr hw
  have hss := Real.sq_sqrt hw.le
  have heq : 1+(t/Real.sqrt (1-t^2))^2 = ((Real.sqrt (1-t^2))⁻¹)^2 := by
    field_simp
    nlinarith [hss]
  rw [heq,Real.sqrt_sq (inv_nonneg.mpr hs.le)]
  field_simp

private theorem equator_profile_smooth (k : ℕ)
    (s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) :
    ContDiffOn ℝ 2
      (fun t => s (meridian k 1 0 (by norm_num) 1 (by norm_num)
        (t/Real.sqrt (1-t^2)))) (Ioo (-1) 1) := by
  have hf : ContDiff ℝ ∞ (fun r => s (meridian k 1 0 (by norm_num) 1 (by norm_num) r)) :=
    (s.contMDiff.comp (meridian_smooth k 1 0 (by norm_num) 1 (by norm_num))).contDiff
  have hw : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < 1-t^2 := by
    intro t ht; nlinarith [ht.1,ht.2]
  have hg : ContDiffOn ℝ 2 (fun t : ℝ => t/Real.sqrt (1-t^2)) (Ioo (-1) 1) :=
    contDiffOn_id.div ((contDiffOn_const.sub (contDiffOn_id.pow 2)).sqrt
      (fun t ht => ne_of_gt (hw t ht))) (fun t ht => ne_of_gt (Real.sqrt_pos.mpr (hw t ht)))
  exact (hf.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)).comp_contDiffOn hg

private theorem round_latitude_local_profile (k : ℕ)
    (s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (hlat : ConstantOnLatitudes k s)
    (x : RoundSphere k) :
    ∃ U ∈ 𝓝 ((roundCoordinate k).toFun x), ∃ v : ℝ → ℝ,
      ContDiffOn ℝ 2 v U ∧ ∀ y : RoundSphere k,
        (roundCoordinate k).toFun y ∈ U → v ((roundCoordinate k).toFun y) = s y := by
  by_cases hx : 0 < (roundCoordinate k).toFun x
  · obtain ⟨H,hH,hHr⟩ := smooth_even_exists_C2_square_profile
      (fun r => s (meridian k 0 1 (by norm_num) 1 (by norm_num) r))
      (pole_meridian_smooth_even k s hlat 1 (by norm_num)).1
      (pole_meridian_smooth_even k s hlat 1 (by norm_num)).2
    refine ⟨Ioi 0,isOpen_Ioi.mem_nhds hx,fun t => H ((t⁻¹)^2-1),
      inv_square_profile_smooth H hH _ (fun t ht => ne_of_gt ht),?_⟩
    intro y hy
    have hy1 := (abs_le.mp (roundCoordinate_bounds k y)).2
    have hi : 1 ≤ ((roundCoordinate k).toFun y)⁻¹ := (one_le_inv₀ hy).mpr hy1
    have hq : 0 ≤ (((roundCoordinate k).toFun y)⁻¹)^2-1 := by nlinarith
    dsimp only
    rw [← Real.sq_sqrt hq,hHr]
    apply hlat
    rw [pole_meridian_latitude]
    exact positive_pole_meridian_inverse hy hy1
  · by_cases hxneg : (roundCoordinate k).toFun x < 0
    · obtain ⟨H,hH,hHr⟩ := smooth_even_exists_C2_square_profile
        (fun r => s (meridian k 0 1 (by norm_num) (-1) (by norm_num) r))
        (pole_meridian_smooth_even k s hlat (-1) (by norm_num)).1
        (pole_meridian_smooth_even k s hlat (-1) (by norm_num)).2
      refine ⟨Iio 0,isOpen_Iio.mem_nhds hxneg,fun t => H ((t⁻¹)^2-1),
        inv_square_profile_smooth H hH _ (fun t ht => ne_of_lt ht),?_⟩
      intro y hy
      have hy1 := (abs_le.mp (roundCoordinate_bounds k y)).1
      have hi : 1 ≤ (-(roundCoordinate k).toFun y)⁻¹ :=
        (one_le_inv₀ (neg_pos.mpr hy)).mpr (by linarith)
      simp only [inv_neg] at hi
      have hq : 0 ≤ (((roundCoordinate k).toFun y)⁻¹)^2-1 := by nlinarith
      dsimp only
      rw [← Real.sq_sqrt hq,hHr]
      apply hlat
      rw [pole_meridian_latitude]
      exact negative_pole_meridian_inverse hy hy1
    · have hx0 : (roundCoordinate k).toFun x = 0 := le_antisymm (le_of_not_gt hx) (le_of_not_gt hxneg)
      refine ⟨Ioo (-1) 1,isOpen_Ioo.mem_nhds (by rw [hx0]; constructor <;> norm_num),
        fun t => s (meridian k 1 0 (by norm_num) 1 (by norm_num) (t/Real.sqrt (1-t^2))),
        equator_profile_smooth k s,?_⟩
      intro y hy
      apply hlat
      rw [equator_meridian_latitude]
      exact equator_meridian_inverse hy.1 hy.2

/-- Two-pole regularity follows from the actual smooth sphere function and
same-latitude constancy. The resulting profile is C² on all of ℝ. -/
theorem round_smooth_same_latitude_exists_C2_profile (k : ℕ)
    (s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (hlat : ConstantOnLatitudes k s) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      ∀ x : RoundSphere k, s x = v ((roundCoordinate k).toFun x) := by
  have hclosed : IsClosed ((roundCoordinate k).toFun '' (univ : Set (RoundSphere k))) :=
    (isCompact_univ.image (roundCoordinate k).smooth.continuous).isClosed
  obtain ⟨v,hv,hvs⟩ := exists_contDiff_extension_of_local (n := 2)
    (f := (roundCoordinate k).toFun) (g := (s : RoundSphere k → ℝ)) (K := univ) hclosed
    (fun x _ => by
      obtain ⟨U,hU,v,hv,hvs⟩ := round_latitude_local_profile k s hlat x
      exact ⟨U,hU,v,hv,fun y _ hy => hvs y hy⟩)
  exact ⟨v,hv,fun x => (hvs (mem_univ x)).symm⟩

/-- Every latitude in the full closed interval is realized by an actual
round-sphere point, including both poles. -/
theorem roundCoordinate_surjective_Icc (k : ℕ) (t : ℝ) (ht : t ∈ Icc (-1) 1) :
    ∃ x : RoundSphere k, (roundCoordinate k).toFun x = t := by
  by_cases hp : 0 < t
  · refine ⟨meridian k 0 1 (by norm_num) 1 (by norm_num)
      (Real.sqrt ((t⁻¹)^2-1)),?_⟩
    rw [pole_meridian_latitude]
    exact positive_pole_meridian_inverse hp ht.2
  · by_cases hn : t < 0
    · refine ⟨meridian k 0 1 (by norm_num) (-1) (by norm_num)
        (Real.sqrt ((t⁻¹)^2-1)),?_⟩
      rw [pole_meridian_latitude]
      exact negative_pole_meridian_inverse hn ht.1
    · have h0 : t = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      refine ⟨meridian k 1 0 (by norm_num) 1 (by norm_num) 0,?_⟩
      rw [equator_meridian_latitude,h0]
      simp

theorem roundCoordinate_range (k : ℕ) :
    range ((roundCoordinate k).toFun) = Icc (-1) 1 := by
  ext t
  constructor
  · rintro ⟨x,rfl⟩
    exact abs_le.mp (roundCoordinate_bounds k x)
  · exact roundCoordinate_surjective_Icc k t

/-- True positivity of the sphere function transfers to the entire
closed latitude interval, without endpoint assumptions. -/
theorem round_positive_same_latitude_exists_C2_profile (k : ℕ)
    (s : C^∞⟮𝓡 (k+2), RoundSphere k; ℝ⟯) (hlat : ConstantOnLatitudes k s)
    (hpos : ∀ x, 0 < s x) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      (∀ x : RoundSphere k, s x = v ((roundCoordinate k).toFun x)) ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t := by
  obtain ⟨v,hv,hvs⟩ := round_smooth_same_latitude_exists_C2_profile k s hlat
  refine ⟨v,hv,hvs,?_⟩
  intro t ht
  obtain ⟨x,hx⟩ := roundCoordinate_surjective_Icc k t ht
  rw [← hx,← hvs x]
  exact hpos x

end DFLSphere
