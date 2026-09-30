import continuation.EvenSquareFiniteProfile
import DFLSphere433.RoundSphereSharpGap
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Closed

/-! Genuine C³ pole profiles for every positive physical sphere dimension,
including the circle. The same normalized meridians, smooth even squared
radius, and closed-set gluing prove regularity without a profile premise. -/
noncomputable section
set_option maxHeartbeats 800000
open Set Filter Function Metric Manifold
open scoped Topology ContDiff Manifold RealInnerProductSpace InnerProductSpace
namespace DFLPhysicalLatitude
open DifferentialGeometry DifferentialGeometry.Analysis DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis.Laplacian
open DFLSpectralCoordinates DFLSphere
abbrev PhysicalAmbient (k : ℕ) := EuclideanSpace ℝ (Fin (k+2))
abbrev PhysicalSphere (k : ℕ) := sphere (0 : PhysicalAmbient k) 1
instance (k : ℕ) : Fact (Module.finrank ℝ (PhysicalAmbient k) = k+1+1) :=
  ⟨by simp [PhysicalAmbient]⟩
instance (k : ℕ) : NeZero (k+1) := ⟨by omega⟩
def physicalSphereMetric (k : ℕ) : SmoothRiemannianMetric (𝓡 (k+1)) (PhysicalSphere k) :=
  roundMetric (E := PhysicalAmbient k) (n := k+1)
def physicalCoordinate (k : ℕ) : SmoothScalar (physicalSphereMetric k) :=
  ⟨innerCoordFun (E := PhysicalAmbient k) (n := k+1) (EuclideanSpace.single 0 1),
    (innerCoordFun (E := PhysicalAmbient k) (n := k+1) (EuclideanSpace.single 0 1)).contMDiff⟩
/-- Actual globally smooth normalized physicalMeridian in two coordinate directions. -/
def physicalMeridianAmbient (k : ℕ) (i j : Fin (k+2)) (eps r : ℝ) : PhysicalAmbient k :=
  (Real.sqrt (1+r^2))⁻¹ •
    (eps • EuclideanSpace.single i 1 + r • EuclideanSpace.single j 1)

private theorem physicalMeridianAmbient_norm (k : ℕ) (i j : Fin (k+2)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    ‖physicalMeridianAmbient k i j eps r‖ = 1 := by
  have hp : 0 < 1+r^2 := by positivity
  have hs := Real.sq_sqrt hp.le
  have hsn : Real.sqrt (1+r^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hii : ⟪(EuclideanSpace.single i 1 : PhysicalAmbient k), EuclideanSpace.single i 1⟫_ℝ = 1 := by simp
  have hjj : ⟪(EuclideanSpace.single j 1 : PhysicalAmbient k), EuclideanSpace.single j 1⟫_ℝ = 1 := by simp
  have hij0 : ⟪(EuclideanSpace.single i 1 : PhysicalAmbient k), EuclideanSpace.single j 1⟫_ℝ = 0 := by
    simp [EuclideanSpace.inner_single_left,hij]
  have hji0 : ⟪(EuclideanSpace.single j 1 : PhysicalAmbient k), EuclideanSpace.single i 1⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact hij0
  have hsq : ‖physicalMeridianAmbient k i j eps r‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    unfold physicalMeridianAmbient
    simp only [real_inner_smul_left,real_inner_smul_right,inner_add_left,inner_add_right,
      hii,hjj,hij0,hji0,mul_zero,zero_add,add_zero,mul_one]
    field_simp
    nlinarith [hs]
  nlinarith [norm_nonneg (physicalMeridianAmbient k i j eps r)]

def physicalMeridian (k : ℕ) (i j : Fin (k+2)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) : PhysicalSphere k :=
  ⟨physicalMeridianAmbient k i j eps r, by simpa using physicalMeridianAmbient_norm k i j hij eps heps r⟩

theorem physicalMeridian_smooth (k : ℕ) (i j : Fin (k+2)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 (k+1)) ∞ (physicalMeridian k i j hij eps heps) := by
  have hs : ContDiff ℝ ∞ (fun r : ℝ => Real.sqrt (1+r^2)) :=
    (by fun_prop : ContDiff ℝ ∞ (fun r : ℝ => 1+r^2)).sqrt (by intro r; positivity)
  have ha : ContDiff ℝ ∞ (physicalMeridianAmbient k i j eps) :=
    (hs.inv (by intro r; positivity)).smul (contDiff_const.add (contDiff_id.smul contDiff_const))
  exact ha.contMDiff.codRestrict_sphere (fun r => by simpa using physicalMeridianAmbient_norm k i j hij eps heps r)

/-- Same-latitude constancy of the actual sphere function. This is the
conclusion of axis-fixed orthogonal invariance, not a profile assumption. -/
def PhysicalConstantOnLatitudes (k : ℕ) (s : PhysicalSphere k → ℝ) : Prop :=
  ∀ x y, (physicalCoordinate k).toFun x = (physicalCoordinate k).toFun y → s x = s y

private theorem physicalMeridian_coordinate_i_C3 (k : ℕ) (i j : Fin (k+2)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    ⟪(EuclideanSpace.single i 1 : PhysicalAmbient k),
      (physicalMeridian k i j hij eps heps r : PhysicalAmbient k)⟫_ℝ = eps/Real.sqrt (1+r^2) := by
  simp [physicalMeridian,physicalMeridianAmbient,EuclideanSpace.inner_single_left,hij,div_eq_mul_inv,mul_comm]

private theorem physicalMeridian_coordinate_j_C3 (k : ℕ) (i j : Fin (k+2)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    ⟪(EuclideanSpace.single j 1 : PhysicalAmbient k),
      (physicalMeridian k i j hij eps heps r : PhysicalAmbient k)⟫_ℝ = r/Real.sqrt (1+r^2) := by
  simp [physicalMeridian,physicalMeridianAmbient,EuclideanSpace.inner_single_left,Ne.symm hij,div_eq_mul_inv,mul_comm]

private theorem physicalCoordinate_bounds_C3 (k : ℕ) (x : PhysicalSphere k) :
    |(physicalCoordinate k).toFun x| ≤ 1 := by
  change |⟪(EuclideanSpace.single 0 1 : PhysicalAmbient k),(x : PhysicalAmbient k)⟫_ℝ| ≤ 1
  simpa [norm_eq_of_mem_sphere x] using
    (abs_real_inner_le_norm (EuclideanSpace.single 0 1 : PhysicalAmbient k) (x : PhysicalAmbient k))

private theorem pole_physicalMeridian_latitude_C3 (k : ℕ) (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    (physicalCoordinate k).toFun (physicalMeridian k 0 1 (by norm_num) eps heps r) =
      eps/Real.sqrt (1+r^2) :=
  physicalMeridian_coordinate_i_C3 k 0 1 (by norm_num) eps heps r

private theorem equator_physicalMeridian_latitude_C3 (k : ℕ) (r : ℝ) :
    (physicalCoordinate k).toFun (physicalMeridian k 1 0 (by norm_num) 1 (by norm_num) r) =
      r/Real.sqrt (1+r^2) :=
  physicalMeridian_coordinate_j_C3 k 1 0 (by norm_num) 1 (by norm_num) r

private theorem pole_physicalMeridian_smooth_even_C3 (k : ℕ)
    (s : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯) (hlat : PhysicalConstantOnLatitudes k s)
    (eps : ℝ) (heps : eps^2 = 1) :
    ContDiff ℝ ∞ (fun r => s (physicalMeridian k 0 1 (by norm_num) eps heps r)) ∧
      Function.Even (fun r => s (physicalMeridian k 0 1 (by norm_num) eps heps r)) := by
  refine ⟨(s.contMDiff.comp (physicalMeridian_smooth k 0 1 (by norm_num) eps heps)).contDiff,?_⟩
  intro r
  apply hlat
  rw [pole_physicalMeridian_latitude_C3,pole_physicalMeridian_latitude_C3,neg_sq]

private theorem inv_square_profile_smooth_C3 (H : ℝ → ℝ) (hH : ContDiff ℝ 3 H)
    (U : Set ℝ) (hU : ∀ t ∈ U, t ≠ 0) :
    ContDiffOn ℝ 3 (fun t => H ((t⁻¹)^2-1)) U := by
  have hi : ContDiffOn ℝ 3 (fun t : ℝ => (t⁻¹)^2-1) U :=
    ((contDiffOn_id.inv hU).pow 2).sub contDiffOn_const
  exact hH.comp_contDiffOn hi

private theorem positive_pole_physicalMeridian_inverse_C3 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1/Real.sqrt (1+(Real.sqrt ((t⁻¹)^2-1))^2) = t := by
  have hi : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have hq : 0 ≤ (t⁻¹)^2-1 := by nlinarith
  rw [Real.sq_sqrt hq]
  have heq : 1+((t⁻¹)^2-1) = (t⁻¹)^2 := by ring
  rw [heq,Real.sqrt_sq (inv_nonneg.mpr ht.le)]
  simp

private theorem negative_pole_physicalMeridian_inverse_C3 {t : ℝ} (ht : t < 0) (ht1 : -1 ≤ t) :
    -1/Real.sqrt (1+(Real.sqrt ((t⁻¹)^2-1))^2) = t := by
  have hp := positive_pole_physicalMeridian_inverse_C3 (t := -t) (neg_pos.mpr ht) (by linarith)
  simp only [inv_neg,neg_sq] at hp
  rw [neg_div]
  linarith

private theorem equator_physicalMeridian_inverse_C3 {t : ℝ} (ht : -1 < t) (ht1 : t < 1) :
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
    (s : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯) :
    ContDiffOn ℝ 3
      (fun t => s (physicalMeridian k 1 0 (by norm_num) 1 (by norm_num)
        (t/Real.sqrt (1-t^2)))) (Ioo (-1) 1) := by
  have hf : ContDiff ℝ ∞ (fun r => s (physicalMeridian k 1 0 (by norm_num) 1 (by norm_num) r)) :=
    (s.contMDiff.comp (physicalMeridian_smooth k 1 0 (by norm_num) 1 (by norm_num))).contDiff
  have hw : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < 1-t^2 := by
    intro t ht; nlinarith [ht.1,ht.2]
  have hg : ContDiffOn ℝ 3 (fun t : ℝ => t/Real.sqrt (1-t^2)) (Ioo (-1) 1) :=
    contDiffOn_id.div ((contDiffOn_const.sub (contDiffOn_id.pow 2)).sqrt
      (fun t ht => ne_of_gt (hw t ht))) (fun t ht => ne_of_gt (Real.sqrt_pos.mpr (hw t ht)))
  exact (hf.of_le (by decide : (3 : ℕ∞ω) ≤ ∞)).comp_contDiffOn hg

private theorem round_latitude_local_profile_C3 (k : ℕ)
    (s : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯) (hlat : PhysicalConstantOnLatitudes k s)
    (x : PhysicalSphere k) :
    ∃ U ∈ 𝓝 ((physicalCoordinate k).toFun x), ∃ v : ℝ → ℝ,
      ContDiffOn ℝ 3 v U ∧ ∀ y : PhysicalSphere k,
        (physicalCoordinate k).toFun y ∈ U → v ((physicalCoordinate k).toFun y) = s y := by
  by_cases hx : 0 < (physicalCoordinate k).toFun x
  · obtain ⟨H,hH,hHr⟩ := smooth_even_exists_C3_square_profile
      (fun r => s (physicalMeridian k 0 1 (by norm_num) 1 (by norm_num) r))
      (pole_physicalMeridian_smooth_even_C3 k s hlat 1 (by norm_num)).1
      (pole_physicalMeridian_smooth_even_C3 k s hlat 1 (by norm_num)).2
    refine ⟨Ioi 0,isOpen_Ioi.mem_nhds hx,fun t => H ((t⁻¹)^2-1),
      inv_square_profile_smooth_C3 H hH _ (fun t ht => ne_of_gt ht),?_⟩
    intro y hy
    have hy1 := (abs_le.mp (physicalCoordinate_bounds_C3 k y)).2
    have hi : 1 ≤ ((physicalCoordinate k).toFun y)⁻¹ := (one_le_inv₀ hy).mpr hy1
    have hq : 0 ≤ (((physicalCoordinate k).toFun y)⁻¹)^2-1 := by nlinarith
    dsimp only
    rw [← Real.sq_sqrt hq,hHr]
    apply hlat
    rw [pole_physicalMeridian_latitude_C3]
    exact positive_pole_physicalMeridian_inverse_C3 hy hy1
  · by_cases hxneg : (physicalCoordinate k).toFun x < 0
    · obtain ⟨H,hH,hHr⟩ := smooth_even_exists_C3_square_profile
        (fun r => s (physicalMeridian k 0 1 (by norm_num) (-1) (by norm_num) r))
        (pole_physicalMeridian_smooth_even_C3 k s hlat (-1) (by norm_num)).1
        (pole_physicalMeridian_smooth_even_C3 k s hlat (-1) (by norm_num)).2
      refine ⟨Iio 0,isOpen_Iio.mem_nhds hxneg,fun t => H ((t⁻¹)^2-1),
        inv_square_profile_smooth_C3 H hH _ (fun t ht => ne_of_lt ht),?_⟩
      intro y hy
      have hy1 := (abs_le.mp (physicalCoordinate_bounds_C3 k y)).1
      have hi : 1 ≤ (-(physicalCoordinate k).toFun y)⁻¹ :=
        (one_le_inv₀ (neg_pos.mpr hy)).mpr (by linarith)
      simp only [inv_neg] at hi
      have hq : 0 ≤ (((physicalCoordinate k).toFun y)⁻¹)^2-1 := by nlinarith
      dsimp only
      rw [← Real.sq_sqrt hq,hHr]
      apply hlat
      rw [pole_physicalMeridian_latitude_C3]
      exact negative_pole_physicalMeridian_inverse_C3 hy hy1
    · have hx0 : (physicalCoordinate k).toFun x = 0 := le_antisymm (le_of_not_gt hx) (le_of_not_gt hxneg)
      refine ⟨Ioo (-1) 1,isOpen_Ioo.mem_nhds (by rw [hx0]; constructor <;> norm_num),
        fun t => s (physicalMeridian k 1 0 (by norm_num) 1 (by norm_num) (t/Real.sqrt (1-t^2))),
        equator_profile_smooth_C3 k s,?_⟩
      intro y hy
      apply hlat
      rw [equator_physicalMeridian_latitude_C3]
      exact equator_physicalMeridian_inverse_C3 hy.1 hy.2

/-- Two-pole regularity follows from the actual smooth sphere function and
same-latitude constancy. The resulting profile is C³ on all of ℝ. -/
theorem physical_smooth_same_latitude_exists_C3_profile (k : ℕ)
    (s : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯) (hlat : PhysicalConstantOnLatitudes k s) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 3 v ∧
      ∀ x : PhysicalSphere k, s x = v ((physicalCoordinate k).toFun x) := by
  have hclosed : IsClosed ((physicalCoordinate k).toFun '' (univ : Set (PhysicalSphere k))) :=
    (isCompact_univ.image (physicalCoordinate k).smooth.continuous).isClosed
  obtain ⟨v,hv,hvs⟩ := exists_contDiff_extension_of_local (n := 3)
    (f := (physicalCoordinate k).toFun) (g := (s : PhysicalSphere k → ℝ)) (K := univ) hclosed
    (fun x _ => by
      obtain ⟨U,hU,v,hv,hvs⟩ := round_latitude_local_profile_C3 k s hlat x
      exact ⟨U,hU,v,hv,fun y _ hy => hvs y hy⟩)
  exact ⟨v,hv,fun x => (hvs (mem_univ x)).symm⟩

/-- Every latitude in the full closed interval is realized by an actual
round-sphere point, including both poles. -/
theorem physicalCoordinate_surjective_Icc (k : ℕ) (t : ℝ) (ht : t ∈ Icc (-1) 1) :
    ∃ x : PhysicalSphere k, (physicalCoordinate k).toFun x = t := by
  by_cases hp : 0 < t
  · refine ⟨physicalMeridian k 0 1 (by norm_num) 1 (by norm_num)
      (Real.sqrt ((t⁻¹)^2-1)),?_⟩
    rw [pole_physicalMeridian_latitude_C3]
    exact positive_pole_physicalMeridian_inverse_C3 hp ht.2
  · by_cases hn : t < 0
    · refine ⟨physicalMeridian k 0 1 (by norm_num) (-1) (by norm_num)
        (Real.sqrt ((t⁻¹)^2-1)),?_⟩
      rw [pole_physicalMeridian_latitude_C3]
      exact negative_pole_physicalMeridian_inverse_C3 hn ht.1
    · have h0 : t = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      refine ⟨physicalMeridian k 1 0 (by norm_num) 1 (by norm_num) 0,?_⟩
      rw [equator_physicalMeridian_latitude_C3,h0]
      simp


/-- All actual physical-sphere latitudes lie in the closed physical interval. -/
theorem physicalCoordinate_mem_Icc (k : ℕ) (x : PhysicalSphere k) :
    (physicalCoordinate k).toFun x ∈ Icc (-1 : ℝ) 1 :=
  abs_le.mp (physicalCoordinate_bounds_C3 k x)

end DFLPhysicalLatitude
