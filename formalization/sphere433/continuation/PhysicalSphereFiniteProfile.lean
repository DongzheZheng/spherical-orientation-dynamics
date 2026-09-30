import continuation.PhysicalSphereLatitudeProfileC3

/-! For every finite order, genuine smooth zonal physical sphere functions
have global real profiles of that order, with the same physical values.
A common C-infinity real extension is not asserted or needed. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Filter Function Metric Manifold
open scoped Topology ContDiff Manifold RealInnerProductSpace InnerProductSpace
namespace DFLPhysicalLatitude
open DifferentialGeometry DifferentialGeometry.Analysis DifferentialGeometry.Geometry
open DFLSpectralCoordinates DFLSphere
variable {m : ℕ}
private theorem physicalMeridian_coordinate_i_Finite (k : ℕ) (i j : Fin (k+2)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    ⟪(EuclideanSpace.single i 1 : PhysicalAmbient k),
      (physicalMeridian k i j hij eps heps r : PhysicalAmbient k)⟫_ℝ = eps/Real.sqrt (1+r^2) := by
  simp [physicalMeridian,physicalMeridianAmbient,EuclideanSpace.inner_single_left,hij,div_eq_mul_inv,mul_comm]

private theorem physicalMeridian_coordinate_j_Finite (k : ℕ) (i j : Fin (k+2)) (hij : i ≠ j)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    ⟪(EuclideanSpace.single j 1 : PhysicalAmbient k),
      (physicalMeridian k i j hij eps heps r : PhysicalAmbient k)⟫_ℝ = r/Real.sqrt (1+r^2) := by
  simp [physicalMeridian,physicalMeridianAmbient,EuclideanSpace.inner_single_left,Ne.symm hij,div_eq_mul_inv,mul_comm]

private theorem physicalCoordinate_bounds_Finite (k : ℕ) (x : PhysicalSphere k) :
    |(physicalCoordinate k).toFun x| ≤ 1 := by
  change |⟪(EuclideanSpace.single 0 1 : PhysicalAmbient k),(x : PhysicalAmbient k)⟫_ℝ| ≤ 1
  simpa [norm_eq_of_mem_sphere x] using
    (abs_real_inner_le_norm (EuclideanSpace.single 0 1 : PhysicalAmbient k) (x : PhysicalAmbient k))

private theorem pole_physicalMeridian_latitude_Finite (k : ℕ) (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    (physicalCoordinate k).toFun (physicalMeridian k 0 1 (by norm_num) eps heps r) =
      eps/Real.sqrt (1+r^2) :=
  physicalMeridian_coordinate_i_Finite k 0 1 (by norm_num) eps heps r

private theorem equator_physicalMeridian_latitude_Finite (k : ℕ) (r : ℝ) :
    (physicalCoordinate k).toFun (physicalMeridian k 1 0 (by norm_num) 1 (by norm_num) r) =
      r/Real.sqrt (1+r^2) :=
  physicalMeridian_coordinate_j_Finite k 1 0 (by norm_num) 1 (by norm_num) r

private theorem pole_physicalMeridian_smooth_even_Finite (k : ℕ)
    (s : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯) (hlat : PhysicalConstantOnLatitudes k s)
    (eps : ℝ) (heps : eps^2 = 1) :
    ContDiff ℝ ∞ (fun r => s (physicalMeridian k 0 1 (by norm_num) eps heps r)) ∧
      Function.Even (fun r => s (physicalMeridian k 0 1 (by norm_num) eps heps r)) := by
  refine ⟨(s.contMDiff.comp (physicalMeridian_smooth k 0 1 (by norm_num) eps heps)).contDiff,?_⟩
  intro r
  apply hlat
  rw [pole_physicalMeridian_latitude_Finite,pole_physicalMeridian_latitude_Finite,neg_sq]

private theorem inv_square_profile_smooth_Finite (H : ℝ → ℝ) (hH : ContDiff ℝ (m : ℕ∞ω) H)
    (U : Set ℝ) (hU : ∀ t ∈ U, t ≠ 0) :
    ContDiffOn ℝ (m : ℕ∞ω) (fun t => H ((t⁻¹)^2-1)) U := by
  have hi : ContDiffOn ℝ (m : ℕ∞ω) (fun t : ℝ => (t⁻¹)^2-1) U :=
    ((contDiffOn_id.inv hU).pow 2).sub contDiffOn_const
  exact hH.comp_contDiffOn hi

private theorem positive_pole_physicalMeridian_inverse_Finite {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1/Real.sqrt (1+(Real.sqrt ((t⁻¹)^2-1))^2) = t := by
  have hi : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have hq : 0 ≤ (t⁻¹)^2-1 := by nlinarith
  rw [Real.sq_sqrt hq]
  have heq : 1+((t⁻¹)^2-1) = (t⁻¹)^2 := by ring
  rw [heq,Real.sqrt_sq (inv_nonneg.mpr ht.le)]
  simp

private theorem negative_pole_physicalMeridian_inverse_Finite {t : ℝ} (ht : t < 0) (ht1 : -1 ≤ t) :
    -1/Real.sqrt (1+(Real.sqrt ((t⁻¹)^2-1))^2) = t := by
  have hp := positive_pole_physicalMeridian_inverse_Finite (t := -t) (neg_pos.mpr ht) (by linarith)
  simp only [inv_neg,neg_sq] at hp
  rw [neg_div]
  linarith

private theorem equator_physicalMeridian_inverse_Finite {t : ℝ} (ht : -1 < t) (ht1 : t < 1) :
    (t/Real.sqrt (1-t^2))/Real.sqrt (1+(t/Real.sqrt (1-t^2))^2) = t := by
  have hw : 0 < 1-t^2 := by nlinarith
  have hs : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.mpr hw
  have hss := Real.sq_sqrt hw.le
  have heq : 1+(t/Real.sqrt (1-t^2))^2 = ((Real.sqrt (1-t^2))⁻¹)^2 := by
    field_simp
    nlinarith [hss]
  rw [heq,Real.sqrt_sq (inv_nonneg.mpr hs.le)]
  field_simp

private theorem equator_profile_smooth_Finite (k : ℕ)
    (s : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯) :
    ContDiffOn ℝ (m : ℕ∞ω)
      (fun t => s (physicalMeridian k 1 0 (by norm_num) 1 (by norm_num)
        (t/Real.sqrt (1-t^2)))) (Ioo (-1) 1) := by
  have hf : ContDiff ℝ ∞ (fun r => s (physicalMeridian k 1 0 (by norm_num) 1 (by norm_num) r)) :=
    (s.contMDiff.comp (physicalMeridian_smooth k 1 0 (by norm_num) 1 (by norm_num))).contDiff
  have hw : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < 1-t^2 := by
    intro t ht; nlinarith [ht.1,ht.2]
  have hg : ContDiffOn ℝ (m : ℕ∞ω) (fun t : ℝ => t/Real.sqrt (1-t^2)) (Ioo (-1) 1) :=
    contDiffOn_id.div ((contDiffOn_const.sub (contDiffOn_id.pow 2)).sqrt
      (fun t ht => ne_of_gt (hw t ht))) (fun t ht => ne_of_gt (Real.sqrt_pos.mpr (hw t ht)))
  exact (hf.of_le (by exact WithTop.coe_le_coe.mpr le_top : (m : ℕ∞ω) ≤ ∞)).comp_contDiffOn hg

private theorem round_latitude_local_profile_Finite (k : ℕ)
    (s : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯) (hlat : PhysicalConstantOnLatitudes k s)
    (x : PhysicalSphere k) :
    ∃ U ∈ 𝓝 ((physicalCoordinate k).toFun x), ∃ v : ℝ → ℝ,
      ContDiffOn ℝ (m : ℕ∞ω) v U ∧ ∀ y : PhysicalSphere k,
        (physicalCoordinate k).toFun y ∈ U → v ((physicalCoordinate k).toFun y) = s y := by
  by_cases hx : 0 < (physicalCoordinate k).toFun x
  · obtain ⟨H,hH,hHr⟩ := smooth_even_exists_finite_square_profile m
      (fun r => s (physicalMeridian k 0 1 (by norm_num) 1 (by norm_num) r))
      (pole_physicalMeridian_smooth_even_Finite k s hlat 1 (by norm_num)).1
      (pole_physicalMeridian_smooth_even_Finite k s hlat 1 (by norm_num)).2
    refine ⟨Ioi 0,isOpen_Ioi.mem_nhds hx,fun t => H ((t⁻¹)^2-1),
      inv_square_profile_smooth_Finite H hH _ (fun t ht => ne_of_gt ht),?_⟩
    intro y hy
    have hy1 := (abs_le.mp (physicalCoordinate_bounds_Finite k y)).2
    have hi : 1 ≤ ((physicalCoordinate k).toFun y)⁻¹ := (one_le_inv₀ hy).mpr hy1
    have hq : 0 ≤ (((physicalCoordinate k).toFun y)⁻¹)^2-1 := by nlinarith
    dsimp only
    rw [← Real.sq_sqrt hq,hHr]
    apply hlat
    rw [pole_physicalMeridian_latitude_Finite]
    exact positive_pole_physicalMeridian_inverse_Finite hy hy1
  · by_cases hxneg : (physicalCoordinate k).toFun x < 0
    · obtain ⟨H,hH,hHr⟩ := smooth_even_exists_finite_square_profile m
        (fun r => s (physicalMeridian k 0 1 (by norm_num) (-1) (by norm_num) r))
        (pole_physicalMeridian_smooth_even_Finite k s hlat (-1) (by norm_num)).1
        (pole_physicalMeridian_smooth_even_Finite k s hlat (-1) (by norm_num)).2
      refine ⟨Iio 0,isOpen_Iio.mem_nhds hxneg,fun t => H ((t⁻¹)^2-1),
        inv_square_profile_smooth_Finite H hH _ (fun t ht => ne_of_lt ht),?_⟩
      intro y hy
      have hy1 := (abs_le.mp (physicalCoordinate_bounds_Finite k y)).1
      have hi : 1 ≤ (-(physicalCoordinate k).toFun y)⁻¹ :=
        (one_le_inv₀ (neg_pos.mpr hy)).mpr (by linarith)
      simp only [inv_neg] at hi
      have hq : 0 ≤ (((physicalCoordinate k).toFun y)⁻¹)^2-1 := by nlinarith
      dsimp only
      rw [← Real.sq_sqrt hq,hHr]
      apply hlat
      rw [pole_physicalMeridian_latitude_Finite]
      exact negative_pole_physicalMeridian_inverse_Finite hy hy1
    · have hx0 : (physicalCoordinate k).toFun x = 0 := le_antisymm (le_of_not_gt hx) (le_of_not_gt hxneg)
      refine ⟨Ioo (-1) 1,isOpen_Ioo.mem_nhds (by rw [hx0]; constructor <;> norm_num),
        fun t => s (physicalMeridian k 1 0 (by norm_num) 1 (by norm_num) (t/Real.sqrt (1-t^2))),
        equator_profile_smooth_Finite k s,?_⟩
      intro y hy
      apply hlat
      rw [equator_physicalMeridian_latitude_Finite]
      exact equator_physicalMeridian_inverse_Finite hy.1 hy.2

/-- Two-pole regularity follows from the actual smooth sphere function and
same-latitude constancy. For every finite order, the resulting profile has that order on all of ℝ. -/
theorem physical_smooth_same_latitude_exists_finite_profile (m k : ℕ)
    (s : C^∞⟮𝓡 (k+1), PhysicalSphere k; ℝ⟯) (hlat : PhysicalConstantOnLatitudes k s) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (m : ℕ∞ω) v ∧
      ∀ x : PhysicalSphere k, s x = v ((physicalCoordinate k).toFun x) := by
  have hclosed : IsClosed ((physicalCoordinate k).toFun '' (univ : Set (PhysicalSphere k))) :=
    (isCompact_univ.image (physicalCoordinate k).smooth.continuous).isClosed
  obtain ⟨v,hv,hvs⟩ := exists_contDiff_extension_of_local (n := m)
    (f := (physicalCoordinate k).toFun) (g := (s : PhysicalSphere k → ℝ)) (K := univ) hclosed
    (fun x _ => by
      obtain ⟨U,hU,v,hv,hvs⟩ := round_latitude_local_profile_Finite k s hlat x
      exact ⟨U,hU,v,hv,fun y _ hy => hvs y hy⟩)
  exact ⟨v,hv,fun x => (hvs (mem_univ x)).symm⟩


end DFLPhysicalLatitude
