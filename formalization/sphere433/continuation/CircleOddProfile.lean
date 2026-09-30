import continuation.CircleOddGeometry

/-! Smooth actual odd circle functions admit a genuine global C²
first-transverse profile, including at both physical poles. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Filter Function Metric Manifold
open scoped Topology ContDiff Manifold RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus.SmoothExtension
open DFLPhysicalLatitude DFLSphere
namespace DFLCircleOdd

/-- The pole values of the quotient are the actual smooth Hadamard
meridian factors. They are constructed from u, not boundary assumptions. -/
def circleOddQuotient (u : Circle → ℝ) (x : Circle) : ℝ :=
  if (x : CircleAmbient) 1 = 0 then
    if 0 < (x : CircleAmbient) 0 then circlePoleFactor u 1 (by norm_num) 0
    else circlePoleFactor u (-1) (by norm_num) 0
  else u x/(x : CircleAmbient) 1

theorem circleOddQuotient_factor (u : Circle → ℝ) (hu : CircleOdd u) (x : Circle) :
    u x = (x : CircleAmbient) 1*circleOddQuotient u x := by
  by_cases hx : (x : CircleAmbient) 1 = 0
  · rw [hx,zero_mul]
    exact circle_odd_zero_on_axis u hu x hx
  · dsimp [circleOddQuotient]
    rw [if_neg hx,mul_div_cancel₀ _ hx]

private theorem inv_square_profile_smooth_Odd (H : ℝ → ℝ) (hH : ContDiff ℝ 2 H)
    (U : Set ℝ) (hU : ∀ t ∈ U, t ≠ 0) :
    ContDiffOn ℝ 2 (fun t => H ((t⁻¹)^2-1)) U := by
  have hi : ContDiffOn ℝ 2 (fun t : ℝ => (t⁻¹)^2-1) U :=
    ((contDiffOn_id.inv hU).pow 2).sub contDiffOn_const
  exact hH.comp_contDiffOn hi

private theorem positive_pole_physicalMeridian_inverse_Odd {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1/Real.sqrt (1+(Real.sqrt ((t⁻¹)^2-1))^2) = t := by
  have hi : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have hq : 0 ≤ (t⁻¹)^2-1 := by nlinarith
  rw [Real.sq_sqrt hq]
  have heq : 1+((t⁻¹)^2-1) = (t⁻¹)^2 := by ring
  rw [heq,Real.sqrt_sq (inv_nonneg.mpr ht.le)]
  simp

private theorem negative_pole_physicalMeridian_inverse_Odd {t : ℝ} (ht : t < 0) (ht1 : -1 ≤ t) :
    -1/Real.sqrt (1+(Real.sqrt ((t⁻¹)^2-1))^2) = t := by
  have hp := positive_pole_physicalMeridian_inverse_Odd (t := -t) (neg_pos.mpr ht) (by linarith)
  simp only [inv_neg,neg_sq] at hp
  rw [neg_div]
  linarith

private theorem equator_physicalMeridian_inverse_Odd {t : ℝ} (ht : -1 < t) (ht1 : t < 1) :
    (t/Real.sqrt (1-t^2))/Real.sqrt (1+(t/Real.sqrt (1-t^2))^2) = t := by
  have hw : 0 < 1-t^2 := by nlinarith
  have hs : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.mpr hw
  have hss := Real.sq_sqrt hw.le
  have heq : 1+(t/Real.sqrt (1-t^2))^2 = ((Real.sqrt (1-t^2))⁻¹)^2 := by
    field_simp
    nlinarith [hss]
  rw [heq,Real.sqrt_sq (inv_nonneg.mpr hs.le)]
  field_simp

/-- Actual odd pole meridians have a C² squared-radius quotient. -/
private theorem pole_square_factor (u : C^∞⟮𝓡 1, Circle; ℝ⟯)
    (hu : CircleOdd u) (eps : ℝ) (heps : eps^2 = 1) :
    ∃ H : ℝ → ℝ, ContDiff ℝ 2 H ∧
      ∀ r, H (r^2) = circlePoleFactor u eps heps r := by
  have hh := circlePoleFactor_smooth_even u hu eps heps
  exact smooth_even_exists_finite_square_profile 2 _ hh.1 hh.2

private theorem north_local_quotient (u : C^∞⟮𝓡 1, Circle; ℝ⟯)
    (hu : CircleOdd u) :
    ∃ v : ℝ → ℝ, ContDiffOn ℝ 2 v (Ioi 0) ∧
      ∀ y : Circle, 0 < (y : CircleAmbient) 0 →
        v ((y : CircleAmbient) 0) = circleOddQuotient u y := by
  obtain ⟨H,hH,hHr⟩ := pole_square_factor u hu 1 (by norm_num)
  refine ⟨fun t => H ((t⁻¹)^2-1),
    inv_square_profile_smooth_Odd H hH _ (fun t ht => ne_of_gt ht),?_⟩
  intro y hy
  have hn := circle_norm_identity y
  have hy1 : (y : CircleAmbient) 0 ≤ 1 := by nlinarith [sq_nonneg ((y : CircleAmbient) 1)]
  have hi : 1 ≤ ((y : CircleAmbient) 0)⁻¹ := (one_le_inv₀ hy).mpr hy1
  have hq : 0 ≤ (((y : CircleAmbient) 0)⁻¹)^2-1 := by nlinarith
  let r := Real.sqrt ((((y : CircleAmbient) 0)⁻¹)^2-1)
  let z := circlePoleMeridian 1 (by norm_num) r
  have hrs : r^2 = (((y : CircleAmbient) 0)⁻¹)^2-1 := Real.sq_sqrt hq
  have hz0 : (z : CircleAmbient) 0 = (y : CircleAmbient) 0 := by
    rw [circlePoleMeridian_coord0]
    exact positive_pole_physicalMeridian_inverse_Odd hy hy1
  have hfact : u z = (z : CircleAmbient) 1*H ((((y : CircleAmbient) 0)⁻¹)^2-1) := by
    rw [circlePoleValue_factor u hu 1 (by norm_num) r,← hHr r,hrs]
  have hfy : u y = (y : CircleAmbient) 1*H ((((y : CircleAmbient) 0)⁻¹)^2-1) := by
    exact circle_odd_factor_transfer u hu (fun _ => H ((((y : CircleAmbient) 0)⁻¹)^2-1))
      y z hz0.symm hfact
  by_cases hyz : (y : CircleAmbient) 1 = 0
  · have hy0 : (y : CircleAmbient) 0 = 1 := by rw [hyz] at hn; nlinarith
    dsimp [circleOddQuotient]
    rw [if_pos hyz,if_pos hy,hy0]
    simpa using hHr 0
  · dsimp [circleOddQuotient]
    rw [if_neg hyz,hfy,mul_div_cancel_left₀ _ hyz]

private theorem south_local_quotient (u : C^∞⟮𝓡 1, Circle; ℝ⟯)
    (hu : CircleOdd u) :
    ∃ v : ℝ → ℝ, ContDiffOn ℝ 2 v (Iio 0) ∧
      ∀ y : Circle, (y : CircleAmbient) 0 < 0 →
        v ((y : CircleAmbient) 0) = circleOddQuotient u y := by
  obtain ⟨H,hH,hHr⟩ := pole_square_factor u hu (-1) (by norm_num)
  refine ⟨fun t => H ((t⁻¹)^2-1),
    inv_square_profile_smooth_Odd H hH _ (fun t ht => ne_of_lt ht),?_⟩
  intro y hy
  have hn := circle_norm_identity y
  have hy1 : -1 ≤ (y : CircleAmbient) 0 := by nlinarith [sq_nonneg ((y : CircleAmbient) 1)]
  have hi : 1 ≤ (-(y : CircleAmbient) 0)⁻¹ := (one_le_inv₀ (neg_pos.mpr hy)).mpr (by linarith)
  simp only [inv_neg] at hi
  have hq : 0 ≤ (((y : CircleAmbient) 0)⁻¹)^2-1 := by nlinarith
  let r := Real.sqrt ((((y : CircleAmbient) 0)⁻¹)^2-1)
  let z := circlePoleMeridian (-1) (by norm_num) r
  have hrs : r^2 = (((y : CircleAmbient) 0)⁻¹)^2-1 := Real.sq_sqrt hq
  have hz0 : (z : CircleAmbient) 0 = (y : CircleAmbient) 0 := by
    rw [circlePoleMeridian_coord0]
    exact negative_pole_physicalMeridian_inverse_Odd hy hy1
  have hfact : u z = (z : CircleAmbient) 1*H ((((y : CircleAmbient) 0)⁻¹)^2-1) := by
    rw [circlePoleValue_factor u hu (-1) (by norm_num) r,← hHr r,hrs]
  have hfy : u y = (y : CircleAmbient) 1*H ((((y : CircleAmbient) 0)⁻¹)^2-1) :=
    circle_odd_factor_transfer u hu (fun _ => H ((((y : CircleAmbient) 0)⁻¹)^2-1))
      y z hz0.symm hfact
  by_cases hyz : (y : CircleAmbient) 1 = 0
  · have hy0 : (y : CircleAmbient) 0 = -1 := by rw [hyz] at hn; nlinarith
    dsimp [circleOddQuotient]
    rw [if_pos hyz,if_neg (not_lt_of_ge hy.le),hy0]
    simpa using hHr 0
  · dsimp [circleOddQuotient]
    rw [if_neg hyz,hfy,mul_div_cancel_left₀ _ hyz]

private def equatorFactor (u : Circle → ℝ) (r : ℝ) : ℝ :=
  u (physicalMeridian 0 1 0 (by norm_num) 1 (by norm_num) r)*Real.sqrt (1+r^2)

private theorem equator_local_quotient (u : C^∞⟮𝓡 1, Circle; ℝ⟯)
    (hu : CircleOdd u) :
    ∃ v : ℝ → ℝ, ContDiffOn ℝ 2 v (Ioo (-1) 1) ∧
      ∀ y : Circle, (y : CircleAmbient) 0 ∈ Ioo (-1 : ℝ) 1 →
        v ((y : CircleAmbient) 0) = circleOddQuotient u y := by
  let F := equatorFactor u
  have hF : ContDiff ℝ ∞ F := by
    have hs : ContDiff ℝ ∞ (fun r : ℝ => Real.sqrt (1+r^2)) :=
      (by fun_prop : ContDiff ℝ ∞ (fun r : ℝ => 1+r^2)).sqrt (by intro r; positivity)
    exact ((u.contMDiff.comp (physicalMeridian_smooth 0 1 0 (by norm_num) 1 (by norm_num))).contDiff).mul hs
  let v := fun t => F (t/Real.sqrt (1-t^2))
  have hw : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < 1-t^2 := by intro t ht; nlinarith [ht.1,ht.2]
  have hg : ContDiffOn ℝ 2 (fun t : ℝ => t/Real.sqrt (1-t^2)) (Ioo (-1) 1) :=
    contDiffOn_id.div ((contDiffOn_const.sub (contDiffOn_id.pow 2)).sqrt
      (fun t ht => ne_of_gt (hw t ht))) (fun t ht => ne_of_gt (Real.sqrt_pos.mpr (hw t ht)))
  refine ⟨v,(hF.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)).comp_contDiffOn hg,?_⟩
  intro y hy
  let r := (y : CircleAmbient) 0/Real.sqrt (1-((y : CircleAmbient) 0)^2)
  let z := physicalMeridian 0 1 0 (by norm_num) 1 (by norm_num) r
  have hz0 : (z : CircleAmbient) 0 = (y : CircleAmbient) 0 := by
    have hz0r : (z : CircleAmbient) 0 = r/Real.sqrt (1+r^2) := by
      simp [z,physicalMeridian,physicalMeridianAmbient,div_eq_mul_inv,mul_comm]
    rw [hz0r]
    exact equator_physicalMeridian_inverse_Odd hy.1 hy.2
  have hz1 : (z : CircleAmbient) 1 = 1/Real.sqrt (1+r^2) := by
    simp [z,physicalMeridian,physicalMeridianAmbient,div_eq_mul_inv,mul_comm]
  have hs : Real.sqrt (1+r^2) ≠ 0 := by positivity
  have hfact : u z = (z : CircleAmbient) 1*v ((z : CircleAmbient) 0) := by
    rw [hz1,hz0]
    change u z = (1/Real.sqrt (1+r^2))*(u z*Real.sqrt (1+r^2))
    field_simp
  have hfy := circle_odd_factor_transfer u hu v y z hz0.symm hfact
  have hyz : (y : CircleAmbient) 1 ≠ 0 := by
    intro hz
    have hn := circle_norm_identity y
    rw [hz] at hn
    nlinarith [hw _ hy]
  dsimp [circleOddQuotient]
  rw [if_neg hyz,hfy,mul_div_cancel_left₀ _ hyz]

/-- A genuine smooth circle odd state has a global C² first-transverse
profile. The Hadamard quotient proves both physical pole values. -/
theorem circle_smooth_odd_exists_C2_profile (u : C^∞⟮𝓡 1, Circle; ℝ⟯)
    (hu : CircleOdd u) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      ∀ x : Circle, u x = (x : CircleAmbient) 1*v ((x : CircleAmbient) 0) := by
  have hc : Continuous (fun x : Circle => (x : CircleAmbient) 0) := by
    have hh := (DifferentialGeometry.Geometry.innerCoordFun (n := 1) circleAxis).contMDiff.continuous
    change Continuous (fun x : Circle => ⟪circleAxis,(x : CircleAmbient)⟫_ℝ) at hh
    simpa [circleAxis,EuclideanSpace.inner_single_left] using hh
  have hclosed : IsClosed ((fun x : Circle => (x : CircleAmbient) 0) '' univ) :=
    (isCompact_univ.image hc).isClosed
  obtain ⟨v,hv,hvs⟩ := exists_contDiff_extension_of_local (n := 2)
    (f := fun x : Circle => (x : CircleAmbient) 0) (g := circleOddQuotient u)
    (K := univ) hclosed (by
      intro x _
      by_cases hx : 0 < (x : CircleAmbient) 0
      · obtain ⟨v,hv,hvs⟩ := north_local_quotient u hu
        exact ⟨Ioi 0,isOpen_Ioi.mem_nhds hx,v,hv,fun y _ hy => hvs y hy⟩
      · by_cases hxneg : (x : CircleAmbient) 0 < 0
        · obtain ⟨v,hv,hvs⟩ := south_local_quotient u hu
          exact ⟨Iio 0,isOpen_Iio.mem_nhds hxneg,v,hv,fun y _ hy => hvs y hy⟩
        · have hx0 : (x : CircleAmbient) 0 = 0 := le_antisymm (le_of_not_gt hx) (le_of_not_gt hxneg)
          obtain ⟨v,hv,hvs⟩ := equator_local_quotient u hu
          refine ⟨Ioo (-1) 1,isOpen_Ioo.mem_nhds ?_,v,hv,fun y _ hy => hvs y hy⟩
          rw [hx0]
          norm_num)
  refine ⟨v,hv,?_⟩
  intro x
  rw [circleOddQuotient_factor u hu x]
  have he : v ((x : CircleAmbient) 0) = circleOddQuotient u x := hvs (mem_univ x)
  rw [he]

end DFLCircleOdd
