import DFL.Geometry.CircleLawSource

/-!
# Closed lower rays of the original circle-coordinate law

Finite-measure monotonicity and continuity of the geometric `arccos` tail
settle the equator and poles, without assuming an arcsine density.
-/

namespace DFL.Geometry

open MeasureTheory Filter
open scoped Topology

noncomputable section

private theorem two_pos : 0 < (2 : ℕ) := by decide

private instance : IsFiniteMeasure (area 2) := by
  change IsFiniteMeasure (volume : Measure (Ambient 2)).toSphere
  infer_instance

private instance : IsFiniteMeasure (coordinateLaw 2 two_pos) := by
  change IsFiniteMeasure ((area 2).map (coordinate 2 two_pos))
  infer_instance

private theorem closed_lower_of_open_lower
    (μ : Measure ℝ) [IsFiniteMeasure μ] (F : ℝ → ℝ)
    (t b : ℝ) (htb : t < b) (hF : ContinuousAt F t)
    (hopen : μ.real (Set.Iio t) = F t)
    (hnear : ∀ u ∈ Set.Ioo t b, μ.real (Set.Iio u) = F u) :
    μ.real (Set.Iic t) = F t := by
  have hleft : F t ≤ μ.real (Set.Iic t) := by
    rw [← hopen]
    exact measureReal_mono (Set.Iio_subset_Iic le_rfl)
  have hright : ∀ᶠ u in 𝓝[>] t, μ.real (Set.Iic t) ≤ F u := by
    filter_upwards [Ioo_mem_nhdsGT htb] with u hu
    have hsub : Set.Iic t ⊆ Set.Iio u := fun x hx =>
      lt_of_le_of_lt hx hu.1
    simpa only [hnear u hu] using measureReal_mono (μ := μ) hsub
  have hlim : Tendsto F (𝓝[>] t) (𝓝 (F t)) :=
    hF.tendsto.mono_left nhdsWithin_le_nhds
  exact le_antisymm (ge_of_tendsto hlim hright) hleft

theorem coordinateLaw_two_Iic_neg_real (t : ℝ)
    (ht : -1 < t) (ht0 : t < 0) :
    (coordinateLaw 2 two_pos).real (Set.Iic t) =
      2 * Real.arccos (-t) := by
  apply closed_lower_of_open_lower
    (coordinateLaw 2 two_pos) (fun u => 2 * Real.arccos (-u)) t 0 ht0
  · fun_prop
  · exact coordinateLaw_two_Iio_neg_real t ht ht0
  · intro u hu
    exact coordinateLaw_two_Iio_neg_real u (ht.trans hu.1) hu.2

theorem coordinateLaw_two_Iic_pos_real (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    (coordinateLaw 2 two_pos).real (Set.Iic t) =
      2 * Real.pi - 2 * Real.arccos t := by
  have htail := coordinateLaw_two_Ioi_real t ht ht1
  have hcompl := measureReal_compl (μ := coordinateLaw 2 two_pos)
    (s := Set.Ioi t) measurableSet_Ioi
  simpa only [Set.compl_Ioi, coordinateLaw_two_univ_real, htail] using hcompl

theorem coordinateLaw_two_Iic_neg_one_real :
    (coordinateLaw 2 two_pos).real (Set.Iic (-1 : ℝ)) = 0 := by
  let μ := coordinateLaw 2 two_pos
  let F : ℝ → ℝ := fun u => 2 * Real.arccos (-u)
  have hright : ∀ᶠ u in 𝓝[>] (-1 : ℝ),
      μ.real (Set.Iic (-1 : ℝ)) ≤ F u := by
    filter_upwards [Ioo_mem_nhdsGT (show (-1 : ℝ) < 0 by norm_num)]
      with u hu
    have hsub : Set.Iic (-1 : ℝ) ⊆ Set.Iio u := fun x hx =>
      lt_of_le_of_lt hx hu.1
    have htail : μ.real (Set.Iio u) = F u := by
      dsimp [μ, F]
      exact coordinateLaw_two_Iio_neg_real u hu.1 hu.2
    simpa only [htail] using measureReal_mono (μ := μ) hsub
  have hlim : Tendsto F (𝓝[>] (-1 : ℝ)) (𝓝 (F (-1))) := by
    have hc : ContinuousAt F (-1) := by fun_prop
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hupper : μ.real (Set.Iic (-1 : ℝ)) ≤ F (-1) :=
    ge_of_tendsto hlim hright
  have hF : F (-1) = 0 := by simp [F]
  exact le_antisymm (hF ▸ hupper) measureReal_nonneg

theorem coordinateLaw_two_Iic_zero_real :
    (coordinateLaw 2 two_pos).real (Set.Iic (0 : ℝ)) =
      Real.pi := by
  let μ := coordinateLaw 2 two_pos
  let M := μ.real (Set.Iic (0 : ℝ))
  have hlow_event : ∀ᶠ u in 𝓝[<] (0 : ℝ),
      2 * Real.arccos (-u) ≤ M := by
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)]
      with u hu
    have hsub : Set.Iio u ⊆ Set.Iic (0 : ℝ) := fun x hx =>
      (le_of_lt hx).trans hu.2.le
    have htail := coordinateLaw_two_Iio_neg_real u hu.1 hu.2
    simpa only [M, μ, htail] using measureReal_mono (μ := μ) hsub
  have hlim_low : Tendsto (fun u : ℝ => 2 * Real.arccos (-u))
      (𝓝[<] (0 : ℝ)) (𝓝 Real.pi) := by
    have hc : ContinuousAt (fun u : ℝ => 2 * Real.arccos (-u)) 0 := by fun_prop
    have hval : 2 * Real.arccos (-(0 : ℝ)) = Real.pi := by
      rw [neg_zero, Real.arccos_zero]
      ring
    simpa only [hval] using hc.tendsto.mono_left
      (nhdsWithin_le_nhds : (𝓝[<] (0 : ℝ)) ≤ 𝓝 (0 : ℝ))
  have hlow : Real.pi ≤ M := le_of_tendsto hlim_low hlow_event
  have hupp_event : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      M ≤ 2 * Real.pi - 2 * Real.arccos u := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
      with u hu
    have hsub : Set.Iic (0 : ℝ) ⊆ Set.Iic u :=
      Set.Iic_subset_Iic.mpr hu.1.le
    have htail := coordinateLaw_two_Iic_pos_real u hu.1 hu.2
    simpa only [M, μ, htail] using measureReal_mono (μ := μ) hsub
  have hlim_upp : Tendsto (fun u : ℝ => 2 * Real.pi - 2 * Real.arccos u)
      (𝓝[>] (0 : ℝ)) (𝓝 Real.pi) := by
    have hc : ContinuousAt (fun u : ℝ => 2 * Real.pi - 2 * Real.arccos u)
        0 := by fun_prop
    have hval : 2 * Real.pi - 2 * Real.arccos (0 : ℝ) = Real.pi := by
      rw [Real.arccos_zero]
      ring
    simpa only [hval] using hc.tendsto.mono_left
      (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ))
  have hupp : M ≤ Real.pi := ge_of_tendsto hlim_upp hupp_event
  exact le_antisymm hupp hlow

theorem coordinateLaw_two_Iic_low_real (t : ℝ) (ht : t < -1) :
    (coordinateLaw 2 two_pos).real (Set.Iic t) = 0 := by
  have hsub : Set.Iic t ⊆ (Set.Icc (-1 : ℝ) 1)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and]
    intro hxlow
    have hxt : x ≤ t := hx
    linarith
  exact measureReal_mono_null hsub
    ((measureReal_eq_zero_iff).2 (coordinateLaw_outside_Icc 2 two_pos))

theorem coordinateLaw_two_Iic_high_real (t : ℝ) (ht : 1 ≤ t) :
    (coordinateLaw 2 two_pos).real (Set.Iic t) = 2 * Real.pi := by
  have hcap : sphereCapSucc 1 t = ∅ := by
    ext ω
    simp only [sphereCapSucc, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    intro h
    have hcoord := (coordinate_mem_Icc 2 two_pos ω).2
    linarith
  have htail : (coordinateLaw 2 two_pos).real (Set.Ioi t) = 0 := by
    rw [coordinateLaw, Measure.real, Measure.map_apply
      (continuous_coordinate 2 two_pos).measurable measurableSet_Ioi]
    change ((area 2) (sphereCapSucc 1 t)).toReal = 0
    rw [hcap]
    simp
  have hcompl := measureReal_compl (μ := coordinateLaw 2 two_pos)
    (s := Set.Ioi t) measurableSet_Ioi
  simpa only [Set.compl_Ioi, coordinateLaw_two_univ_real, htail, sub_zero] using hcompl

end

end DFL.Geometry
