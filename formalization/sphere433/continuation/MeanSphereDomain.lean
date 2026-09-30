import continuation.MeanSpherePoleFamily
import continuation.CompactC2WeakH1
import DFLSphere433.RoundSphereCoordinates
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Closed

/-! Actual angular mean representatives in the original physical form domain.
The smooth even pole averages give a global C³ latitude representative by
closed-set gluing. No axisymmetry or regularity of an averaged state is assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold Metric Module Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Analysis DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DFLCotSphere DFLAngularMean DFLSphere
namespace DFLMeanSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E=n+2)]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

def heightInverse (t : ℝ) : ℝ := t/Real.sqrt (1-t^2)
def poleRadius (t : ℝ) : ℝ := Real.sqrt ((t⁻¹)^2-1)

def heightMean (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (t : ℝ) : ℝ :=
  if 0<t then poleMean p 1 (by norm_num) u (poleRadius t)
  else if t<0 then poleMean p (-1) (by norm_num) u (poleRadius t)
  else cotMean p u 0

private theorem heightInverse_smooth :
    ContDiffOn ℝ 3 heightInverse (Ioo (-1) 1) := by
  have hw : ∀ t ∈ Ioo (-1 : ℝ) 1, 0<1-t^2 := by
    intro t ht; nlinarith [ht.1,ht.2]
  exact contDiffOn_id.div ((contDiffOn_const.sub (contDiffOn_id.pow 2)).sqrt
    (fun t ht => ne_of_gt (hw t ht))) (fun t ht => ne_of_gt (Real.sqrt_pos.mpr (hw t ht)))

private theorem cotHeight_heightInverse {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    cotHeight (heightInverse t)=t := by
  have hw : 0<1-t^2 := by nlinarith [ht.1,ht.2]
  have hs : 0<Real.sqrt (1-t^2) := Real.sqrt_pos.mpr hw
  have hss := Real.sq_sqrt hw.le
  have heq : 1+(t/Real.sqrt (1-t^2))^2=((Real.sqrt (1-t^2))⁻¹)^2 := by
    field_simp
    nlinarith [hss]
  unfold cotHeight heightInverse cotAngularScale
  rw [heq,Real.sqrt_sq (inv_nonneg.mpr hs.le)]
  field_simp

private theorem poleRadius_pos {t : ℝ} (ht : t ∈ Ioo (-1) 1) (ht0 : t≠0) :
    0<poleRadius t := by
  apply Real.sqrt_pos.mpr
  have hsq : t^2<1 := by nlinarith [ht.1,ht.2]
  have hi : 1<(t⁻¹)^2 := by
    rw [inv_pow]
    exact (one_lt_inv₀ (sq_pos_of_ne_zero ht0)).mpr hsq
  linarith

private theorem positive_pole_inverse {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    cotAngularScale (poleRadius t)=t := by
  have hi : 1≤t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have hq : 0≤(t⁻¹)^2-1 := by nlinarith
  unfold cotAngularScale poleRadius
  rw [Real.sq_sqrt hq]
  have heq : 1+((t⁻¹)^2-1)=(t⁻¹)^2 := by ring
  rw [heq,Real.sqrt_sq (inv_nonneg.mpr ht.le)]
  simp

private theorem negative_pole_inverse {t : ℝ} (ht : t<0) (ht1 : -1≤t) :
    -cotAngularScale (poleRadius t)=t := by
  have hp := positive_pole_inverse (t := -t) (neg_pos.mpr ht) (by linarith)
  simp only [poleRadius,inv_neg,neg_sq] at hp
  change -cotAngularScale (Real.sqrt ((t⁻¹)^2-1))=t
  linarith

omit [FiniteDimensional ℝ E] in
private theorem poleFamily_height (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1)
    (y : PolarDir p) (r : ℝ) :
    ⟪(p : E),(poleFamily p eps heps (y,r) : E)⟫_ℝ=eps*cotAngularScale r := by
  have hpp : ⟪(p : E),(p : E)⟫_ℝ=1 := by
    rw [real_inner_self_eq_norm_sq,norm_eq_of_mem_sphere p]; norm_num
  have hpy : ⟪(p : E),((y : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ=0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (y : (ℝ ∙ (p : E))ᗮ).property
  change ⟪(p : E),cotAngularScale r • (eps • (p : E)+r • ((y : (ℝ ∙ (p : E))ᗮ) : E))⟫_ℝ=_
  simp only [real_inner_smul_right,inner_add_right,hpp,hpy,mul_one,mul_zero,add_zero]
  ring

private theorem cotHeight_inverse_radius (eps r : ℝ) (heps : eps^2=1) (hr : 0<r) :
    cotHeight (eps/r)=eps*cotAngularScale r := by
  unfold cotHeight
  rw [cotAngularScale_inverse_radius eps r heps hr]
  field_simp

/-- On the genuine interior latitude coordinate the pole construction is
exactly the original angular integral. -/
theorem heightMean_eq_cotMean (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    heightMean p u t=cotMean p u (heightInverse t) := by
  by_cases hp : 0<t
  · have hr := poleRadius_pos ht (ne_of_gt hp)
    have hh : cotHeight (1/poleRadius t)=t := by
      rw [cotHeight_inverse_radius 1 _ (by norm_num) hr,one_mul]
      exact positive_pole_inverse hp ht.2.le
    have hi := cotHeight_strictMono.injective (hh.trans (cotHeight_heightInverse ht).symm)
    simp only [heightMean,if_pos hp]
    rw [poleMean_eq_cotMean p 1 (by norm_num) u _ hr,hi]
  · by_cases hn : t<0
    · have hr := poleRadius_pos ht (ne_of_lt hn)
      have hh : cotHeight (-1/poleRadius t)=t := by
        rw [cotHeight_inverse_radius (-1) _ (by norm_num) hr,neg_one_mul]
        exact negative_pole_inverse hn ht.1.le
      have hi := cotHeight_strictMono.injective (hh.trans (cotHeight_heightInverse ht).symm)
      simp only [heightMean,if_neg hp,if_pos hn]
      rw [poleMean_eq_cotMean p (-1) (by norm_num) u _ hr,hi]
    · have ht0 : t=0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      simp [heightMean,ht0,heightInverse]

private theorem inv_square_profile_smooth (H : ℝ → ℝ) (hH : ContDiff ℝ 3 H)
    (U : Set ℝ) (hU : ∀t∈U,t≠0) :
    ContDiffOn ℝ 3 (fun t => H ((t⁻¹)^2-1)) U :=
  hH.comp_contDiffOn (((contDiffOn_id.inv hU).pow 2).sub contDiffOn_const)

private theorem heightMean_local_profile (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (t : ℝ) (_ht : t ∈ Icc (-1) 1) :
    ∃U∈𝓝 t,∃v : ℝ → ℝ,ContDiffOn ℝ 3 v U ∧
      ∀s∈Icc (-1 : ℝ) 1,s∈U → v s=heightMean p u s := by
  by_cases hp : 0<t
  · obtain ⟨H,hH,hHr⟩ := smooth_even_exists_C3_square_profile
      (poleMean p 1 (by norm_num) u) (poleMean_smooth _ _ _ _) (poleMean_even _ _ _ _)
    refine ⟨Ioi 0,isOpen_Ioi.mem_nhds hp,fun s => H ((s⁻¹)^2-1),
      inv_square_profile_smooth H hH _ (fun s hs => ne_of_gt hs),?_⟩
    intro s hs hs0
    change 0<s at hs0
    have hi : 1 ≤ s⁻¹ := (one_le_inv₀ hs0).mpr hs.2
    have hq : 0≤(s⁻¹)^2-1 := by nlinarith
    simp only [heightMean,if_pos hs0]
    rw [← Real.sq_sqrt hq,hHr]
    rfl
  · by_cases hn : t<0
    · obtain ⟨H,hH,hHr⟩ := smooth_even_exists_C3_square_profile
        (poleMean p (-1) (by norm_num) u) (poleMean_smooth _ _ _ _) (poleMean_even _ _ _ _)
      refine ⟨Iio 0,isOpen_Iio.mem_nhds hn,fun s => H ((s⁻¹)^2-1),
        inv_square_profile_smooth H hH _ (fun s hs => ne_of_lt hs),?_⟩
      intro s hs hs0
      change s<0 at hs0
      have hi : 1≤(-s)⁻¹ := (one_le_inv₀ (neg_pos.mpr hs0)).mpr (by linarith [hs.1])
      simp only [inv_neg] at hi
      have hq : 0≤(s⁻¹)^2-1 := by nlinarith
      simp only [heightMean,if_neg (not_lt_of_ge hs0.le),if_pos hs0]
      rw [← Real.sq_sqrt hq,hHr]
      rfl
    · have ht0 : t=0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      refine ⟨Ioo (-1) 1,isOpen_Ioo.mem_nhds (by rw [ht0]; constructor <;> norm_num),
        fun s => cotMean p u (heightInverse s),
        ((cotMean_smooth p u).of_le (by decide : (3 : ℕ∞ω)≤(∞ : ℕ∞ω))).comp_contDiffOn heightInverse_smooth,?_⟩
      intro s _ hs
      exact (heightMean_eq_cotMean p u hs).symm

/-- The angular average of an arbitrary actual smooth sphere function has
a global C³ latitude representative, including both original poles. -/
theorem angularMean_exists_C3_profile (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    ∃v : ℝ → ℝ,ContDiff ℝ 3 v ∧ ∀t∈Icc (-1 : ℝ) 1,v t=heightMean p u t := by
  have hc : IsClosed ((id : ℝ → ℝ) '' Icc (-1 : ℝ) 1) := by simpa using isClosed_Icc
  obtain ⟨v,hv,hvs⟩ := exists_contDiff_extension_of_local (n := 3)
    (f := id) (g := heightMean p u) (K := Icc (-1) 1) hc
    (fun t ht => heightMean_local_profile p u t ht)
  exact ⟨v,hv,hvs⟩

/-- The actual sphere radial representative determined by a latitude profile. -/
def meanSphereProfile (p : sphere (0 : E) 1) (v : ℝ → ℝ)
    (x : sphere (0 : E) 1) : ℝ := v ⟪(p : E),(x : E)⟫_ℝ

omit [FiniteDimensional ℝ E] in
theorem meanSphereProfile_contMDiff (p : sphere (0 : E) 1) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 3 v) :
    ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) 3 (meanSphereProfile p v) :=
  hv.contMDiff.comp ((innerCoordFun (E := E) (n := n+1) (p : E)).contMDiff.of_le (by decide : (3 : ℕ∞ω)≤(∞ : ℕ∞ω)))

/-- The whole-sphere representative pulls back to the genuine original
angular average, rather than to a separately selected radial state. -/
theorem meanSphereProfile_cot (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (v : ℝ → ℝ)
    (hv : ∀t∈Icc (-1 : ℝ) 1,v t=heightMean p u t) (y : PolarDir p) (s : ℝ) :
    meanSphereProfile p v (cotSpherePD (n := n) p (y,s))=cotMean p u s := by
  have ht := cotHeight_mem s
  have hi : heightInverse (cotHeight s)=s :=
    cotHeight_strictMono.injective (cotHeight_heightInverse ht)
  unfold meanSphereProfile
  rw [cotSpherePD_height]
  change v (cotHeight s)=_
  rw [hv _ ⟨ht.1.le,ht.2.le⟩,heightMean_eq_cotMean p u ht,hi]

/-- Both the actual radial angular mean and its actual deviation belong to
the genuine smooth H¹ completion, with their original classical energies.
The only input is the original smooth sphere function. -/
theorem angularMean_exists_form_domain (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    ∃v : ℝ → ℝ, ContDiff ℝ 3 v ∧
      (∀t∈Icc (-1 : ℝ) 1,v t=heightMean p u t) ∧
      ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) 2 (meanSphereProfile p v) ∧
      (∀y : PolarDir p,∀s : ℝ,
        meanSphereProfile p v (cotSpherePD (n := n) p (y,s))=cotMean p u s) ∧
      ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) 2 (fun x => u x-meanSphereProfile p v x) ∧
      (∀y : PolarDir p,∀s : ℝ,
        u (cotSpherePD (n := n) p (y,s))-meanSphereProfile p v (cotSpherePD (n := n) p (y,s))=
          cotDeviation p u (y,s)) ∧
      ∃A D : H1Compl (roundMetric (E := E) (n := n+1)),
        (H1ComplToLp _ A : sphere (0 : E) 1 → ℝ) =ᵐ[
          riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1) (roundMetric (E := E) (n := n+1))]
          meanSphereProfile p v ∧
        (H1ComplToLp _ D : sphere (0 : E) 1 → ℝ) =ᵐ[
          riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1) (roundMetric (E := E) (n := n+1))]
          (fun x => u x-meanSphereProfile p v x) ∧
        ‖A‖^2-‖H1ComplToLp _ A‖^2=
          ∫x, normGradSqFun (roundMetric (E := E) (n := n+1)) (meanSphereProfile p v) x
            ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1) (roundMetric (E := E) (n := n+1)) ∧
        ‖D‖^2-‖H1ComplToLp _ D‖^2=
          ∫x, normGradSqFun (roundMetric (E := E) (n := n+1)) (fun x => u x-meanSphereProfile p v x) x
            ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1) (roundMetric (E := E) (n := n+1)) := by
  let : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin (n+1)))) := ⟨by simp⟩
  obtain ⟨v,hv,hvs⟩ := angularMean_exists_C3_profile p u
  have hA : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) 2 (meanSphereProfile p v) :=
    (meanSphereProfile_contMDiff p v hv).of_le (by norm_num)
  have hD : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) 2 (fun x => u x-meanSphereProfile p v x) :=
    (u.contMDiff.of_le (by decide : (2 : ℕ∞ω)≤(∞ : ℕ∞ω))).sub hA
  obtain ⟨A,hAL,hAE⟩ := DFLC2WeakH1.contMDiff_two_exists_completion_energy
    (roundMetric (E := E) (n := n+1)) _ hA
  obtain ⟨D,hDL,hDE⟩ := DFLC2WeakH1.contMDiff_two_exists_completion_energy
    (roundMetric (E := E) (n := n+1)) _ hD
  refine ⟨v,hv,hvs,hA,meanSphereProfile_cot p u v hvs,hD,?_,A,D,hAL,hDL,hAE,hDE⟩
  intro y s
  rw [meanSphereProfile_cot p u v hvs]
  rfl

end DFLMeanSphere
