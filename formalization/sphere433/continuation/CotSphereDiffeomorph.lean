import DifferentialGeometry.Geometry.Metric.Sphere.Polar.PartialDiffeomorphism
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The original polar sphere coordinates in the globally regular parameter
s=cot(theta). Source is the full angular sphere times ℝ; target is the true
sphere with its two poles removed. Smoothness and both inverse identities
are derived from the actual polar partial diffeomorphism. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold Metric Module Set Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+2)]

def cotAngle (s : ℝ) : ℝ := Real.pi/2-Real.arctan s

def cotParameter (theta : ℝ) : ℝ := Real.tan (Real.pi/2-theta)

theorem cotAngle_mem (s : ℝ) : cotAngle s ∈ Ioo (0 : ℝ) Real.pi := by
  have hs := Real.arctan_mem_Ioo s
  dsimp [cotAngle]
  constructor <;> linarith [hs.1,hs.2]

theorem cotParameter_cotAngle (s : ℝ) : cotParameter (cotAngle s) = s := by
  simp [cotParameter,cotAngle,Real.tan_arctan]

theorem cotAngle_cotParameter {theta : ℝ} (ht : theta ∈ Ioo (0 : ℝ) Real.pi) :
    cotAngle (cotParameter theta) = theta := by
  have hl : -(Real.pi/2) < Real.pi/2-theta := by linarith [ht.2]
  have hr : Real.pi/2-theta < Real.pi/2 := by linarith [ht.1]
  rw [cotAngle,cotParameter,Real.arctan_tan hl hr]
  ring

theorem cotAngle_smooth : ContDiff ℝ ∞ cotAngle := contDiff_const.sub Real.contDiff_arctan

private theorem cotParameter_smoothAt {theta : ℝ} (ht : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContDiffAt ℝ ∞ cotParameter theta := by
  have hm : Real.pi/2-theta ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [ht.1,ht.2]
  exact (Real.contDiffAt_tan.mpr (ne_of_gt (Real.cos_pos_of_mem_Ioo hm))).comp theta
    (contDiffAt_const.sub contDiffAt_id)

/-- The true smooth reparametrization, with no excluded real s values. -/
def cotPolarParameterPD (p : sphere (0 : E) 1) :
    PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 n))
      (PolarDir p × ℝ) (ℝ × PolarDir p) ∞ where
  toFun q := (cotAngle q.2,q.1)
  invFun q := (q.2,cotParameter q.1)
  source := univ
  target := polarSource p
  map_source' q _ := cotAngle_mem q.2
  map_target' _ _ := mem_univ _
  left_inv' q _ := by ext <;> simp [cotParameter_cotAngle]
  right_inv' q hq := by ext <;> simp [cotAngle_cotParameter hq]
  open_source := isOpen_univ
  open_target := isOpen_Ioo.preimage continuous_fst
  contMDiffOn_toFun :=
    ((cotAngle_smooth.contMDiff.comp contMDiff_snd).prodMk contMDiff_fst).contMDiffOn
  contMDiffOn_invFun := by
    intro q hq
    exact (contMDiffAt_snd.prodMk
      ((cotParameter_smoothAt hq).contMDiffAt.comp q contMDiffAt_fst)).contMDiffWithinAt

/-- Actual global cot-parameter partial diffeomorphism of the sphere. -/
def cotSpherePD (p : sphere (0 : E) 1) :
    PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1))
      (PolarDir p × ℝ) (sphere (0 : E) 1) ∞ :=
  (cotPolarParameterPD (n := n) p).trans (spherePolarPD (n := n) p)

@[simp] theorem cotSpherePD_apply (p : sphere (0 : E) 1) (q : PolarDir p × ℝ) :
    cotSpherePD (n := n) p q = spherePolarPD (n := n) p (cotAngle q.2,q.1) := rfl

@[simp] theorem cotSpherePD_source (p : sphere (0 : E) 1) :
    (cotSpherePD (n := n) p).source = univ := by
  have hs : (cotSpherePD (n := n) p).source =
      (cotPolarParameterPD (n := n) p).source ∩
        (cotPolarParameterPD (n := n) p) ⁻¹' (spherePolarPD (n := n) p).source := rfl
  rw [hs]
  ext q
  simp only [cotPolarParameterPD,spherePolarPD_source,mem_inter_iff,mem_univ,true_and,mem_preimage]
  exact ⟨fun _ => trivial,fun _ => cotAngle_mem q.2⟩

@[simp] theorem cotSpherePD_target (p : sphere (0 : E) 1) :
    (cotSpherePD (n := n) p).target = polarTarget p := by
  ext x
  change x ∈ polarTarget p ∩ {x | (spherePolarPD (n := n) p).symm x ∈ polarSource p} ↔
    x ∈ polarTarget p
  exact ⟨fun h => h.1,fun h => ⟨h,(spherePolarPD (n := n) p).map_target' h⟩⟩

theorem cotSpherePD_smooth (p : sphere (0 : E) 1) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) ∞ (cotSpherePD (n := n) p) := by
  apply contMDiffOn_univ.mp
  simpa only [cotSpherePD_source] using (cotSpherePD (n := n) p).contMDiffOn_toFun

theorem cotSpherePD_inverse_smooth (p : sphere (0 : E) 1) :
    ContMDiffOn (𝓡 (n+1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (cotSpherePD (n := n) p).symm (polarTarget p) := by
  rw [← cotSpherePD_target (n := n) p]
  exact (cotSpherePD (n := n) p).contMDiffOn_invFun

theorem cotSpherePD_left_inverse (p : sphere (0 : E) 1) (q : PolarDir p × ℝ) :
    (cotSpherePD (n := n) p).symm (cotSpherePD (n := n) p q) = q :=
  (cotSpherePD (n := n) p).left_inv' (by rw [cotSpherePD_source]; exact mem_univ q)

theorem cotSpherePD_right_inverse (p : sphere (0 : E) 1) (x : sphere (0 : E) 1)
    (hx : x ∈ polarTarget p) :
    cotSpherePD (n := n) p ((cotSpherePD (n := n) p).symm x) = x :=
  (cotSpherePD (n := n) p).right_inv' (by rw [cotSpherePD_target]; exact hx)

/-- All real cot parameters have strictly positive angular scale. -/
def cotAngularScale (s : ℝ) : ℝ := (Real.sqrt (1+s^2))⁻¹

def cotLineScale (s : ℝ) : ℝ := (1+s^2)⁻¹

theorem cotAngularScale_pos (s : ℝ) : 0 < cotAngularScale s := by
  unfold cotAngularScale
  positivity

theorem cotLineScale_pos (s : ℝ) : 0 < cotLineScale s := by
  unfold cotLineScale
  positivity

theorem cotAngularScale_smooth : ContDiff ℝ ∞ cotAngularScale :=
  ((by fun_prop : ContDiff ℝ ∞ (fun s : ℝ => 1+s^2)).sqrt
    (by intro s; positivity)).inv (by intro s; positivity)

theorem cotLineScale_smooth : ContDiff ℝ ∞ cotLineScale :=
  (by fun_prop : ContDiff ℝ ∞ (fun s : ℝ => 1+s^2)).inv (by intro s; positivity)

theorem cotAngle_cos (s : ℝ) : Real.cos (cotAngle s) = s*cotAngularScale s := by
  rw [cotAngle,Real.cos_pi_div_two_sub,Real.sin_arctan]
  rfl

theorem cotAngle_sin (s : ℝ) : Real.sin (cotAngle s) = cotAngularScale s := by
  rw [cotAngle,Real.sin_pi_div_two_sub,Real.cos_arctan]
  simp [cotAngularScale]

/-- The actual ambient map is (s*p+y)/sqrt(1+s²), globally in s. -/
theorem cotSpherePD_ambient (p : sphere (0 : E) 1) (q : PolarDir p × ℝ) :
    (cotSpherePD (n := n) p q : E) = cotAngularScale q.2 •
      (q.2 • (p : E)+((q.1 : (ℝ ∙ (p : E))ᗮ) : E)) := by
  change Real.cos (cotAngle q.2) • (p : E)+Real.sin (cotAngle q.2) •
    ((q.1 : (ℝ ∙ (p : E))ᗮ) : E) = _
  rw [cotAngle_cos,cotAngle_sin,smul_add,smul_smul,
    mul_comm q.2 (cotAngularScale q.2)]

/-- The actual open sphere target, with exactly the two physical poles
removed. -/
def cotSphereTarget (p : sphere (0 : E) 1) : TopologicalSpace.Opens (sphere (0 : E) 1) :=
  ⟨polarTarget p,by simpa only [cotSpherePD_target] using (cotSpherePD (n := n) p).open_target⟩

theorem cotSpherePD_mem_target (p : sphere (0 : E) 1) (q : PolarDir p × ℝ) :
    cotSpherePD (n := n) p q ∈ polarTarget p := by
  have ht := (cotSpherePD (n := n) p).map_source'
    (by rw [cotSpherePD_source]; exact mem_univ q)
  simpa only [cotSpherePD_target] using ht

/-- A genuine globally defined diffeomorphism onto the actual open sphere
submanifold, constructed from the proved partial diffeomorphism. -/
def cotSphereDiffeo (p : sphere (0 : E) 1) :
    Diffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1))
      (PolarDir p × ℝ) (cotSphereTarget (n := n) p) ∞ where
  toFun q := ⟨cotSpherePD (n := n) p q,cotSpherePD_mem_target p q⟩
  invFun x := (cotSpherePD (n := n) p).symm x.1
  left_inv q := cotSpherePD_left_inverse p q
  right_inv x := by
    apply Subtype.ext
    exact cotSpherePD_right_inverse p x.1 x.2
  contMDiff_toFun := by
    intro q
    exact codRestr_contMDiffAt (fun y => cotSpherePD_mem_target p y) (cotSpherePD_smooth p).contMDiffAt
  contMDiff_invFun := by
    intro x
    change ContMDiffAt (𝓡 (n+1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (fun y : cotSphereTarget (n := n) p => (cotSpherePD (n := n) p).symm (y : sphere (0 : E) 1)) x
    rw [contMDiffAt_subtype_iff]
    exact (cotSpherePD_inverse_smooth p).contMDiffAt
      ((cotSphereTarget (n := n) p).isOpen.mem_nhds x.2)

@[simp] theorem cotSphereDiffeo_coe (p : sphere (0 : E) 1) (q : PolarDir p × ℝ) :
    (cotSphereDiffeo (n := n) p q : sphere (0 : E) 1) = cotSpherePD (n := n) p q := rfl

end DFLCotSphere
