import DFL.Spectral.ClosedFormLinear

/-!
# The Hilbert implementation retains the same physical variational problem

The two coordinate projections are continuous linear maps.  The Hilbert
space contains only centered values, and its exact Rayleigh infimum agrees
with both earlier physical smooth-core and closed-graph infima.
-/

namespace DFL.Spectral

open MeasureTheory InnerProductSpace

noncomputable section

/-- The actual sphere value projection from the completed Hilbert graph. -/
def formValue (d : ℕ) (r : ℝ) :
    HilbertFormSpace d r →L[ℝ] Lp ℝ 2 (alignedMeasure d r) :=
  (WithLp.fstL 2 ℝ _ _).comp (hilbertFormSubmodule d r).subtypeL

/-- The actual sphere tangent-gradient projection from the completed graph. -/
def formGradient (d : ℕ) (r : ℝ) :
    HilbertFormSpace d r →L[ℝ] Lp (Ambient d) 2 (alignedMeasure d r) :=
  (WithLp.sndL 2 ℝ _ _).comp (hilbertFormSubmodule d r).subtypeL

def hilbertToClosed (d : ℕ) (r : ℝ) (p : HilbertFormSpace d r) :
    ClosedFormSpace d r := ⟨WithLp.ofLp p.1, p.2⟩

def closedToHilbert (d : ℕ) (r : ℝ) (p : ClosedFormSpace d r) :
    HilbertFormSpace d r := ⟨WithLp.toLp 2 p.1, p.2⟩

@[simp] theorem hilbertToClosed_closedToHilbert (d : ℕ) (r : ℝ)
    (p : ClosedFormSpace d r) :
    hilbertToClosed d r (closedToHilbert d r p) = p := rfl

@[simp] theorem closedToHilbert_hilbertToClosed (d : ℕ) (r : ℝ)
    (p : HilbertFormSpace d r) :
    closedToHilbert d r (hilbertToClosed d r p) = p := rfl

theorem form_norm_sq (d : ℕ) (r : ℝ) (p : HilbertFormSpace d r) :
    ‖p‖ ^ 2 = ‖formValue d r p‖ ^ 2 + ‖formGradient d r p‖ ^ 2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 p.1

/-- The original variance denominator on the centered Hilbert graph. -/
def formVariance (d : ℕ) (r : ℝ) (p : HilbertFormSpace d r) : ℝ :=
  ‖formValue d r p‖ ^ 2

/-- The original tangent-gradient energy on the completed Hilbert graph. -/
def formEnergy (d : ℕ) (r : ℝ) (p : HilbertFormSpace d r) : ℝ :=
  ‖formGradient d r p‖ ^ 2

def hilbertFormRayleigh (d : ℕ) (r : ℝ) (p : HilbertFormSpace d r) : ℝ :=
  formEnergy d r p / formVariance d r p

def hilbertFormRayleighValues (d : ℕ) (r : ℝ) : Set ℝ :=
  {q | ∃ p : HilbertFormSpace d r,
    0 < formVariance d r p ∧ q = hilbertFormRayleigh d r p}

def hilbertFormGap (d : ℕ) (r : ℝ) : ℝ :=
  sInf (hilbertFormRayleighValues d r)

theorem hilbertFormRayleigh_eq_closed (d : ℕ) (r : ℝ)
    (p : HilbertFormSpace d r) :
    hilbertFormRayleigh d r p =
      closedFormRayleigh d r (hilbertToClosed d r p) := rfl

theorem hilbertFormRayleighValues_eq_closed (d : ℕ) (r : ℝ) :
    hilbertFormRayleighValues d r = closedFormRayleighValues d r := by
  ext q
  constructor
  · rintro ⟨p, hp, hq⟩
    exact ⟨hilbertToClosed d r p, hp, hq⟩
  · rintro ⟨p, hp, hq⟩
    exact ⟨closedToHilbert d r p, hp, hq⟩

/-- Changing to the actual Hilbert graph norm preserves exactly the
global physical smooth-core infimum. -/
theorem hilbertFormGap_eq_coreGap (d : ℕ) (r : ℝ) :
    hilbertFormGap d r = coreGap d r := by
  unfold hilbertFormGap
  rw [hilbertFormRayleighValues_eq_closed]
  exact closedFormGap_eq_coreGap d r

private def constantOne (d : ℕ) (r : ℝ) : Lp ℝ 2 (alignedMeasure d r) := by
  letI : IsProbabilityMeasure (alignedMeasure d r) := alignedMeasure_probability d r
  exact (memLp_const (1 : ℝ)).toLp (fun _ => 1)

private theorem coreGraph_centered_inner (d : ℕ) (r : ℝ)
    (f : SphereC1Core d) :
    inner ℝ (constantOne d r) (coreGraph d r f).1 = 0 := by
  letI : IsProbabilityMeasure (alignedMeasure d r) := alignedMeasure_probability d r
  rw [L2.inner_def]
  have hone : (constantOne d r : SpherePoint d → ℝ) =ᵐ[alignedMeasure d r]
      (fun _ => 1) := (memLp_const (1 : ℝ)).coeFn_toLp
  have hval : ((coreGraph d r f).1 : SpherePoint d → ℝ) =ᵐ[alignedMeasure d r]
      centeredCoreValue d r f := (centeredCoreValue_memLp d r f).coeFn_toLp
  have hcongr : (fun x => inner ℝ (constantOne d r x) ((coreGraph d r f).1 x))
      =ᵐ[alignedMeasure d r] centeredCoreValue d r f := by
    filter_upwards [hone, hval] with x hx hy
    rw [hx, hy]
    change centeredCoreValue d r f x * 1 = centeredCoreValue d r f x
    exact mul_one _
  rw [integral_congr_ae hcongr]
  unfold centeredCoreValue
  rw [integral_sub ((coreValue_memLp d r f).integrable (by norm_num))
    (integrable_const _)]
  simp

/-- Completion preserves centering: every value is orthogonal to constants
in the original physical `L²` space. -/
theorem formValue_orthogonal_constants (d : ℕ) (r : ℝ)
    (p : HilbertFormSpace d r) :
    inner ℝ (constantOne d r) (formValue d r p) = 0 := by
  let S : Set (Lp ℝ 2 (alignedMeasure d r) ×
    Lp (Ambient d) 2 (alignedMeasure d r)) :=
      {q | inner ℝ (constantOne d r) q.1 = 0}
  have hclosed : IsClosed S :=
    isClosed_eq (continuous_const.inner continuous_fst) continuous_const
  have hsubset : Set.range (coreGraph d r) ⊆ S := by
    rintro _ ⟨f, rfl⟩
    exact coreGraph_centered_inner d r f
  have hp : WithLp.ofLp p.1 ∈ closedFormGraph d r := p.2
  exact (closure_minimal hsubset hclosed) hp

end

end DFL.Spectral
