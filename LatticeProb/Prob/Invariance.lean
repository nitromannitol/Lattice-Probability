/-
Sub-invariant functions are invariant.

If `T` preserves a probability (or finite) measure `μ` and `f : Ω → ℝ≥0∞` is measurable with
`f ≤ f ∘ T` a.e., then `f ∘ T = f` a.e. (`ae_eq_comp_of_ae_le_comp`). Real-valued corollary
(`ae_eq_comp_of_ae_le_comp_real`) via the strictly monotone embedding
`t ↦ ENNReal.ofReal (Real.exp t)`, and the ergodic corollary (`ae_eq_const_of_ae_le_comp_real`):
for ergodic `T`, such an `f` is a.e. constant (Mathlib `Ergodic.ae_eq_const_of_ae_eq_comp₀`).

Route. For each rational level `q`, the superlevel set `U q = {f > q}` satisfies
`U q ⊆ T⁻¹ (U q)` a.e. (since `f ≤ f ∘ T`) and `μ (T⁻¹ U q) = μ (U q)` (measure preservation),
so `U q =ᵐ T⁻¹ (U q)` (Mathlib `ae_eq_of_ae_subset_of_measure_ge`, finite measure). Countably
many `q`: a.e. `x` has `q < f x ↔ q < f (T x)` for all rational `q ≥ 0`, which forces
`f x = f (T x)` (`ENNReal.lt_iff_exists_rat_btwn`).

No ergodicity and no integrability is needed for the invariance; the target `ℝ≥0∞` handles `∞`.

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/
import Mathlib

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The rational levels used below: `(Real.toNNReal q : ℝ≥0∞)` for `q : ℚ`. -/
private noncomputable def ratLevel (q : ℚ) : ℝ≥0∞ := ((Real.toNNReal q : NNReal) : ℝ≥0∞)

/-- The superlevel set `{f > c}` is a.e. contained in its preimage under `T`, from `f ≤ f ∘ T`. -/
private theorem ae_subset_preimage_superlevel {μ : Measure Ω} {T : Ω → Ω} {f : Ω → ℝ≥0∞}
    (hle : f ≤ᵐ[μ] f ∘ T)
    (c : ℝ≥0∞) :
    {x | c < f x} ≤ᵐ[μ] T ⁻¹' {x | c < f x} := by
  filter_upwards [hle] with x hx hc
  exact lt_of_lt_of_le hc hx

/-- The superlevel set `{f > c}` a.e. equals its preimage under a measure-preserving `T`. -/
private theorem ae_eq_preimage_superlevel {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ≥0∞} (hf : Measurable f) (hle : f ≤ᵐ[μ] f ∘ T)
    (c : ℝ≥0∞) :
    {x | c < f x} =ᵐ[μ] T ⁻¹' {x | c < f x} := by
  set s : Set Ω := {x | c < f x} with hs
  have hsub : s ≤ᵐ[μ] T ⁻¹' s := ae_subset_preimage_superlevel (μ := μ) (T := T) hle c
  have hsmeas : MeasurableSet s := measurableSet_lt measurable_const hf
  have hnull : NullMeasurableSet s μ := hsmeas.nullMeasurableSet
  have hmp : μ (T ⁻¹' s) = μ s := hT.measure_preimage hnull
  exact ae_eq_of_ae_subset_of_measure_ge hsub (le_of_eq hmp) hnull (measure_ne_top μ (T ⁻¹' s))

/-- A.e., `f x` and `f (T x)` sit on the same side of every rational level `ratLevel q`. -/
private theorem ae_forall_ratLevel_lt_iff_comp {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ≥0∞} (hf : Measurable f) (hle : f ≤ᵐ[μ] f ∘ T) :
    ∀ᵐ x ∂μ, ∀ q : ℚ, (ratLevel q < f x ↔ ratLevel q < f (T x)) := by
  rw [ae_all_iff]
  intro q
  filter_upwards [ae_eq_preimage_superlevel hT hf hle (ratLevel q)] with x hx
  exact iff_of_eq hx

/-- Two values of `f` agreeing against every rational level, with `a ≤ b`, are equal. -/
private theorem eq_of_forall_ratLevel_lt_iff {a b : ℝ≥0∞} (hab : a ≤ b)
    (h : ∀ q : ℚ, (ratLevel q < a ↔ ratLevel q < b)) :
    a = b := by
  by_contra hne
  have hlt : a < b := lt_of_le_of_ne hab hne
  obtain ⟨q, hq0, haq, hqb⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  have haq' : a < ratLevel q := haq
  have hqb' : ratLevel q < b := hqb
  exact (lt_asymm haq') ((h q).2 hqb')

/-- **Sub-invariant functions are invariant** (values in `ℝ≥0∞`). -/
theorem ae_eq_comp_of_ae_le_comp (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Ω → ℝ≥0∞) (hf : Measurable f)
    (hle : f ≤ᵐ[μ] f ∘ T) : f ∘ T =ᵐ[μ] f := by
  filter_upwards [ae_forall_ratLevel_lt_iff_comp hT hf hle, hle] with x hx hxle
  exact (eq_of_forall_ratLevel_lt_iff hxle hx).symm

/-! ### Real-valued and ergodic corollaries -/

/-- The strictly monotone measurable embedding `ℝ → ℝ≥0∞` used for the real corollary. -/
private noncomputable def embR (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp t)

/-- `embR` is monotone: `embR s ≤ embR t ↔ s ≤ t`. -/
private theorem embR_le_embR_iff {s t : ℝ} : embR s ≤ embR t ↔ s ≤ t := by
  simp only [embR, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos t).le, Real.exp_le_exp]

/-- `embR` is measurable. -/
private theorem measurable_embR : Measurable embR := by
  unfold embR
  exact ENNReal.measurable_ofReal.comp Real.measurable_exp

/-- Real-valued corollary of `ae_eq_comp_of_ae_le_comp`: a sub-invariant real-valued function is
invariant a.e. -/
theorem ae_eq_comp_of_ae_le_comp_real (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Ω → ℝ) (hf : Measurable f)
    (hle : f ≤ᵐ[μ] f ∘ T) : f ∘ T =ᵐ[μ] f := by
  have hmeas : Measurable (fun x => embR (f x)) := measurable_embR.comp hf
  have hleE : ∀ᵐ x ∂μ, embR (f x) ≤ embR (f (T x)) :=
    hle.mono fun x hx => embR_le_embR_iff.mpr hx
  have hmain := ae_eq_comp_of_ae_le_comp μ T hT (fun x => embR (f x)) hmeas hleE
  exact hmain.mono fun x hx => le_antisymm (embR_le_embR_iff.mp hx.le) (embR_le_embR_iff.mp hx.ge)

/-- For ergodic `T`, a measurable real function with `f ≤ f ∘ T` a.e. is a.e. constant. -/
theorem ae_eq_const_of_ae_le_comp_real (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (herg : Ergodic T μ) (f : Ω → ℝ) (hf : Measurable f) (hle : f ≤ᵐ[μ] f ∘ T) :
    ∃ c : ℝ, f =ᵐ[μ] Function.const Ω c :=
  herg.ae_eq_const_of_ae_eq_comp₀ hf.nullMeasurable
    (ae_eq_comp_of_ae_le_comp_real μ T herg.toMeasurePreserving f hf hle)

end LatticeProb
