import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Measurable tails of open scale events -/

open MeasureTheory Filter Set Topology

namespace LatticeProb

/-- Environments with a bad scale strictly between zero and the threshold. -/
def openScaleBadTail {E : Type*} (B : E → Set ℝ) (a : ℝ) : Set E :=
  {x | ∃ r, r ∈ B x ∧ 0 < r ∧ r < a}

/-- Open scale sections reduce the continuum of witnesses to rational scales. -/
theorem measurableSet_openScaleBadTail {E : Type*} [MeasurableSpace E]
    (B : E → Set ℝ) (a : ℝ)
    (hopen : ∀ x, IsOpen (B x))
    (hmeas : ∀ q : ℚ, MeasurableSet {x | (q : ℝ) ∈ B x}) :
    MeasurableSet (openScaleBadTail B a) := by
  have heq : openScaleBadTail B a =
      ⋃ q : ℚ, if 0 < (q : ℝ) ∧ (q : ℝ) < a then {x | (q : ℝ) ∈ B x} else ∅ := by
    ext x
    simp only [openScaleBadTail, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨r, hr, hr0, hra⟩
      have ho : IsOpen (B x ∩ Ioo 0 a) := (hopen x).inter isOpen_Ioo
      obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open ho ⟨r, hr, hr0, hra⟩
      exact ⟨q, by simpa [hq.2.1, hq.2.2] using hq.1⟩
    · rintro ⟨q, hq⟩
      by_cases h : 0 < (q : ℝ) ∧ (q : ℝ) < a
      · exact ⟨q, by simpa [h] using hq, h.1, h.2⟩
      · simp only [h, ite_false, mem_empty_iff_false] at hq
  rw [heq]
  refine MeasurableSet.iUnion fun q => ?_
  split
  · exact hmeas q
  · exact MeasurableSet.empty

/-- Almost-sure eventual absence of bad scales gives vanishing tail probabilities. -/
theorem tendsto_measure_openScaleBadTail {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsFiniteMeasure ν] (B : E → Set ℝ) (a : ℕ → ℝ)
    (hopen : ∀ x, IsOpen (B x))
    (hmeas : ∀ q : ℚ, MeasurableSet {x | (q : ℝ) ∈ B x})
    (ha : Antitone a)
    (hgood : ∀ᵐ x ∂ν, ∃ n, ∀ r ∈ B x, 0 < r → r < a n → False) :
    Tendsto (fun n => ν (openScaleBadTail B (a n))) atTop (𝓝 0) := by
  have hm : ∀ n, MeasurableSet (openScaleBadTail B (a n)) :=
    fun n => measurableSet_openScaleBadTail B (a n) hopen hmeas
  have hant : Antitone (fun n => openScaleBadTail B (a n)) := by
    intro i j hij x hx
    obtain ⟨r, hr, hr0, hrj⟩ := hx
    exact ⟨r, hr, hr0, lt_of_lt_of_le hrj (ha hij)⟩
  have hnull : ν (⋂ n, openScaleBadTail B (a n)) = 0 := by
    apply measure_mono_null _ (ae_iff.mp hgood)
    intro x hx hg
    obtain ⟨n, hn⟩ := hg
    obtain ⟨r, hr, hr0, hra⟩ := mem_iInter.mp hx n
    exact hn r hr hr0 hra
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (s := fun n => openScaleBadTail B (a n)) (fun n => (hm n).nullMeasurableSet)
    hant ⟨0, measure_ne_top ν _⟩
  simpa only [hnull, Function.comp_def] using h

end LatticeProb
