import LatticeProb.Prob.BorelScaleBadTail

/-! # Scale tails with measurable witness codes -/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace LatticeProb

/-- Environments admitting a bad positive scale and a witness below a threshold. -/
def witnessScaleBadTail {E W : Type*} (B : Set (E × (ℝ × W))) (a : ℝ) : Set E :=
  {x | ∃ r w, (x, r, w) ∈ B ∧ 0 < r ∧ r ≤ a}

/-- A Borel witness relation has a universally measurable scale tail. -/
theorem uMeasurableSet_witnessScaleBadTail {E W : Type*}
    [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace W] [StandardBorelSpace W]
    (B : Set (E × (ℝ × W))) (a : ℝ) (hB : MeasurableSet B) :
    LQGMetric.UMeasurableSet (witnessScaleBadTail B a) := by
  have h : MeasurableSet {p : E × (ℝ × W) | p ∈ B ∧ 0 < p.2.1 ∧ p.2.1 ≤ a} :=
    hB.inter ((measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
      (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const))
  convert LQGMetric.UMeasurableSet.setOf_exists h using 1
  ext x
  constructor
  · rintro ⟨r, w, hr, hr0, hra⟩
    exact ⟨(r, w), hr, hr0, hra⟩
  · rintro ⟨⟨r, w⟩, hr, hr0, hra⟩
    exact ⟨r, w, hr, hr0, hra⟩

/-- Almost-sure eventual absence of witnesses gives vanishing scale-tail probabilities. -/
theorem tendsto_measure_witnessScaleBadTail {E W : Type*}
    [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace W] [StandardBorelSpace W]
    (ν : Measure E) [IsFiniteMeasure ν] (B : Set (E × (ℝ × W)))
    (hB : MeasurableSet B) (a : ℕ → ℝ) (ha : Antitone a)
    (hgood : ∀ᵐ x ∂ν, ∃ n, ∀ r w, (x, r, w) ∈ B → 0 < r → r ≤ a n → False) :
    Tendsto (fun n => ν (witnessScaleBadTail B (a n))) atTop (𝓝 0) := by
  have hm : ∀ n, NullMeasurableSet (witnessScaleBadTail B (a n)) ν :=
    fun n => (uMeasurableSet_witnessScaleBadTail B (a n) hB) ν inferInstance
  have hant : Antitone (fun n => witnessScaleBadTail B (a n)) := by
    intro i j hij x hx
    obtain ⟨r, w, hr, hr0, hrj⟩ := hx
    exact ⟨r, w, hr, hr0, hrj.trans (ha hij)⟩
  have hnull : ν (⋂ n, witnessScaleBadTail B (a n)) = 0 := by
    apply measure_mono_null _ (ae_iff.mp hgood)
    intro x hx hg
    obtain ⟨n, hn⟩ := hg
    obtain ⟨r, w, hr, hr0, hra⟩ := mem_iInter.mp hx n
    exact hn r w hr hr0 hra
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (s := fun n => witnessScaleBadTail B (a n)) hm hant ⟨0, measure_ne_top ν _⟩
  simpa only [hnull, Function.comp_def] using h

end LatticeProb
