import LatticeProb.Prob.AreaCurveConditionMeasurable
import LatticeProb.Prob.FiniteOnCompactsPart

/-! # Measurable mass-parametrized curves with locally finite measures -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Local finiteness is a measurable property of a measurable family of measures. -/
theorem measurableSet_isFiniteMeasureOnCompacts
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [WeaklyLocallyCompactSpace E] [SigmaCompactSpace E]
    {μ : Ω → Measure E} (hμ : Measurable μ) :
    MeasurableSet {ω | IsFiniteMeasureOnCompacts (μ ω)} := by
  have heq : {ω | IsFiniteMeasureOnCompacts (μ ω)} =
      ⋂ n : ℕ, {ω | μ ω (CompactExhaustion.choice E n) < ⊤} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h n
      let _ : IsFiniteMeasureOnCompacts (μ ω) := h
      exact ((CompactExhaustion.choice E).isCompact n).measure_lt_top
    · intro h
      exact ⟨fun K hK => by
        obtain ⟨n, hn⟩ := (CompactExhaustion.choice E).exists_superset_of_isCompact hK
        exact (measure_mono hn).trans_lt (h n)⟩
  rw [heq]
  exact MeasurableSet.iInter fun n => measurableSet_lt
    ((Measure.measurable_coe ((CompactExhaustion.choice E).isCompact n).isClosed.measurableSet).comp hμ)
    measurable_const

/-- Local finiteness and mass parametrization together form a measurable event. -/
theorem measurableSet_locallyFinite_curve_mass_parametrized
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [WeaklyLocallyCompactSpace E]
    [SigmaCompactSpace E] {μ : Ω → Measure E} (hμ : Measurable μ)
    {L : Ω → ℝ → E} (hLc : ∀ ω, Continuous (L ω))
    (hLm : ∀ t, Measurable fun ω => L ω t) :
    MeasurableSet {ω | IsFiniteMeasureOnCompacts (μ ω) ∧
      ∀ a b : ℝ, a ≤ b → μ ω (L ω '' Icc a b) = ENNReal.ofReal (b - a)} := by
  have hm := measurableSet_curve_mass_parametrized
    (measurable_finiteOnCompactsPart_comp hμ)
    (fun ω => isFiniteMeasureOnCompacts_finiteOnCompactsPart (μ ω)) hLc hLm
  have hf := measurableSet_isFiniteMeasureOnCompacts hμ
  convert hf.inter hm using 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨hfin, h⟩
    let _ : IsFiniteMeasureOnCompacts (μ ω) := hfin
    exact ⟨hfin, by simpa only [finiteOnCompactsPart_eq_self] using h⟩
  · rintro ⟨hfin, h⟩
    let _ : IsFiniteMeasureOnCompacts (μ ω) := hfin
    exact ⟨hfin, by simpa only [finiteOnCompactsPart_eq_self] using h⟩

end LatticeProb
