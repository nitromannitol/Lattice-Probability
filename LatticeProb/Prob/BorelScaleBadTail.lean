import LatticeProb.Bonanno.LQGMetric.Meas.UM
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Tails of Borel scale events -/

open MeasureTheory Filter Set Topology

namespace LatticeProb

/-- Environments with a bad positive scale at most the given threshold. -/
def borelScaleBadTail {E : Type*} (B : Set (E × ℝ)) (a : ℝ) : Set E :=
  {x | ∃ r, (x, r) ∈ B ∧ 0 < r ∧ r ≤ a}

/-- Projecting a Borel relation gives a universally measurable bad-scale tail. -/
theorem uMeasurableSet_borelScaleBadTail {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] (B : Set (E × ℝ)) (a : ℝ) (hB : MeasurableSet B) :
    LQGMetric.UMeasurableSet (borelScaleBadTail B a) := by
  have h : MeasurableSet {p : E × ℝ | p ∈ B ∧ 0 < p.2 ∧ p.2 ≤ a} :=
    hB.inter ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))
  exact LQGMetric.UMeasurableSet.setOf_exists h

/-- Almost-sure eventual absence of bad scales gives vanishing tail probabilities. -/
theorem tendsto_measure_borelScaleBadTail {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] (ν : Measure E) [IsFiniteMeasure ν]
    (B : Set (E × ℝ)) (hB : MeasurableSet B) (a : ℕ → ℝ) (ha : Antitone a)
    (hgood : ∀ᵐ x ∂ν, ∃ n, ∀ r, (x, r) ∈ B → 0 < r → r ≤ a n → False) :
    Tendsto (fun n => ν (borelScaleBadTail B (a n))) atTop (𝓝 0) := by
  have hm : ∀ n, NullMeasurableSet (borelScaleBadTail B (a n)) ν :=
    fun n => (uMeasurableSet_borelScaleBadTail B (a n) hB) ν inferInstance
  have hant : Antitone (fun n => borelScaleBadTail B (a n)) := by
    intro i j hij x hx
    obtain ⟨r, hr, hr0, hrj⟩ := hx
    exact ⟨r, hr, hr0, hrj.trans (ha hij)⟩
  have hnull : ν (⋂ n, borelScaleBadTail B (a n)) = 0 := by
    apply measure_mono_null _ (ae_iff.mp hgood)
    intro x hx hg
    obtain ⟨n, hn⟩ := hg
    obtain ⟨r, hr, hr0, hra⟩ := mem_iInter.mp hx n
    exact hn r hr hr0 hra
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (s := fun n => borelScaleBadTail B (a n)) hm hant ⟨0, measure_ne_top ν _⟩
  simpa only [hnull, Function.comp_def] using h

/-- A small random scale and null-measurable bad tails yield a vanishing
failure probability without assuming independence. -/
theorem tendsto_measure_failure_of_nullMeasurable_badTail
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (ν : Measure E) (l : Filter ι)
    (X : ι → Ω → E) (R : ι → Ω → ℝ) (A : ι → Set Ω)
    (T : ℕ → Set E) (a : ℕ → ℝ)
    (hT : ∀ k, NullMeasurableSet (T k) ν)
    (hX : ∀ i, AEMeasurable (X i) P)
    (hlaw : ∀ i, Measure.map (X i) P = ν)
    (hscale : ∀ k, Tendsto (fun i => P {ω | a k < R i ω}) l (𝓝 0))
    (htail : Tendsto (fun k => ν (T k)) atTop (𝓝 0))
    (hcover : ∀ i k, A i ⊆ {ω | a k < R i ω} ∪ (X i) ⁻¹' T k) :
    Tendsto (fun i => P (A i)) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_nhds_zero.1 htail _ he2).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (hscale k) _ he2] with i hi
  calc
    P (A i) ≤ P {ω | a k < R i ω} + P ((X i) ⁻¹' T k) :=
      (measure_mono (hcover i k)).trans (measure_union_le _ _)
    _ = P {ω | a k < R i ω} + ν (T k) := by
      rw [← hlaw i, Measure.map_apply₀ (hX i) (by simpa only [hlaw i] using hT k)]
    _ ≤ e / 2 + e / 2 := add_le_add hi hk
    _ = e := ENNReal.add_halves e

end LatticeProb
