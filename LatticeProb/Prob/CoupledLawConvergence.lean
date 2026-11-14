import LatticeProb.Prob.LevyProkhorovMaps
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Laws of nearby random variables

Random variables on a common probability space whose distance vanishes in probability have
laws whose Lévy–Prokhorov distance vanishes, even when both variables vary.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb

/-- A common coupling bounds the Lévy–Prokhorov distance of two laws by a radius at which
its bad-pair probability is at most that radius. -/
theorem levyProkhorovDist_map_le_of_coupled {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) {X Y : Ω → E} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (r : ℝ≥0) (hbad : P {ω | (r : ℝ≥0∞) ≤ edist (X ω) (Y ω)} ≤ r) :
    levyProkhorovDist (P.map X) (P.map Y) ≤ r := by
  have hset : MeasurableSet {p : E × E | (r : ℝ≥0∞) ≤ edist p.1 p.2} :=
    measurableSet_le measurable_const (continuous_fst.edist continuous_snd).measurable
  have h := levyProkhorovEDist_le_of_coupling (P.map X) (P.map Y)
    (P.map fun ω => (X ω, Y ω)) (Measure.fst_map_prodMk₀ hX hY)
    (Measure.snd_map_prodMk₀ hX hY) r (by
      rw [Measure.map_apply_of_aemeasurable (hX.prodMk hY) hset]
      exact hbad)
  change (levyProkhorovEDist (P.map X) (P.map Y)).toReal ≤ (r : ℝ)
  exact (ENNReal.toReal_mono (by simp) h).trans_eq (by simp)

/-- If two moving random variables are close in probability, their laws are close in
Lévy–Prokhorov distance. -/
theorem tendsto_levyProkhorovDist_map_of_coupled {Ω E ι : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) {l : Filter ι} {X Y : ι → Ω → E}
    (hX : ∀ i, AEMeasurable (X i) P) (hY : ∀ i, AEMeasurable (Y i) P)
    (hclose : ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun i => P {ω | ε ≤ edist (X i ω) (Y i ω)}) l (𝓝 0)) :
    Tendsto (fun i => levyProkhorovDist (P.map (X i)) (P.map (Y i))) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let r : ℝ≥0 := ⟨ε / 2, le_of_lt (half_pos hε)⟩
  have hr : (0 : ℝ≥0∞) < r := ENNReal.coe_pos.mpr (by exact half_pos hε)
  have hc := (hclose r hr).eventually (gt_mem_nhds hr)
  filter_upwards [hc] with i hi
  have hle := levyProkhorovDist_map_le_of_coupled P (hX i) (hY i) r hi.le
  have hnonneg : 0 ≤ levyProkhorovDist (P.map (X i)) (P.map (Y i)) :=
    ENNReal.toReal_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt hle (by change ε / 2 < ε; linarith)

end LatticeProb
