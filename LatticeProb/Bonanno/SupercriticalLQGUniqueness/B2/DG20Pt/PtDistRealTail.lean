/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRealTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenMeasurable
import LatticeProb.Bonanno.LQGMetric.Prob.Quantile

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_measurable_real_upper_tail_small
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Measurable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ P {ω | M < f ω} ≤ ENNReal.ofReal ε := by
  let μ : Measure ℝ := P.map f
  have ht := LQGMetric.tendsto_measure_Ioi_atTop_zero (μ := μ)
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1
    (ht.eventually (eventually_lt_nhds hε'))
  let M : ℝ := max 1 M₀
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨M, hM, ?_⟩
  have hμ : μ (Ioi M) < ENNReal.ofReal ε := hM₀ M (le_max_right _ _)
  have heq : P {ω | M < f ω} = μ (Ioi M) := by
    change P (f ⁻¹' Ioi M) = (P.map f) (Ioi M)
    exact (Measure.map_apply hf measurableSet_Ioi).symm
  rw [heq]
  exact hμ.le

end SupercriticalLQGUniqueness.B2.DG20Pt
