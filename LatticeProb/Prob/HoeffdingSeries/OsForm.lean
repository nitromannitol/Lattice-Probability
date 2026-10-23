import LatticeProb.Prob.HoeffdingSeries.Tail
import LatticeProb.Prob.StochasticO

/-!
# Infinite Hoeffding inequality in stochastic O₂ notation

The Gaussian tail yields the universal constant two. The zero square-sum case is
handled by almost sure vanishing, so no positive variance assumption is needed.
-/

namespace LatticeProb

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- An almost surely zero variable satisfies a zero-scale stochastic bound. -/
theorem osBound_abs_zero_of_ae_eq_zero {Y : Ω → ℝ} (hY : Y =ᵐ[P] 0) (s : ℝ) :
    OsBound P s 0 (fun ω => |Y ω|) := by
  intro t _
  have hz : P {ω | t * 0 < max |Y ω| 0} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hY] with ω hω
    simp only [hω, Pi.zero_apply, abs_zero, max_self, mul_zero, lt_self_iff_false,
      not_false_eq_true]
  rw [hz]
  exact bot_le

/-- A sub-Gaussian variable has an O₂ bound at twice the square root of its parameter. -/
theorem osBound_abs_of_hasSubgaussianMGF {Y : Ω → ℝ} {c : ℝ≥0}
    (hY : HasSubgaussianMGF Y c P) :
    OsBound P 2 (2 * Real.sqrt c) (fun ω => |Y ω|) := by
  by_cases hc : c = 0
  · subst c
    simpa only [NNReal.coe_zero, Real.sqrt_zero, mul_zero] using
      osBound_abs_zero_of_ae_eq_zero hY.ae_eq_zero_of_hasSubgaussianMGF_zero 2
  · apply osBound_abs_of_gaussian_tail (Real.sqrt_pos.mpr (NNReal.coe_pos.mpr
      (pos_iff_ne_zero.mpr hc)))
    intro t ht
    rw [Real.sq_sqrt c.coe_nonneg]
    exact measure_abs_ge_le_of_hasSubgaussianMGF hY ht.le

/-- The infinite Hoeffding series satisfies the paper's O₂ bound with constant two. -/
theorem osBound_abs_seriesLimit {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hm : ∀ n, Measurable (X n)) (hi : iIndepFun X P)
    (hc : ∀ n, ∫ ω, X n ω ∂P = 0) (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (ha : Summable (fun n => a n ^ 2)) :
    OsBound P 2 (2 * Real.sqrt (∑' n, a n ^ 2)) (fun ω => |seriesLimit X a ω|) := by
  by_cases hz : (∑' n, a n ^ 2) = 0
  · rw [hz, Real.sqrt_zero, mul_zero]
    exact osBound_abs_zero_of_ae_eq_zero
      (seriesLimit_ae_eq_zero_of_tsum_sq_eq_zero hm hi hc hb ha hz) 2
  · exact osBound_abs_of_hasSubgaussianMGF (hasSubgaussianMGF_seriesLimit hm hi hc hb ha)

/-- Independent centered bounded variables with square-summable weights converge almost
surely and in `L²`, with a universal O₂ bound on their limit. -/
theorem hoeffding_infinite :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → ℝ),
      (∀ n, Measurable (X n)) → iIndepFun X P →
      (∀ n, ∫ ω, X n ω ∂P = 0) → (∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) →
      Summable (fun n => a n ^ 2) →
      ∃ S : Ω → ℝ, MemLp S 2 P ∧
        (∀ᵐ ω ∂P, Tendsto (fun N => ∑ n ∈ Finset.range N, a n * X n ω) atTop
          (nhds (S ω))) ∧
        Tendsto (fun N => eLpNorm
          (fun ω => ∑ n ∈ Finset.range N, a n * X n ω - S ω) 2 P) atTop (nhds 0) ∧
        OsBound P 2 (C * Real.sqrt (∑' n, a n ^ 2)) (fun ω => |S ω|) := by
  refine ⟨2, by norm_num, ?_⟩
  intro Ω _ P _ X a hm hi hc hb ha
  exact ⟨seriesLimit X a, memLp_seriesLimit hm hi hc hb ha,
    ae_tendsto_seriesLimit hm hi hc hb ha,
    tendsto_eLpNorm_seriesPartialSum_sub_limit hm hi hc hb ha,
    osBound_abs_seriesLimit hm hi hc hb ha⟩

end LatticeProb
