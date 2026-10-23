import LatticeProb.Prob.HoeffdingSeries.OsForm
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Hoeffding bounds for absolutely summable countable families

Absolute summability gives a pointwise sum on every path. A sequence of finite subsets
exhausting the index type passes the finite sub-Gaussian estimates to this sum by Fatou.
This includes finite and empty index types and has the same universal constant two.
-/

namespace LatticeProb

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℝ} {a : ι → ℝ}

omit [Countable ι] [MeasurableSpace Ω] in
/-- Absolutely summable real coefficients have summable squares. -/
theorem summable_sq_of_summable_real (ha : Summable a) : Summable (fun i => a i ^ 2) := by
  have hprod := ha.abs.mul_of_nonneg ha.abs (fun i => abs_nonneg (a i))
    (fun i => abs_nonneg (a i))
  have hdiag := hprod.comp_injective (show Function.Injective (fun i : ι => (i, i)) from
    fun _ _ h => (Prod.mk.inj h).1)
  simpa only [Function.comp_def, ← pow_two, sq_abs] using hdiag

omit [Countable ι] [MeasurableSpace Ω] in
/-- A bounded family with absolutely summable weights is summable on every path. -/
theorem summable_weighted_of_abs_le_one (ha : Summable a)
    (hb : ∀ i ω, |X i ω| ≤ 1) (ω : Ω) : Summable (fun i => a i * X i ω) := by
  apply ha.abs.of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul_of_nonneg_left (hb i ω) (abs_nonneg (a i))).trans_eq (mul_one _)

omit [IsProbabilityMeasure P] in
/-- The pointwise weighted countable sum of measurable real variables is measurable. -/
theorem measurable_weighted_tsum (hm : ∀ i, Measurable (X i)) (a : ι → ℝ) :
    Measurable (fun ω => ∑' i, a i * X i ω) :=
  Measurable.tsum (fun i => measurable_const.mul (hm i))

/-- An absolutely summable countable family has sub-Gaussian parameter its square-sum. -/
theorem hasSubgaussianMGF_weighted_tsum (hm : ∀ i, Measurable (X i))
    (hi : iIndepFun X P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hb : ∀ i ω, |X i ω| ≤ 1) (ha : Summable a) :
    HasSubgaussianMGF (fun ω => ∑' i, a i * X i ω)
      ⟨∑' i, a i ^ 2, tsum_nonneg (fun i => sq_nonneg (a i))⟩ P := by
  classical
  obtain ⟨s, hs⟩ := exists_seq_tendsto (atTop : Filter (Finset ι))
  have hind : iIndepFun (fun i ω => a i * X i ω) P :=
    hi.comp (fun i x => a i * x) (fun _ => measurable_const.mul measurable_id)
  have hfinite N : HasSubgaussianMGF (fun ω => ∑ i ∈ s N, a i * X i ω)
      (∑ i ∈ s N, (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)) P := by
    apply HasSubgaussianMGF.sum_of_iIndepFun hind
    intro i _
    simpa using (hasSubgaussianMGF_of_abs_le_one (hm i) (hc i)
      (ae_of_all _ (hb i))).const_mul (a i)
  apply hasSubgaussianMGF_of_ae_tendsto hfinite
  · intro N
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum]
    exact (summable_sq_of_summable_real ha).sum_le_tsum (s N) (fun i _ => sq_nonneg (a i))
  · exact ae_of_all _ (fun ω =>
      (summable_weighted_of_abs_le_one ha hb ω).hasSum.comp hs)

/-- Countable Hoeffding tail estimate, including zero square-sum and finite index types. -/
theorem measure_abs_weighted_tsum_ge_le (hm : ∀ i, Measurable (X i))
    (hi : iIndepFun X P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hb : ∀ i ω, |X i ω| ≤ 1) (ha : Summable a) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |∑' i, a i * X i ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ∑' i, a i ^ 2))) :=
  measure_abs_ge_le_of_hasSubgaussianMGF (hasSubgaussianMGF_weighted_tsum hm hi hc hb ha) ht

/-- Countable Hoeffding O₂ estimate with the same constant two as the natural-index result. -/
theorem osBound_abs_weighted_tsum (hm : ∀ i, Measurable (X i))
    (hi : iIndepFun X P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hb : ∀ i ω, |X i ω| ≤ 1) (ha : Summable a) :
    OsBound P 2 (2 * Real.sqrt (∑' i, a i ^ 2)) (fun ω => |∑' i, a i * X i ω|) :=
  osBound_abs_of_hasSubgaussianMGF (hasSubgaussianMGF_weighted_tsum hm hi hc hb ha)

/-- A universal constant controls every absolutely summable countable independent family. -/
theorem hoeffding_countable :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (a : ι → ℝ),
      (∀ i, Measurable (X i)) → iIndepFun X P →
      (∀ i, ∫ ω, X i ω ∂P = 0) → (∀ i ω, |X i ω| ≤ 1) → Summable a →
      Measurable (fun ω => ∑' i, a i * X i ω) ∧
        OsBound P 2 (C * Real.sqrt (∑' i, a i ^ 2)) (fun ω => |∑' i, a i * X i ω|) ∧
        ∀ t : ℝ, 0 ≤ t → P {ω | t ≤ |∑' i, a i * X i ω|} ≤
          ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ∑' i, a i ^ 2))) := by
  refine ⟨2, by norm_num, ?_⟩
  intro ι Ω _ _ P _ X a hm hi hc hb ha
  exact ⟨measurable_weighted_tsum hm a, osBound_abs_weighted_tsum hm hi hc hb ha,
    fun _ ht => measure_abs_weighted_tsum_ge_le hm hi hc hb ha ht⟩

end LatticeProb
