import Mathlib.Basic.Real.Pointwise
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The infimum of a set of nonnegative reals defined by a threshold condition

For a predicate `P` on `ℝ`, the infimum `sInf {m | 0 ≤ m ∧ P m}` is the smallest threshold at which a
monotone quantity (a distribution function, a hitting probability) reaches a level.  Two elementary
facts are needed for medians and quantiles of nonnegative variables:

* `LatticeProb.sInf_setOf_nonneg_comp_mul`: changing the scale, `sInf {m | 0 ≤ m ∧ P (c * m)} =
  sInf {m | 0 ≤ m ∧ P m} / c` for `c > 0`;
* `LatticeProb.measurable_sInf_setOf_nonneg`: if the predicates `P ω` are upward closed (`P ω m` and
  `m ≤ m'` imply `P ω m'`) and `ω ↦ P ω q` is measurable for every rational `q`, then
  `ω ↦ sInf {m | 0 ≤ m ∧ P ω m}` is measurable (the convention `sInf ∅ = 0` is the one of `ℝ`).

For a distribution function `F` and a level `a`, `P m := a ≤ F m` is upward closed as soon as `F` is
monotone, so the median (`a = 1/2`) of a measurable family of distribution functions is measurable and
the median of `x ↦ F (c * x)` is the median of `F` divided by `c`.
-/

open MeasureTheory Set
open scoped Pointwise

namespace LatticeProb

/-- Scaling the argument by `c > 0` divides the infimum of a threshold set of nonnegative reals by
`c`: `inf {m ≥ 0 | P (c m)} = (inf {m ≥ 0 | P m}) / c`. -/
theorem sInf_setOf_nonneg_comp_mul (P : ℝ → Prop) {c : ℝ} (hc : 0 < c) :
    sInf {m : ℝ | 0 ≤ m ∧ P (c * m)} = sInf {m : ℝ | 0 ≤ m ∧ P m} / c := by
  have hset : {m : ℝ | 0 ≤ m ∧ P (c * m)} = c⁻¹ • {m : ℝ | 0 ≤ m ∧ P m} := by
    ext m
    simp only [mem_ofPred_eq, mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨h0, hP⟩
      exact ⟨c * m, ⟨mul_nonneg hc.le h0, hP⟩, by field_simp⟩
    · rintro ⟨s, ⟨hs0, hs⟩, rfl⟩
      refine ⟨mul_nonneg (inv_nonneg.2 hc.le) hs0, ?_⟩
      rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [hset, Real.sInf_smul_of_nonneg (inv_nonneg.2 hc.le), smul_eq_mul, div_eq_inv_mul]

/-- The infimum of the threshold set `{m ≥ 0 | P ω m}` of upward closed predicates is a measurable
function of `ω` as soon as the events `{ω | P ω q}`, `q` rational, are measurable. -/
theorem measurable_sInf_setOf_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Ω → ℝ → Prop}
    (hup : ∀ ω m m', m ≤ m' → P ω m → P ω m')
    (hmeas : ∀ q : ℚ, MeasurableSet {ω | P ω q}) :
    Measurable fun ω => sInf {m : ℝ | 0 ≤ m ∧ P ω m} := by
  refine measurable_of_Iio fun a => ?_
  have key : ∀ ω, sInf {m : ℝ | 0 ≤ m ∧ P ω m} < a ↔
      (∃ q : ℚ, ((q : ℝ) < a ∧ 0 ≤ (q : ℝ)) ∧ P ω q) ∨
        ((∀ q : ℚ, ¬ (0 ≤ (q : ℝ) ∧ P ω q)) ∧ 0 < a) := by
    intro ω
    by_cases hne : ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ P ω q
    · have hS : ({m : ℝ | 0 ≤ m ∧ P ω m}).Nonempty := by
        obtain ⟨q, hq⟩ := hne
        exact ⟨q, hq⟩
      constructor
      · intro h
        obtain ⟨s, ⟨hs0, hs⟩, hsa⟩ := exists_lt_of_csInf_lt hS h
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hsa
        exact Or.inl ⟨q, ⟨hq2, hs0.trans hq1.le⟩, hup ω s q hq1.le hs⟩
      · rintro (⟨q, ⟨hqa, hq0⟩, hq⟩ | ⟨hall, -⟩)
        · exact lt_of_le_of_lt (csInf_le ⟨0, fun m hm => hm.1⟩ ⟨hq0, hq⟩) hqa
        · obtain ⟨q, hq⟩ := hne
          exact absurd hq (hall q)
    · have hS : {m : ℝ | 0 ≤ m ∧ P ω m} = ∅ := by
        refine eq_empty_of_forall_notMem fun m hm => ?_
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_one m)
        exact hne ⟨q, hm.1.trans hq1.le, hup ω m q hq1.le hm.2⟩
      rw [hS, Real.sInf_empty]
      constructor
      · exact fun h => Or.inr ⟨fun q hq => hne ⟨q, hq⟩, h⟩
      · rintro (⟨q, ⟨-, hq0⟩, hq⟩ | ⟨-, h⟩)
        · exact absurd ⟨q, hq0, hq⟩ hne
        · exact h
  have hset : (fun ω => sInf {m : ℝ | 0 ≤ m ∧ P ω m}) ⁻¹' Iio a =
      (⋃ q : ℚ, {ω | ((q : ℝ) < a ∧ 0 ≤ (q : ℝ)) ∧ P ω q}) ∪
        ((⋂ q : ℚ, {ω | ¬ (0 ≤ (q : ℝ) ∧ P ω q)}) ∩ {_ω | 0 < a}) := by
    ext ω
    simp only [mem_preimage, mem_Iio, key, mem_union, mem_iUnion, mem_ofPred_eq, mem_inter_iff,
      mem_iInter]
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.iUnion fun q => ?_)
    (MeasurableSet.inter (MeasurableSet.iInter fun q => ?_) (MeasurableSet.const _))
  · exact (MeasurableSet.const _).inter (hmeas q)
  · exact ((MeasurableSet.const _).inter (hmeas q)).compl

end LatticeProb
