/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/SkorokhodMix.lean.
-/

import Mathlib.Probability.ConditionalProbability

/-!
# Skorokhod representation, step 2: the mixture laws of Billingsley's construction

Fix probability measures `P` (the limit) and `Q` (= `P_n`) on `S`, a finite measurable
partition `B 0, …, B k` of `S` and `ε ∈ (0, 1]` with `(1 - ε) P (B i) ≤ Q (B i)` for all `i`
(Billingsley (6.9)). With `Q(· | B i)` the conditional laws, the measure
`p = ε⁻¹ ∑ᵢ (Q (B i) - (1 - ε) P (B i)) Q(· | B i)` is a probability measure, and
`(1 - ε) ∑ᵢ P (B i) Q(A | B i) + ε p(A) = Q(A)`: a point chosen as "`Q(· | B i)` if
`X ∈ B i` (`X ∼ P`) with probability `1 - ε`, else `∼ p`" has law `Q`.

Source: Billingsley, *Convergence of Probability Measures*, 2nd ed. (1999), proof of
Theorem 6.7, p. 71 (definition of `p_n` and the computation of `P[X_n ∈ A]`). Billingsley
amalgamates the `P`-null cells into `B 0` so that `P_n(· | B i)` is defined; instead we set
`Q(· | B) := Q` when `Q B = 0` (`skCond`), which makes the amalgamation unnecessary.
-/

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal

namespace LatticeProb.Skorokhod

variable {S : Type*} [MeasurableSpace S]

/-- The conditional measure `Q(· | B)`, or `Q` itself when `Q B = 0`.

This is a convention, not the conditional measure: when `Q B = 0`, `skCond Q B` is `Q`.
Consumers that need the conditional law must argue with `Q B ≠ 0`. -/
noncomputable def skCond (Q : Measure S) (B : Set S) : Measure S :=
  if Q B = 0 then Q else Q[|B]

/-- `skCond Q B` is a probability measure whenever `Q` is one. -/
instance skCond_isProbabilityMeasure (Q : Measure S) [IsProbabilityMeasure Q] (B : Set S) :
    IsProbabilityMeasure (skCond Q B) := by
  unfold skCond; split_ifs with h
  · infer_instance
  · exact cond_isProbabilityMeasure h

/-- For measurable `B`, `Q B * skCond Q B A = Q (B ∩ A)`. This holds also when `Q B = 0`,
which is what makes the convention `skCond Q B = Q` harmless. -/
lemma skCond_mul (Q : Measure S) [IsFiniteMeasure Q] {B : Set S} (hB : MeasurableSet B)
    (A : Set S) : Q B * skCond Q B A = Q (B ∩ A) := by
  unfold skCond; split_ifs with h
  · rw [h, zero_mul, measure_mono_null inter_subset_left h]
  · rw [mul_comm, cond_mul_eq_inter hB]

/-- If `Q B ≠ 0`, the conditional measure `Q(· | B)` gives no mass to the complement `Bᶜ`. -/
lemma skCond_compl (Q : Measure S) {B : Set S} (hB : MeasurableSet B) (h : Q B ≠ 0) :
    skCond Q B Bᶜ = 0 := by
  simp [skCond, h, cond_apply hB]

/-- A finite measurable partition `B 0, …, B k` of `S` (cells beyond `k` are empty). -/
structure IsSkPartition (B : ℕ → Set S) (k : ℕ) : Prop where
  meas : ∀ i, MeasurableSet (B i)
  disj : Pairwise (Disjoint on B)
  cover : (⋃ i, B i) = univ
  empty : ∀ i, k < i → B i = ∅

/-- Every point of `S` lies in one of the cells `B 0, …, B k`. -/
lemma IsSkPartition.exists_mem {B : ℕ → Set S} {k : ℕ} (hB : IsSkPartition B k) (x : S) :
    ∃ i ≤ k, x ∈ B i := by
  have hx : x ∈ ⋃ i, B i := hB.cover ▸ mem_univ x
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  refine ⟨i, ?_, hi⟩
  by_contra h
  rw [hB.empty i (not_le.1 h)] at hi
  exact hi

/-- For a measurable set `A` and any measure `μ`, the pieces `μ (B i ∩ A)` for `i ≤ k`
add up to `μ A`. -/
lemma IsSkPartition.sum_measure_inter {B : ℕ → Set S} {k : ℕ} (hB : IsSkPartition B k)
    (μ : Measure S) {A : Set S} (hA : MeasurableSet A) :
    ∑ i ∈ Finset.range (k + 1), μ (B i ∩ A) = μ A := by
  rw [← measure_biUnion_finset (fun i _ j _ hij => ((hB.disj hij).mono inter_subset_left
    inter_subset_left)) (fun i _ => (hB.meas i).inter hA)]
  congr 1
  ext x
  simp only [mem_iUnion, mem_inter_iff, Finset.mem_range, exists_prop]
  refine ⟨fun ⟨_, _, _, h⟩ => h, fun h => ?_⟩
  obtain ⟨i, hi, hx⟩ := hB.exists_mem x
  exact ⟨i, by omega, hx, h⟩

/-- The mixture `p = ε⁻¹ ∑ᵢ (Q (B i) - (1 - ε) P (B i)) • Q(· | B i)` of Billingsley's
proof of Theorem 6.7 (his `p_n`). -/
noncomputable def skMix (P Q : Measure S) (B : ℕ → Set S) (k : ℕ) (ε : ℝ) : Measure S :=
  (ENNReal.ofReal ε)⁻¹ • ∑ i ∈ Finset.range (k + 1),
    (Q (B i) - ENNReal.ofReal (1 - ε) * P (B i)) • skCond Q (B i)

variable (P Q : Measure S) [IsProbabilityMeasure Q] {B : ℕ → Set S} {k : ℕ} {ε : ℝ}

/-- **Billingsley p. 71**: the mixture identity `(1 - ε) ∑ᵢ P (B i) Q(A | B i) + ε p (A) = Q (A)`
on measurable sets `A`, so the law `Q` is recovered from the mixture. -/
lemma skMix_key (hB : IsSkPartition B k) (hε : 0 < ε)
    (hlow : ∀ i, ENNReal.ofReal (1 - ε) * P (B i) ≤ Q (B i)) {A : Set S} (hA : MeasurableSet A) :
    ENNReal.ofReal (1 - ε) * ∑ i ∈ Finset.range (k + 1), P (B i) * skCond Q (B i) A +
      ENNReal.ofReal ε * skMix P Q B k ε A = Q A := by
  have hε0 : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.2 hε).ne'
  rw [skMix, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hε0 ENNReal.ofReal_ne_top, one_mul, Measure.finsetSum_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← hB.sum_measure_inter Q hA]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, ← mul_assoc, ← add_mul, add_tsub_cancel_of_le (hlow i),
    skCond_mul Q (hB.meas i)]

/-- The mixture `skMix P Q B k ε` is a probability measure when `0 < ε ≤ 1` and
`(1 - ε) P (B i) ≤ Q (B i)` for every cell. -/
lemma skMix_isProbabilityMeasure [IsProbabilityMeasure P] (hB : IsSkPartition B k)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlow : ∀ i, ENNReal.ofReal (1 - ε) * P (B i) ≤ Q (B i)) :
    IsProbabilityMeasure (skMix P Q B k ε) := by
  constructor
  have h := skMix_key P Q hB hε hlow MeasurableSet.univ
  simp only [measure_univ, mul_one] at h
  have hsum : ∑ i ∈ Finset.range (k + 1), P (B i) = 1 := by
    simpa using hB.sum_measure_inter P MeasurableSet.univ
  rw [hsum, mul_one] at h
  have h1 : ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε * skMix P Q B k ε univ =
      ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε * 1 := by
    rw [h, mul_one, ← ENNReal.ofReal_add (by linarith) hε.le, sub_add_cancel, ENNReal.ofReal_one]
  rw [ENNReal.add_right_inj ENNReal.ofReal_ne_top,
    ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hε).ne' ENNReal.ofReal_ne_top] at h1
  exact h1

namespace SkorokhodMixExample

/-- Nonvacuity of `hlow`: for `Q = P` it holds for every `ε ∈ (0, 1]`, since
`ENNReal.ofReal (1 - ε) ≤ 1`. -/
example [IsProbabilityMeasure P] (hB : IsSkPartition B k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IsProbabilityMeasure (skMix P P B k ε) :=
  skMix_isProbabilityMeasure P P hB hε hε1 fun i => by
    have h1 : ENNReal.ofReal (1 - ε) ≤ 1 := ENNReal.ofReal_le_one.2 (by linarith)
    exact mul_le_of_le_one_left zero_le h1

/-- Nonvacuity of `IsSkPartition`: the partition with cell `S` at index `0` and empty cells
elsewhere. -/
example : IsSkPartition (fun i : ℕ => if i = 0 then (univ : Set S) else ∅) 0 where
  meas i := by by_cases hi : i = 0 <;> simp [hi]
  disj := by
    intro i j hij
    simp only [Function.onFun]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp_all
  cover := eq_univ_of_univ_subset (subset_iUnion_of_subset 0 (by simp))
  empty i hi := by simp [show i ≠ 0 by omega]

end SkorokhodMixExample

end LatticeProb.Skorokhod
