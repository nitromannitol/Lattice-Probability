/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/SkorokhodLaw.lean.
-/
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.ProductMeasure
import LatticeProb.Prob.SkorokhodSpace

/-!
# Skorokhod representation, step 4: the random elements and their laws

On `Ω = (ι → S) × [0,1]`, `ι = Option (ℕ × ℕ ⊕ ℕ)`, with the product of `P` (coordinate
`none`, Billingsley's `X`), the conditional laws `P_n(· | B^{m(n)}_i)` (coordinates
`some (inl (n, i))`, Billingsley's `Y_{ni}`), the mixtures `p_n` (coordinates `some (inr n)`,
Billingsley's `Z_n`) and Lebesgue measure on `[0,1]` (Billingsley's `ξ`), define
`X'_n = Y_{n i}` if `ξ ≤ 1 - ε_{m(n)}` and `X ∈ B^{m(n)}_i`, and `X'_n = Z_n` otherwise
(`X'_n = Z_n ∼ P_n` when `n < n_0`). This file proves that the law of each `X'_n` is `P_n`
(`LatticeProb.Skorokhod.SkData.map_X'`), using the product law of the coordinates.

Source: Billingsley, *Convergence of Probability Measures*, 2nd ed. (1999), proof of
Theorem 6.7, p. 71 (the infinite product space, the definition of `X_n` and the computation of
`P[X_n ∈ A]`). We use mathlib's `Measure.infinitePi` for the product of the countably many
laws. Billingsley's separate `Y_n ∼ P_n` for `n < n_1` is merged into `Z_n`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped ENNReal unitInterval

namespace LatticeProb.Skorokhod

/-- Index set of the coordinates of Billingsley's product space. -/
abbrev SkIdx : Type := Option (ℕ × ℕ ⊕ ℕ)

/-- Billingsley's probability space: the coordinates `SkIdx → S` times the unit interval. -/
abbrev SkΩ (S : Type*) : Type _ := (SkIdx → S) × I

variable {S : Type*} [MeasurableSpace S] [PseudoMetricSpace S]
variable {P : Measure S} {Ps : ℕ → Measure S} (D : SkData P Ps)

namespace SkData

/-- The laws of the coordinates. -/
noncomputable def ν : SkIdx → Measure S
  | none => P
  | some (Sum.inl (n, i)) => skCond (Ps n) (D.B (D.reg n) i)
  | some (Sum.inr n) =>
    if D.φ 0 ≤ n then skMix P (Ps n) (D.B (D.reg n)) (D.k (D.reg n)) (skEps (D.reg n)) else Ps n

variable [IsProbabilityMeasure P] [∀ n, IsProbabilityMeasure (Ps n)]

/-- Every coordinate law is a probability measure. -/
instance isProbabilityMeasure_ν (j : SkIdx) : IsProbabilityMeasure (D.ν j) := by
  rcases j with _ | ⟨⟨n, i⟩⟩ | n
  · exact ‹IsProbabilityMeasure P›
  · exact skCond_isProbabilityMeasure _ _
  · simp only [ν]
    split_ifs with hn
    · exact skMix_isProbabilityMeasure P (Ps n) (D.part _) (skEps_pos _)
        (by linarith [skEps_le_half (D.reg n)]) (D.lower _ n (D.reg_spec hn))
    · infer_instance

/-- The probability measure of Billingsley's space: the infinite product of the coordinate
laws, times Lebesgue measure on `[0,1]`. -/
noncomputable def prob : Measure (SkΩ S) := (Measure.infinitePi D.ν).prod volume

/-- The probability measure of Billingsley's space is a probability measure. -/
instance : IsProbabilityMeasure D.prob := by unfold prob; infer_instance

omit [PseudoMetricSpace S] in
/-- The event that the coordinate `a` lies in a measurable set is measurable. -/
lemma measurableSet_coord (a : SkIdx) {U : Set S} (hU : MeasurableSet U) :
    MeasurableSet {ω : SkΩ S | ω.1 a ∈ U} :=
  ((measurable_pi_apply a).comp measurable_fst) hU

/-- For distinct coordinates `a` and `b`, the probability that `ω.2 ≤ c` and the coordinates
`a`, `b` lie in `U`, `V` is `D.ν a U * D.ν b V * c`. -/
lemma prob_two {a b : SkIdx} (hab : a ≠ b) {U V : Set S} (hU : MeasurableSet U)
    (hV : MeasurableSet V) (c : I) :
    D.prob {ω | ω.2 ≤ c ∧ ω.1 a ∈ U ∧ ω.1 b ∈ V} = D.ν a U * D.ν b V * ENNReal.ofReal c := by
  classical
  have : {ω : SkΩ S | ω.2 ≤ c ∧ ω.1 a ∈ U ∧ ω.1 b ∈ V} =
      (Set.pi (({a, b} : Finset SkIdx) : Set SkIdx)
        (fun j => if j = a then U else if j = b then V else univ)) ×ˢ Iic c := by
    ext ω
    simp only [Set.mem_setOf_eq, mem_prod, Set.mem_pi, Finset.coe_insert, Finset.coe_singleton,
      mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq, ↓reduceIte, mem_Iic,
      hab.symm]
    tauto
  rw [this, prob, Measure.prod_prod, Measure.infinitePi_pi (X := fun _ => S) (μ := D.ν), Finset.prod_pair hab,
    unitInterval.volume_Iic]
  · simp [hab.symm]
  · intro j _
    split_ifs
    exacts [hU, hV, MeasurableSet.univ]

/-- The probability that `c < ω.2` and the coordinate `a` lies in `U` is `D.ν a U * (1 - c)`. -/
lemma prob_one (a : SkIdx) {U : Set S} (hU : MeasurableSet U) (c : I) :
    D.prob {ω | ¬ ω.2 ≤ c ∧ ω.1 a ∈ U} = D.ν a U * ENNReal.ofReal (1 - c) := by
  have : {ω : SkΩ S | ¬ ω.2 ≤ c ∧ ω.1 a ∈ U} =
      (Set.pi (({a} : Finset SkIdx) : Set SkIdx) fun _ => U) ×ˢ Ioi c := by
    ext ω
    simp only [Set.mem_setOf_eq, mem_prod, Set.mem_pi, Finset.coe_singleton, mem_singleton_iff,
      forall_eq, mem_Ioi, not_le]
    tauto
  rw [this, prob, Measure.prod_prod, Measure.infinitePi_pi (X := fun _ => S) (μ := D.ν) (fun _ _ => hU),
    Finset.prod_singleton, unitInterval.volume_Ioi]

/-- The coordinate `a` has law `D.ν a`. -/
lemma prob_coord (a : SkIdx) {U : Set S} (hU : MeasurableSet U) :
    D.prob {ω | ω.1 a ∈ U} = D.ν a U := by
  have : {ω : SkΩ S | ω.1 a ∈ U} =
      (Set.pi (({a} : Finset SkIdx) : Set SkIdx) fun _ => U) ×ˢ univ := by
    ext ω; simp
  rw [this, prob, Measure.prod_prod, Measure.infinitePi_pi (X := fun _ => S) (μ := D.ν) (fun _ _ => hU),
    Finset.prod_singleton, measure_univ, mul_one]

/-- Billingsley's threshold `1 - ε_m` for `ξ`. -/
noncomputable def thr (m : ℕ) : I :=
  ⟨1 - skEps m, by constructor <;> linarith [skEps_pos m, skEps_le_half m]⟩

omit [IsProbabilityMeasure P] [∀ n, IsProbabilityMeasure (Ps n)] in
/-- The cell index of a point is at most the top index `k m` of the partition `B m`. -/
lemma idx_le (m : ℕ) (x : S) : D.idx m x ≤ D.k m := by
  by_contra h
  have := D.mem_idx m x
  rw [(D.part m).empty _ (not_le.1 h)] at this
  exact this

/-- Billingsley's `X_n` before the final modification on a null set. -/
noncomputable def X' (n : ℕ) (ω : SkΩ S) : S :=
  if D.φ 0 ≤ n ∧ ω.2 ≤ thr (D.reg n) then ω.1 (some (Sum.inl (n, D.idx (D.reg n) (ω.1 none))))
  else ω.1 (some (Sum.inr n))

omit [IsProbabilityMeasure P] [∀ n, IsProbabilityMeasure (Ps n)] in
/-- The preimage of a set under `X' n` when `φ 0 ≤ n`, decomposed over the cells of `B (reg n)`. -/
lemma preimage_X'_of_le {n : ℕ} (hn : D.φ 0 ≤ n) (A : Set S) :
    D.X' n ⁻¹' A = (⋃ i ∈ Finset.range (D.k (D.reg n) + 1),
      {ω : SkΩ S | ω.2 ≤ thr (D.reg n) ∧ ω.1 none ∈ D.B (D.reg n) i ∧
        ω.1 (some (Sum.inl (n, i))) ∈ A}) ∪
      {ω | ¬ ω.2 ≤ thr (D.reg n) ∧ ω.1 (some (Sum.inr n)) ∈ A} := by
  ext ω
  simp only [mem_preimage, X', hn, true_and, mem_union, mem_iUnion, Set.mem_setOf_eq,
    Finset.mem_range, exists_prop]
  split_ifs with h
  · constructor
    · intro hA
      exact Or.inl ⟨D.idx _ (ω.1 none), Nat.lt_succ_of_le (D.idx_le _ _), h, D.mem_idx _ _, hA⟩
    · rintro (⟨i, -, -, hB, hA⟩ | ⟨h', -⟩)
      · rwa [D.idx_eq hB]
      · exact absurd h h'
  · constructor
    · intro hA; exact Or.inr ⟨h, hA⟩
    · rintro (⟨i, -, h', -⟩ | ⟨-, hA⟩)
      · exact absurd h' h
      · exact hA

omit [IsProbabilityMeasure P] [∀ n, IsProbabilityMeasure (Ps n)] in
/-- The preimage of a set under `X' n` when `n < φ 0` is a coordinate event. -/
lemma preimage_X'_of_lt {n : ℕ} (hn : ¬ D.φ 0 ≤ n) (A : Set S) :
    D.X' n ⁻¹' A = {ω : SkΩ S | ω.1 (some (Sum.inr n)) ∈ A} := by
  ext ω; simp [X', hn]

omit [IsProbabilityMeasure P] [∀ n, IsProbabilityMeasure (Ps n)] in
/-- Each `X' n` is measurable. -/
lemma measurable_X' (n : ℕ) : Measurable (D.X' n) := by
  intro A hA
  by_cases hn : D.φ 0 ≤ n
  · rw [D.preimage_X'_of_le hn]
    exact (Finset.measurableSet_biUnion _ fun i _ => (measurable_snd measurableSet_Iic).inter
      ((measurableSet_coord _ ((D.part _).meas i)).inter (measurableSet_coord _ hA))).union
      ((measurable_snd measurableSet_Iic).compl.inter (measurableSet_coord _ hA))
  · rw [D.preimage_X'_of_lt hn]
    exact measurableSet_coord _ hA

/-- **Billingsley p. 71**: `L(X'_n) = P_n`. -/
theorem map_X' (n : ℕ) : D.prob.map (D.X' n) = Ps n := by
  ext A hA
  rw [Measure.map_apply (D.measurable_X' n) hA]
  by_cases hn : D.φ 0 ≤ n
  · set m := D.reg n
    rw [D.preimage_X'_of_le hn, measure_union, measure_biUnion_finset]
    · rw [Finset.sum_congr rfl fun i _ => D.prob_two (a := none) (b := some (Sum.inl (n, i)))
        (by simp) ((D.part m).meas i) hA (thr m), D.prob_one _ hA]
      have key := skMix_key P (Ps n) (D.part m) (skEps_pos m) (D.lower m n (D.reg_spec hn)) hA
      rw [← key]
      have hthr : ((thr m : I) : ℝ) = 1 - skEps m := rfl
      simp only [ν, hn, ite_true, hthr]
      rw [Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · rw [show ((thr (D.reg n) : I) : ℝ) = 1 - skEps (D.reg n) from rfl, sub_sub_cancel]
        ring
    · intro i _ j _ hij
      exact Set.disjoint_left.2 fun ω h1 h2 =>
        Set.disjoint_left.1 ((D.part m).disj hij) h1.2.1 h2.2.1
    · exact fun i _ => (measurable_snd measurableSet_Iic).inter
        ((measurableSet_coord _ ((D.part _).meas i)).inter (measurableSet_coord _ hA))
    · refine Set.disjoint_left.2 fun ω h1 h2 => ?_
      obtain ⟨i, -, hi⟩ := mem_iUnion₂.1 h1
      exact h2.1 hi.1
    · exact (measurable_snd measurableSet_Iic).compl.inter (measurableSet_coord _ hA)
  · rw [D.preimage_X'_of_lt hn, D.prob_coord _ hA]
    simp [ν, hn]

end SkData

namespace SkorokhodLawExample

example (μ : ProbabilityMeasure ℝ) :
    ∃ D : SkData (μ : Measure ℝ) fun _ => (μ : Measure ℝ),
      ∀ n, D.prob.map (D.X' n) = (μ : Measure ℝ) := by
  obtain ⟨D⟩ := exists_skData (μ := μ) (μs := fun _ => μ) tendsto_const_nhds
  exact ⟨D, fun n => D.map_X' n⟩

end SkorokhodLawExample

end LatticeProb.Skorokhod
