/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.GridModulusProbability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.GreedyOscillationModulus
import LatticeProb.Bonanno.ReflectedGMS.Limit.GridStoppingTransfer
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppingExcursionCount

/-!
# A finite-grid modulus probability bound

The deterministic greedy-cell estimate is combined with the terminal second
moment bound for the number of completed excursions.  The remaining terms are
the probability of a large individual grid jump and the finitely many
probabilities of short proper greedy gaps.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A genuine martingale and its square compensator control the probability of
a large modulus on a finite deterministic grid. -/
theorem grid_modulus_probability_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    (d : ℝ≥0) {ε b : ℝ} (hε : 0 < ε) (hb : 0 ≤ b)
    (N L K : ℕ) (hK : 0 < K)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2T : MemLp (M ((N : ℝ≥0) * d)) 2 P) :
    P {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ N ∧ j - i ≤ L ∧
        4 * (ε + b) < |M ((j : ℝ≥0) * d) ω - M ((i : ℝ≥0) * d) ω|} ≤
      P {ω | ∃ n < N,
        b < |M (((n + 1 : ℕ) : ℝ≥0) * d) ω - M ((n : ℝ≥0) * d) ω|} +
      ENNReal.ofReal
        ((∫ ω, (M ((N : ℝ≥0) * d) ω) ^ 2 ∂P) / (ε ^ 2 * (K : ℝ))) +
      ∑ k ∈ Finset.range K,
        P {ω |
          greedyOscillationStop (fun i => M ((i : ℝ≥0) * d)) ε N (k + 1) ω < N ∧
          greedyOscillationStop (fun i => M ((i : ℝ≥0) * d)) ε N (k + 1) ω ≤
            greedyOscillationStop (fun i => M ((i : ℝ≥0) * d)) ε N k ω + L} := by
  let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * d
  have hgrid : Monotone grid := fun i j hij =>
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (show 0 ≤ d from zero_le)
  let G : Filtration ℕ m :=
    { seq := fun i => F (grid i)
      mono' := fun _ _ hij => F.mono (hgrid hij)
      le' := fun i => F.le (grid i) }
  let X : ℕ → Ω → ℝ := fun i => M (grid i)
  let σ : ℕ → Ω → ℕ := greedyOscillationStop X ε N
  let τ : ℕ → Ω → WithTop ℝ≥0 := fun k ω => grid (σ k ω)
  have hX : StronglyAdapted G X := fun i => hM.stronglyAdapted (grid i)
  have hσ : ∀ k, IsStoppingTime G (fun ω => (σ k ω : WithTop ℕ)) := fun k =>
    greedyOscillationStop_isStoppingTime hX N k
  have hτ : ∀ k, IsStoppingTime F (τ k) := fun k =>
    isStoppingTime_deterministicGrid grid (fun _ => le_rfl) (hσ k)
  have hmono : ∀ k ω, τ k ω ≤ τ (k + 1) ω := by
    intro k ω
    exact WithTop.coe_le_coe.mpr
      (hgrid (greedyOscillationStop_mono_step X hε N k ω))
  have hT : ∀ k ω, τ k ω ≤ grid N := by
    intro k ω
    exact WithTop.coe_le_coe.mpr (hgrid (greedyOscillationStop_le X ε N k ω))
  let jumpBad : Set Ω := {ω | ∃ n < N, b < |X (n + 1) ω - X n ω|}
  let countBad : Set Ω := {ω | σ K ω < N}
  let shortGap : ℕ → Set Ω := fun k =>
    {ω | σ (k + 1) ω < N ∧ σ (k + 1) ω ≤ σ k ω + L}
  let modulusBad : Set Ω := {ω | ∃ i j : ℕ,
    i ≤ j ∧ j ≤ N ∧ j - i ≤ L ∧ 4 * (ε + b) < |X j ω - X i ω|}
  have hpoint : modulusBad ⊆ jumpBad ∪ countBad ∪ ⋃ k ∈ Finset.range K, shortGap k := by
    intro ω hω
    by_contra hnot
    obtain ⟨i, j, hij, hjN, hji, hlarge⟩ := hω
    have hjump : ∀ n < N, |X (n + 1) ω - X n ω| ≤ b := by
      intro n hn
      by_contra hnle
      apply hnot
      exact Or.inl (Or.inl ⟨n, hn, lt_of_not_ge hnle⟩)
    have hσK : σ K ω = N :=
      Nat.le_antisymm (greedyOscillationStop_le X ε N K ω) (by
        by_contra hnle
        apply hnot
        exact Or.inl (Or.inr (lt_of_not_ge hnle)))
    have hgap : ∀ k < K, σ (k + 1) ω < N → L < σ (k + 1) ω - σ k ω := by
      intro k hk hkN
      have hnshort : ¬σ (k + 1) ω ≤ σ k ω + L := by
        intro hshort
        apply hnot
        exact Or.inr (mem_iUnion_of_mem k (mem_iUnion_of_mem (Finset.mem_range.mpr hk)
          ⟨hkN, hshort⟩))
      have hmono' := greedyOscillationStop_mono_step X hε N k ω
      omega
    have hbound := abs_sub_le_four_mul_of_greedyOscillationStop_eq_horizon
      X hε hb N K L i j ω hjump hσK hgap hij hjN hji
    exact (not_lt_of_ge hbound) (by simpa [abs_sub_comm] using hlarge)
  have hcountSubset : countBad ⊆
      {ω | (K : ℝ) ≤ largeStoppingIncrementCount M τ ε K ω} := by
    intro ω hω
    have hall : ∀ k ∈ Finset.range K,
        ({ω | ε ≤ |stoppedValue M (τ (k + 1)) ω - stoppedValue M (τ k) ω|}.indicator
          (fun _ => (1 : ℝ))) ω = 1 := by
      intro k hk
      have hkK : k < K := Finset.mem_range.mp hk
      have hkN : σ (k + 1) ω < N := by
        have hle : σ (k + 1) ω ≤ σ K ω :=
          greedyOscillationStop_mono X hε N ω (by omega)
        exact hle.trans_lt hω
      rw [Set.indicator_of_mem]
      change ε ≤ |X (σ (k + 1) ω) ω - X (σ k ω) ω|
      exact le_abs_sub_at_greedyOscillationStop_succ X hε N k ω hkN
    unfold largeStoppingIncrementCount
    change (K : ℝ) ≤ ∑ k ∈ Finset.range K,
      ({ω | ε ≤ |stoppedValue M (τ (k + 1)) ω - stoppedValue M (τ k) ω|}.indicator
        (fun _ => (1 : ℝ))) ω
    calc
      (K : ℝ) = ∑ k ∈ Finset.range K, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hall k hk).symm.le
  have hcount : P countBad ≤ ENNReal.ofReal
      ((∫ ω, (M (grid N) ω) ^ 2 ∂P) / (ε ^ 2 * (K : ℝ))) := by
    refine (measure_mono hcountSubset).trans ?_
    exact (large_stopping_increment_count_uniform_terminal_bounds
      hM hC τ hτ (grid N) hmono hT hrM hrC h2T hε
        (by exact_mod_cast hK) K).2
  have hunion : P modulusBad ≤ P jumpBad + P countBad +
      ∑ k ∈ Finset.range K, P (shortGap k) := by
    refine (measure_mono hpoint).trans ?_
    calc
      P (jumpBad ∪ countBad ∪ ⋃ k ∈ Finset.range K, shortGap k) ≤
          P (jumpBad ∪ countBad) + P (⋃ k ∈ Finset.range K, shortGap k) :=
        measure_union_le _ _
      _ ≤ (P jumpBad + P countBad) + ∑ k ∈ Finset.range K, P (shortGap k) :=
        add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _)
      _ = P jumpBad + P countBad + ∑ k ∈ Finset.range K, P (shortGap k) := rfl
  change P modulusBad ≤ P jumpBad + _ + ∑ k ∈ Finset.range K, P (shortGap k)
  exact hunion.trans (add_le_add (add_le_add le_rfl hcount) le_rfl)

end ReflectedGMS.MartingaleLimit
