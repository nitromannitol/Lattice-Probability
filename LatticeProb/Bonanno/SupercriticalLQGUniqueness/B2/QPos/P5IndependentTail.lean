/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5IndependentTail at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.MeasureTheory.OuterMeasure.Basic

 



set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

theorem independent_many_failures_bound
    {Ω α : Type*} [MeasurableSpace Ω] [DecidableEq α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : α → Set Ω) (hE : iIndepSet E μ)
    (F : Finset α) (r : ℕ) (q : ℝ≥0∞)
    (hsmall : ∀ i ∈ F, μ (E i) ≤ q) :
    μ {ω | ∃ s : Finset α, s ⊆ F ∧ s.card = r ∧
        ∀ i ∈ s, ω ∈ E i} ≤
      (Nat.choose F.card r : ℝ≥0∞) * q ^ r := by
  let S := F.powersetCard r
  have hcover : {ω | ∃ s : Finset α, s ⊆ F ∧ s.card = r ∧
      ∀ i ∈ s, ω ∈ E i} ⊆
      ⋃ s ∈ S, ⋂ i ∈ s, E i := by
    intro ω hω
    obtain ⟨s, hs, hcard, hmem⟩ := hω
    apply Set.mem_iUnion.mpr
    refine ⟨s, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨hs, hcard⟩
    · apply Set.mem_iInter.mpr
      intro i
      apply Set.mem_iInter.mpr
      intro hi
      exact hmem i hi
  have hcap (s : Finset α) (hs : s ∈ S) :
      μ (⋂ i ∈ s, E i) ≤ q ^ r := by
    have hsF : s ⊆ F := (Finset.mem_powersetCard.mp hs).1
    have hcard : s.card = r := (Finset.mem_powersetCard.mp hs).2
    calc
      μ (⋂ i ∈ s, E i) = ∏ i ∈ s, μ (E i) := hE.meas_biInter s
      _ ≤ ∏ _i ∈ s, q := by
        apply Finset.prod_le_prod
        intro i hi; exact hsmall i (hsF hi)
      _ = q ^ r := by simp [hcard]
  calc
    μ {ω | ∃ s : Finset α, s ⊆ F ∧ s.card = r ∧
      ∀ i ∈ s, ω ∈ E i}
        ≤ μ (⋃ s ∈ S, ⋂ i ∈ s, E i) := measure_mono hcover
    _ ≤ ∑ s ∈ S, μ (⋂ i ∈ s, E i) := measure_biUnion_finset_le S _
    _ ≤ ∑ _s ∈ S, q ^ r := by
      apply Finset.sum_le_sum
      intro s hs
      exact hcap s hs
    _ = (Nat.choose F.card r : ℝ≥0∞) * q ^ r := by
      simp [S, Finset.card_powersetCard]

end SupercriticalLQGUniqueness.B2.QPos
