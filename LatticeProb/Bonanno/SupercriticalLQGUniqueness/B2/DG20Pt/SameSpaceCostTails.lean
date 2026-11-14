/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.SameSpaceCostTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.CouplingCostTails

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_same_space_cost_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : Ω → ℝ≥0∞) (C bLo bHi L H η : ℝ≥0∞)
    (hCL : C * L ≤ bLo) (hCH : C * bHi ≤ H)
    (hbad : P {ω | ¬ (A ω ≤ C * B ω ∧ B ω ≤ C * A ω)} ≤ η)
    (hlo : P {ω | B ω ≤ bLo} ≤ η)
    (hhi : P {ω | bHi < B ω} ≤ η) :
    P {ω | A ω < L} ≤ η + η ∧
      P {ω | H < A ω} ≤ η + η := by
  have hsubLo : {ω | A ω < L} ⊆
      {ω | ¬ (A ω ≤ C * B ω ∧ B ω ≤ C * A ω)} ∪
      {ω | B ω ≤ bLo} := by
    intro ω hω
    by_cases hg : A ω ≤ C * B ω ∧ B ω ≤ C * A ω
    · right
      exact hg.2.trans ((mul_le_mul_of_nonneg_left hω.le bot_le).trans hCL)
    · exact Or.inl hg
  have hsubHi : {ω | H < A ω} ⊆
      {ω | ¬ (A ω ≤ C * B ω ∧ B ω ≤ C * A ω)} ∪
      {ω | bHi < B ω} := by
    intro ω hω
    by_cases hg : A ω ≤ C * B ω ∧ B ω ≤ C * A ω
    · right
      by_contra h
      exact (not_le_of_gt hω) (hg.1.trans
        ((mul_le_mul_of_nonneg_left (le_of_not_gt h) bot_le).trans hCH))
    · exact Or.inl hg
  constructor
  · calc
      P {ω | A ω < L} ≤ P ({ω | ¬ (A ω ≤ C * B ω ∧ B ω ≤ C * A ω)} ∪
        {ω | B ω ≤ bLo}) := measure_mono hsubLo
      _ ≤ P {ω | ¬ (A ω ≤ C * B ω ∧ B ω ≤ C * A ω)} +
        P {ω | B ω ≤ bLo} := measure_union_le _ _
      _ ≤ η + η := add_le_add hbad hlo
  · calc
      P {ω | H < A ω} ≤ P ({ω | ¬ (A ω ≤ C * B ω ∧ B ω ≤ C * A ω)} ∪
        {ω | bHi < B ω}) := measure_mono hsubHi
      _ ≤ P {ω | ¬ (A ω ≤ C * B ω ∧ B ω ≤ C * A ω)} +
        P {ω | bHi < B ω} := measure_union_le _ _
      _ ≤ η + η := add_le_add hbad hhi

end SupercriticalLQGUniqueness.B2.DG20Pt
