/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.MinFourTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.SafeBoxScaleLower

 




set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem measure_min_four_lt
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X₀ X₁ X₂ X₃ a : Ω → ℝ≥0∞) (b₀ b₁ b₂ b₃ : ℝ≥0∞)
    (h₀ : P {ω | X₀ ω < a ω} ≤ b₀)
    (h₁ : P {ω | X₁ ω < a ω} ≤ b₁)
    (h₂ : P {ω | X₂ ω < a ω} ≤ b₂)
    (h₃ : P {ω | X₃ ω < a ω} ≤ b₃) :
    P {ω | min (min (X₀ ω) (X₁ ω)) (min (X₂ ω) (X₃ ω)) < a ω} ≤
      b₀ + b₁ + b₂ + b₃ := by
  have hsub : {ω | min (min (X₀ ω) (X₁ ω)) (min (X₂ ω) (X₃ ω)) < a ω} ⊆
      ({ω | X₀ ω < a ω} ∪ {ω | X₁ ω < a ω}) ∪
        ({ω | X₂ ω < a ω} ∪ {ω | X₃ ω < a ω}) := by
    intro ω hω
    simpa only [mem_ofPred_eq, mem_union, min_lt_iff] using hω
  calc
    P _ ≤ P (({ω | X₀ ω < a ω} ∪ {ω | X₁ ω < a ω}) ∪
      ({ω | X₂ ω < a ω} ∪ {ω | X₃ ω < a ω})) := measure_mono hsub
    _ ≤ P ({ω | X₀ ω < a ω} ∪ {ω | X₁ ω < a ω}) +
      P ({ω | X₂ ω < a ω} ∪ {ω | X₃ ω < a ω}) := measure_union_le _ _
    _ ≤ (P {ω | X₀ ω < a ω} + P {ω | X₁ ω < a ω}) +
      (P {ω | X₂ ω < a ω} + P {ω | X₃ ω < a ω}) := by
        exact add_le_add (measure_union_le _ _) (measure_union_le _ _)
    _ ≤ b₀ + b₁ + b₂ + b₃ := by
      have := add_le_add (add_le_add h₀ h₁) (add_le_add h₂ h₃)
      simpa only [add_assoc] using this

end SupercriticalLQGUniqueness.B2.DG20Pt
