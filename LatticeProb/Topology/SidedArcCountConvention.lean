import LatticeProb.Topology.ShiftedTwoSidedArcCount
import LatticeProb.Topology.ShiftedSidedArcCount

/-! # Comparing two conventions for sided arc counts -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Counting both sides differs from counting the second side only at nonconsecutive
indices by exactly the indicator of a guarded, consecutive, two-sided intersection.
The predicates are arbitrary; no identification with geometric sides is asserted. -/
theorem sided_arc_count_convention_difference
    {Ω : Type*} (D L R : Ω → Prop) (k l : ℤ) (ω : Ω) :
    ({ω | k ≠ l ∧ D ω ∧ (L ω ∨ R ω)}.indicator (fun _ => (1 : ℕ))) ω +
        ({ω | k ≠ l ∧ D ω ∧ L ω ∧ R ω}.indicator (fun _ => (1 : ℕ))) ω =
      (({ω | k ≠ l ∧ D ω ∧ (L ω ∨ R ω)}.indicator (fun _ => (1 : ℕ))) ω +
        ({ω | k ≠ l ∧ D ω ∧ L ω ∧ R ω ∧
          1 < max k l - min k l}.indicator (fun _ => (1 : ℕ))) ω) +
        ({ω | k ≠ l ∧ D ω ∧ L ω ∧ R ω ∧
          ¬ 1 < max k l - min k l}.indicator (fun _ => (1 : ℕ))) ω := by
  classical
  by_cases h : k ≠ l ∧ D ω ∧ L ω ∧ R ω <;>
    by_cases hg : 1 < max k l - min k l <;>
    simp [Set.indicator, h, hg]

/-- The two sided arc count conventions agree exactly when the guarded pair is
not simultaneously consecutive and shared on both sides. -/
theorem sided_arc_count_conventions_eq_iff
    {Ω : Type*} (D L R : Ω → Prop) (k l : ℤ) (ω : Ω) :
    (({ω | k ≠ l ∧ D ω ∧ (L ω ∨ R ω)}.indicator (fun _ => (1 : ℕ))) ω +
        ({ω | k ≠ l ∧ D ω ∧ L ω ∧ R ω}.indicator (fun _ => (1 : ℕ))) ω =
      ({ω | k ≠ l ∧ D ω ∧ (L ω ∨ R ω)}.indicator (fun _ => (1 : ℕ))) ω +
        ({ω | k ≠ l ∧ D ω ∧ L ω ∧ R ω ∧
          1 < max k l - min k l}.indicator (fun _ => (1 : ℕ))) ω) ↔
      ¬ (k ≠ l ∧ D ω ∧ L ω ∧ R ω ∧ ¬ 1 < max k l - min k l) := by
  classical
  by_cases h : k ≠ l ∧ D ω ∧ L ω ∧ R ω <;>
    by_cases hg : 1 < max k l - min k l <;>
    simp [Set.indicator, h, hg]

end LatticeProb
