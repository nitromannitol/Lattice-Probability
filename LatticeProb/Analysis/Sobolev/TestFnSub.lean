import LatticeProb.Analysis.Sobolev.Basic

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- The test-function class is closed under subtraction. -/
theorem IsTestFn.sub {d : ℕ} {D : Set (Space d)} {φ ψ : Space d → ℝ}
    (hφ : IsTestFn D φ) (hψ : IsTestFn D ψ) : IsTestFn D (fun x => φ x - ψ x) := by
  refine ⟨hφ.1.sub hψ.1, ?_, ?_⟩
  · exact hφ.2.1.sub hψ.2.1
  · calc tsupport (fun x => φ x - ψ x)
        ⊆ closure (Function.support φ ∪ Function.support ψ) :=
          closure_mono (fun x hx => by
            simp only [Function.mem_support, sub_ne_zero] at hx
            by_cases h : φ x = 0
            · exact Or.inr (by simpa [h, eq_comm] using hx)
            · exact Or.inl h)
      _ = tsupport φ ∪ tsupport ψ := closure_union
      _ ⊆ D := Set.union_subset hφ.2.2 hψ.2.2

end LatticeProb.Sobolev
