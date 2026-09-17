import LatticeProb.Analysis.Sobolev.Basic

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- The test-function class is closed under multiplication by a constant. -/
theorem IsTestFn.const_mul {d : ℕ} {D : Set (Space d)} {φ : Space d → ℝ}
    (hφ : IsTestFn D φ) (c : ℝ) : IsTestFn D (fun x => c * φ x) := by
  refine ⟨hφ.1.const_smul c, ?_, ?_⟩
  · exact hφ.2.1.mul_left
  · exact (tsupport_smul_subset_right (fun _ : Space d => c) φ).trans hφ.2.2

end LatticeProb.Sobolev
