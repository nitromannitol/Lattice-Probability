/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.InputsDGFF at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFDistanceMeasurable

 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos.Inputs

 


def DGFFInductionLowerWindow : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∃ K : ℕ, 8 ≤ K ∧
    ∀ n : ℕ, K + 3 ≤ n →
      (1 / 2 : ℝ≥0∞) ≤ boxDGFF n
        {h | (2 : ℝ) ^ ((n : ℝ) / (K : ℝ)) ≤
          dgffAnnulusDistance n (ξ : ℝ) h}

end SupercriticalLQGUniqueness.B2.QPos.Inputs
