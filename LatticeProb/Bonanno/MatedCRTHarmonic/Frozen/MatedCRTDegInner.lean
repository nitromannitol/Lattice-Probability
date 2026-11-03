/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTDegInner at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDegBall

/-!
# Frozen definition: `MatedCRT.degInner`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **Inner degree** `deg_in(H₀)` ([20] Def 4.5, [20]): the largest `N` such that there are `N` unit
intervals with disjoint interiors whose images lie in `B′` and meet `c([−1,1])`. -/
def degInner (c : C(ℝ, ℂ)) : ℕ∞ :=
  ⨆ (N : ℕ) (a : Fin N → ℝ)
    (_ : (∀ i j, i ≠ j → Disjoint (Ioo (a i) (a i + 1)) (Ioo (a j) (a j + 1))) ∧
      ∀ i, c '' Icc (a i) (a i + 1) ⊆ degBall c ∧ (c '' Icc (a i) (a i + 1) ∩ c '' Icc (-1) 1).Nonempty),
    (N : ℕ∞)

end MatedCRT

end MatedCRTHarmonic
