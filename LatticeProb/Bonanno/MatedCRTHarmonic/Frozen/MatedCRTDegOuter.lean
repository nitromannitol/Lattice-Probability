/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTDegOuter at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDegBall

/-!
# Frozen definition: `MatedCRT.degOuter`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **Outer degree** `deg_out(H₀)` ([20] Def 4.5, [20]): the largest `N′` such that there are `N′`
intervals with disjoint interiors, each with `c((a,b)) ⊂ int B′`, one endpoint image in `∂B′` and the other in
`c([−1,1])`. -/
def degOuter (c : C(ℝ, ℂ)) : ℕ∞ :=
  ⨆ (N : ℕ) (a : Fin N → ℝ) (b : Fin N → ℝ)
    (_ : (∀ i, a i < b i) ∧ (∀ i j, i ≠ j → Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
      ∀ i, c '' Ioo (a i) (b i) ⊆ interior (degBall c) ∧
        ((c (a i) ∈ frontier (degBall c) ∧ c (b i) ∈ c '' Icc (-1) 1) ∨
          (c (b i) ∈ frontier (degBall c) ∧ c (a i) ∈ c '' Icc (-1) 1))),
    (N : ℕ∞)

end MatedCRT

end MatedCRTHarmonic
