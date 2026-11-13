/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Probability at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib

/-!
# Finite-scale union bound for Proposition 2.10 failures

The per-scale estimate needed by the one-scale estimate is a probability bound for each fixed choice of scale and test pair;
The union bound must then retain the number of scales explicitly. This lemma records that finite-family
step without imposing measurability on the failure events: `Measure` uses its outer measure on arbitrary
sets, as in the one-scale estimate event. It is only the union-bound adapter; it does not assert or assume the
Proposition 2.10 estimate itself.
-/

set_option autoImplicit false

namespace MatedCRTHarmonic.GMS4

open MeasureTheory Set
open scoped ENNReal

/-- If each member of a finite family of bad-scale events has probability at most `p`, the union
bound is the number of scales times `p`. The cardinal factor is kept explicit for the later
polynomial-exponent absorption in the one-scale estimate. -/
theorem finite_union_measure_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (I : Finset ι) (bad : ι → Set Ω) (p : ℝ≥0∞)
    (hbad : ∀ i ∈ I, P (bad i) ≤ p) :
    P (⋃ i ∈ I, bad i) ≤ (I.card : ℝ≥0∞) * p := by
  calc
    P (⋃ i ∈ I, bad i) ≤ ∑ i ∈ I, P (bad i) := measure_biUnion_finset_le I bad
    _ ≤ ∑ i ∈ I, p := Finset.sum_le_sum fun i hi => hbad i hi
    _ = (I.card : ℝ≥0∞) * p := by simp

end MatedCRTHarmonic.GMS4
