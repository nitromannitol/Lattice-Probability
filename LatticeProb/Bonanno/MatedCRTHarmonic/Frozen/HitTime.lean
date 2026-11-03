/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.HitTime at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `Markov.hitTime`

The `ℕ∞` infimum of the hitting times (time `0` included; `⊤` if never).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace Markov

variable {S : Type*} [MeasurableSpace S]

/-- First hitting time of `A` (time `0` included; `⊤` if never). -/
def hitTime {T : Type*} (A : Set T) (ω : ℕ → T) : ℕ∞ := ⨅ (n : ℕ) (_ : ω n ∈ A), (n : ℕ∞)

end Markov

end MatedCRTHarmonic
