import Mathlib

/-!
# 0. Order basics

The pointwise implication `∀ s, ω s = true → ω' s = true` used throughout the coupling
construction is exactly the product (`Pi`) order `ω ≤ ω'` on `Bool`-valued functions.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

namespace StrassenAux

attribute [local instance 10] Classical.propDecidable

/-- Pointwise implication `∀ s, ω s = true → ω' s = true` is the Pi order `ω ≤ ω'` on Bool-valued
functions. -/
private theorem le_iff_forall_apply_true_imp_true {ι : Type*} (ω ω' : ι → Bool) :
    (∀ s, ω s = true → ω' s = true) ↔ ω ≤ ω' := by
  simp only [Pi.le_def, Bool.le_iff_imp]

end StrassenAux

end LatticeProb
