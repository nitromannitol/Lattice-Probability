import Mathlib

/-!
# `IsIncreasingSet` and the monotone-coupling support set

The two definitions shared by every stage of Strassen's coupling theorem
(`LatticeProb.Prob.Strassen`): `IsIncreasingSet A` says that `A ⊆ (S → Bool)` is closed under
increasing a `{0,1}`-valued field coordinatewise, and `couplingSupport S` is the set of pairs
`(ω, ω')` with `ω' ≤ ω` coordinatewise, the support of a monotone coupling.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

namespace StrassenAux

attribute [local instance 10] Classical.propDecidable

/-- Verbatim copy of `Exploding.IsIncreasingSet`. -/
def IsIncreasingSet {S : Type} (A : Set (S → Bool)) : Prop :=
  ∀ ω ω' : S → Bool, ω ∈ A → (∀ s, ω s = true → ω' s = true) → ω' ∈ A

/-- The support set of a monotone coupling: second coordinate below the first. -/
def couplingSupport (S : Type) : Set ((S → Bool) × (S → Bool)) :=
  {p | ∀ s, p.2 s = true → p.1 s = true}

end StrassenAux

end LatticeProb
