/-
The van den Berg-Kesten inequality, as an explicit hypothesis.

Mathlib does not have it and this library does not prove it, so a formalization
that needs it carries `LatticeProb.External.BKInequality` as a hypothesis rather
than as an axiom, and the dependence is visible in the statement of every result
that uses it.

Two events occur disjointly at a configuration when two disjoint sets of
coordinates certify them separately: reading only the coordinates in `K` forces
the first event, and reading only the coordinates in `L` forces the second.  The
inequality says that for a product measure on a finite product of two-point
spaces the probability of a disjoint occurrence of two increasing events is at
most the product of the probabilities.  This is van den Berg and Kesten (1985);
Reimer (2000) removed the monotonicity.
-/
import Mathlib

open MeasureTheory

namespace LatticeProb.External

/-- The disjoint occurrence of `A` and `B`: the configurations at which two
disjoint sets of coordinates certify `A` and `B` separately. -/
def disjointOccurrence {ι : Type*} (A B : Set (ι → Bool)) : Set (ι → Bool) :=
  {ω | ∃ K L : Set ι, Disjoint K L ∧
    (∀ ω' : ι → Bool, (∀ i ∈ K, ω' i = ω i) → ω' ∈ A) ∧
    (∀ ω' : ι → Bool, (∀ i ∈ L, ω' i = ω i) → ω' ∈ B)}

-- FROZEN-STATEMENT-BEGIN
/-- **The van den Berg-Kesten inequality** (van den Berg and Kesten, 1985).  For
a product measure on a finite product of two-point spaces and two increasing
measurable events, the probability that they occur disjointly is at most the
product of their probabilities. -/
def BKInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] (μ : ι → Measure Bool) (_ : ∀ i, IsProbabilityMeasure (μ i))
    (A B : Set (ι → Bool)), IsUpperSet A → IsUpperSet B →
    MeasurableSet A → MeasurableSet B →
    Measure.pi μ (disjointOccurrence A B) ≤ Measure.pi μ A * Measure.pi μ B
-- FROZEN-STATEMENT-END

end LatticeProb.External
