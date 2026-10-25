import LatticeProb.Prob.Percolation.LatticeBondCritical
import LatticeProb.Prob.Percolation.LatticeUniqueClusterEvent

/-!
# Classical supercritical Bernoulli bond input

This ordinary proposition states the critical bounds and almost-sure unique infinite
component facts for the canonical lattice product law. Its source is Grimmett,
*Percolation*, second edition (1999), Theorems 1.10 (p. 14) and 8.1 (p. 198), with
Section 1.4 (p. 13) identifying the strictly supercritical regime. The definition
asserts no proof of the literature input and installs no assumption or instance.
-/

namespace LatticeProb.External

open LatticeProb.Percolation

/-- The classical critical bounds and supercritical unique-component probability,
with the literal canonical law, critical value, and existence-and-uniqueness event. -/
def SupercriticalBondUniqueness : Prop :=
  (∀ (d : ℕ) [NeZero d], 2 ≤ d →
    0 < criticalProbability d ∧ criticalProbability d < 1) ∧
  (∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
      latticeBondLaw d p (uniqueInfiniteComponentEvent d) = 1)

end LatticeProb.External
