import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import LatticeProb.Prob.Percolation.LatticeBondCritical


/-!
# Green-column existence input

This module records a cited existence and uniqueness proposition for Green columns
on the supercritical infinite cluster. It is an explicit unproved assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb.Percolation

namespace LatticeProb.External

/-- Existence and uniqueness of the infinite-cluster Green column for each
fixed lattice pole, as described by Dario and Gu around equation (1.8). -/
def SupercriticalBondGreenColumnExistence : Prop :=
  ∀ (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval),
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∀ y : Vertex d, ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
          ∃! g : uniqueInfiniteComponent h → ℝ,
            IsGreenColumn d hd (uniqueInfiniteComponent h) ⟨y, hy⟩ g

end LatticeProb.External
