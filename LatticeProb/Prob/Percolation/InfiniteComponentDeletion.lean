import LatticeProb.Prob.Percolation.FiniteBondDeletion
import LatticeProb.Prob.Percolation.LatticeUniqueCluster

/-!
# Support transport under retained connectedness

An all-open finite deletion preserves the selected infinite support provided every pair of
old support vertices remains reachable and the flipped configuration has a unique infinite
component. Retained connectedness is an explicit conditional hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- Retained ambient reachability preserves the actual selected infinite vertex support. -/
theorem uniqueInfiniteComponent_supp_eq_of_finiteBondFlip_of_retained_connected
    (F : Finset (Bond d)) (hOld : HasUniqueInfiniteOpenComponent ω)
    (hNew : HasUniqueInfiniteOpenComponent (finiteBondFlip F ω))
    (hopen : ∀ e ∈ F, ω e = true)
    (hretained : ∀ x ∈ (uniqueInfiniteComponent hOld).supp,
      ∀ y ∈ (uniqueInfiniteComponent hOld).supp,
        (openGraph (finiteBondFlip F ω)).Reachable x y) :
    (uniqueInfiniteComponent hNew).supp = (uniqueInfiniteComponent hOld).supp := by
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent hOld).nonempty_supp
  let C := (openGraph (finiteBondFlip F ω)).connectedComponentMk o
  have hsub : (uniqueInfiniteComponent hOld).supp ⊆ C.supp := by
    intro y hy
    exact SimpleGraph.ConnectedComponent.sound (hretained y hy o ho)
  have hinf : C.supp.Infinite := (uniqueInfiniteComponent_infinite hOld).mono hsub
  have hC : C = uniqueInfiniteComponent hNew :=
    (eq_uniqueInfiniteComponent_iff hNew C).mpr hinf
  rw [← hC]
  apply Set.Subset.antisymm
  · exact (uniqueInfiniteComponent hOld).connectedComponentMk_supp_subset_supp
      (openGraph_finiteBondFlip_le_of_all_open F ω hopen) ho
  · exact hsub

end LatticeProb.Percolation
