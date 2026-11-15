import Mathlib.Topology.Connected.Basic

/-! # Connected interiors from increasing exhaustions -/

set_option autoImplicit false

open Set

namespace LatticeProb

variable {X : Type*} [TopologicalSpace X]

/-- An increasing sequence of connected subsets of the interior which is dense
in a closed set makes that set the closure of its connected interior. -/
theorem connected_interior_of_increasing_exhaustion (K : Set X) (U : ℕ → Set X)
    (hK : IsClosed K) (hconn : ∀ n, IsConnected (U n))
    (hmono : Monotone U) (hsub : ∀ n, U n ⊆ interior K)
    (hdense : K ⊆ closure (⋃ n, U n)) :
    IsConnected (interior K) ∧ closure (interior K) = K := by
  have hU : IsConnected (⋃ n, U n) := by
    obtain ⟨x, hx⟩ := (hconn 0).1
    refine ⟨⟨x, mem_iUnion.mpr ⟨0, hx⟩⟩, ?_⟩
    apply isPreconnected_iUnion
    · exact ⟨x, mem_iInter.mpr (fun n => hmono (Nat.zero_le n) hx)⟩
    · exact fun n => (hconn n).2
  have hUi : (⋃ n, U n) ⊆ interior K := iUnion_subset hsub
  have hcl : closure (⋃ n, U n) = K := by
    apply Subset.antisymm
    · exact closure_minimal (hUi.trans interior_subset) hK
    · exact hdense
  constructor
  · apply hU.subset_closure hUi
    rw [hcl]
    exact interior_subset
  · apply Subset.antisymm
    · exact closure_minimal interior_subset hK
    · calc
        K = closure (⋃ n, U n) := hcl.symm
        _ ⊆ closure (interior K) := closure_mono hUi

end LatticeProb
