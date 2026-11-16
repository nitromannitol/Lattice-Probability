import LatticeProb.Prob.Percolation.FiniteProductPivotal
import LatticeProb.Vendor.FormalMathPercolation.Literature.SharpnessDCTProofs

/-!
# Finite-box connectivity and pivotal coordinates

A pivotal event does not depend on the state of its pivotal coordinate. This
identifies the probability of a closed pivotal coordinate with its pivotal
probability times the probability that the coordinate is closed. A path from
the origin remains in the set of vertices not connected to the box boundary
when the origin belongs to that set.
-/

open Finset Classical

namespace LatticeProb.Percolation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In a finite product model, a pivotal coordinate is closed with probability
`1 - par i`, independently of its pivotality. -/
theorem fpr_pivot_and_closed (par : ι → ℝ) (i : ι) (A : Set (ι → Bool)) :
    fpr par {ω | ω ∈ Pivot i A ∧ ω i = false} =
      (1 - par i) * fpr par (Pivot i A) := by
  rw [fpr_affine par i {ω | ω ∈ Pivot i A ∧ ω i = false},
    fpr_affine par i (Pivot i A)]
  have hpiv : ∀ (b : Bool) τ,
      (Equiv.piSplitAt i (fun _ => Bool)).symm (b, τ) ∈ Pivot i A ↔
      (Equiv.piSplitAt i (fun _ => Bool)).symm (false, τ) ∈ Pivot i A := by
    intro b τ
    simp only [Pivot, Set.mem_ofPred_eq, update_symm]
  simp only [Set.mem_ofPred_eq, Equiv.piSplitAt_symm_apply, ne_eq,
    ↓reduceDIte, Bool.true_eq_false, and_false, ite_false, Finset.sum_const_zero,
    mul_zero, zero_add, and_true]
  simp only [hpiv true]
  ring

end LatticeProb.Percolation

namespace Percolation.Literature.DCT16

open LatticeModels

variable {d n : ℕ}

/-- If the origin is not connected to the boundary, every connection from the
origin inside the box stays inside the set of vertices disconnected from the
boundary. -/
theorem openConnIn_blockSet_of_openConnIn_box {ω : BondConfig (Site d)} {x : Site d}
    (h0 : (0 : Site d) ∈ blockSet n ω)
    (h : ω ∈ openConnIn (↑(box d n) : Set (Site d)) 0 x) :
    ω ∈ openConnIn (↑(blockSet n ω) : Set (Site d)) 0 x := by
  apply mem_openConnIn_of_pathIn
  apply (pathIn_restrict_cluster (pathIn_of_mem_openConnIn h)).mono
  intro z hz
  rw [Finset.mem_coe, mem_blockSet_iff]
  refine ⟨hz.1, ?_⟩
  intro hzbdry
  have h0bdry : BdryConn n ω 0 := by
    obtain ⟨w, hw, hp⟩ := bdryConn_iff.mp hzbdry
    exact bdryConn_iff.mpr ⟨w, hw, hz.2.trans hp⟩
  exact (mem_blockSet_iff.mp h0).2 h0bdry

end Percolation.Literature.DCT16
