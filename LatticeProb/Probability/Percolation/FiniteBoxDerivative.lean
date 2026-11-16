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
theorem fpr_pivot_and_closed (par : ι → ℝ) (i : ι) (A : Set (ι → _)) :
    fpr par {ω | ω ∈ Pivot i A ∧ ω i = false} =
      (1 - par i) * fpr par (Pivot i A) := by
  rw [fpr_affine par i {ω | ω ∈ Pivot i A ∧ ω i = false},
    fpr_affine par i (Pivot i A)]
  have hpiv : ∀ (b : _) τ,
      (Equiv.piSplitAt i (fun _ => _)).symm (b, τ) ∈ Pivot i A ↔
      (Equiv.piSplitAt i (fun _ => _)).symm (false, τ) ∈ Pivot i A := by
    intro b τ
    simp only [Pivot, Set.mem_ofPred_eq, update_symm]
  simp only [Set.mem_ofPred_eq, Equiv.piSplitAt_symm_apply, ne_eq,
    ↓reduceDIte, reduceCtorEq, and_false, ite_false, Finset.sum_const_zero,
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

/-- A closed pivotal edge leaves the blocking set at a vertex connected to the origin. -/
theorem closed_pivotal_boundary_witness {ω : BondConfig (Site d)} {e : Sym2 (Site d)}
    (he : e ∈ (zdGraph d).edgeSet) (hp : IsPivotal (siteToBoundary d n) e ω)
    (hc : e ∉ ω) :
    ∃ x ∈ blockSet n ω, ∃ y ∈ (zdGraph d).neighborFinset x,
      y ∉ blockSet n ω ∧ s(x, y) = e ∧
      ω ∈ openConnIn (↑(blockSet n ω) : Set (Site d)) 0 x := by
  have hp' := (Russo.isPivotal_iff_of_notMem (isUpperSet_siteToBoundary d n) hc).1 hp
  have h0 : (0 : Site d) ∈ blockSet n ω := zero_mem_blockSet_iff.2 hp'.2
  rw [mem_siteToBoundary_iff] at hp'
  obtain ⟨z, hz, hpath⟩ := hp'.1
  have hzout : z ∉ blockSet n ω := by
    intro h
    exact (mem_blockSet_iff.1 h).2 (bdryConn_of_mem_innerBoundary hz)
  obtain ⟨x, y, hx, hy, hybox, hxy, hprefix⟩ := hpath.exit h0 hzout
  have hyconn : BdryConn n ω y := by
    have h : y ∉ blockSet n ω := hy
    rw [mem_blockSet_iff] at h
    by_contra hh
    exact h ⟨hybox, hh⟩
  have hclosed : s(x, y) ∉ ω := by
    intro h
    have hxb := (mem_blockSet_iff.1 hx)
    exact hxb.2 (hyconn.of_adj hxb.1 ((openGraph_adj ω x y).2
      ⟨h, (openGraph_adj _ x y).1 hxy |>.2⟩))
  have hedge : s(x, y) = e := by
    have h := (openGraph_adj _ x y).1 hxy
    exact (Set.mem_insert_iff.mp h.1).resolve_right hclosed
  have hne : ∀ a b, a ∈ (↑(blockSet n ω) : Set (Site d)) ∩ ↑(box d n) →
      b ∈ (↑(blockSet n ω) : Set (Site d)) ∩ ↑(box d n) → s(a, b) ≠ e := by
    intro a b ha hb hab
    have hs : s(a, b) = s(x, y) := hab.trans hedge.symm
    rcases Sym2.eq_iff.mp hs with ⟨hax, hby⟩ | ⟨hay, hbx⟩
    · exact hy (hby ▸ hb.1)
    · exact hy (hay ▸ ha.1)
  have horig : PathIn (openGraph ω)
      ((↑(blockSet n ω) : Set (Site d)) ∩ ↑(box d n)) 0 x := by
    apply pathIn_congrGraph (G := openGraph (insert e ω))
    · intro a b ha hb hab
      have hab' := (openGraph_adj _ a b).1 hab
      exact (openGraph_adj ω a b).2
        ⟨(Set.mem_insert_iff.mp hab'.1).resolve_left (hne a b ha hb), hab'.2⟩
    · exact hprefix
  refine ⟨x, hx, y, ?_, hy, hedge, ?_⟩
  · rw [SimpleGraph.mem_neighborFinset]
    rw [← hedge] at he
    exact he
  · exact mem_openConnIn_of_pathIn (horig.mono Set.inter_subset_left)

/-- Closed pivotality is equivalent to the oriented blocking-set boundary event. -/
theorem closed_pivotal_iff_boundary_witness {ω : BondConfig (Site d)} {e : Sym2 (Site d)} :
    (e ∈ (zdGraph d).edgeSet ∧ IsPivotal (siteToBoundary d n) e ω ∧ e ∉ ω) ↔
      ∃ S ∈ originSets d n, ∃ x ∈ S, ∃ y ∈ (zdGraph d).neighborFinset x,
        y ∉ S ∧ s(x, y) = e ∧
        ω ∈ openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S := by
  constructor
  · rintro ⟨he, hp, hc⟩
    have hp' := (Russo.isPivotal_iff_of_notMem (isUpperSet_siteToBoundary d n) hc).1 hp
    have h0 : (0 : Site d) ∈ blockSet n ω := zero_mem_blockSet_iff.2 hp'.2
    obtain ⟨x, hx, y, hy, hyS, heq, hconn⟩ := closed_pivotal_boundary_witness he hp hc
    exact ⟨blockSet n ω, mem_originSets.2 ⟨blockSet_subset ω, h0⟩,
      x, hx, y, hy, hyS, heq, hconn, rfl⟩
  · rintro ⟨S, hS, x, hx, y, hy, hyS, heq, hω⟩
    rw [← heq]
    exact subset_pivotal hS hx hy hyS hω

end Percolation.Literature.DCT16
