import LatticeProb.Vendor.FormalMathPercolation.Literature.PlanarDuality
import LatticeProb.Vendor.FormalMathPercolation.Literature.FiniteEnergy

/-!
# Finite-size connectivity

A connection inside a finite vertex set and the state of an edge leaving the set
are independent under Bernoulli bond percolation.
-/

open MeasureTheory Percolation.Literature

noncomputable section

namespace FiniteSizeOneArm

variable {V : Type*} [Countable V]

/-- The open boundary edge contributes a factor `p` to the probability of an
interior connection. -/
theorem interior_connection_inter_boundary_edge (G : SimpleGraph V) (p : unitInterval)
    (S : Finset V) (a b x y : V) (hy : y ∉ S)
    (he : s(x, y) ∈ G.edgeSet) :
    (bondPercolation G p).real
        (openConnIn (↑S : Set V) a b ∩ {ω | s(x, y) ∈ ω}) =
      (p : ℝ) * (bondPercolation G p).real (openConnIn (↑S : Set V) a b) := by
  classical
  have hdis : Disjoint (↑S.sym2 : Set (Sym2 V)) {s(x, y)} := by
    rw [Set.disjoint_singleton_right]
    intro h
    have h' := Finset.mem_sym2_iff.mp h
    exact hy (h' y (by simp))
  have hdet : DeterminedBy {ω : BondConfig V | s(x, y) ∈ ω} {s(x, y)} := by
    rw [determinedBy_iff]
    intro ω ω' h
    have := Set.ext_iff.mp h s(x, y)
    simpa using this
  have hm : MeasurableSet {ω : BondConfig V | s(x, y) ∈ ω} := measurableSet_setOfPred.mpr (measurable_set_mem _)
  rw [bondPercolation_real_inter_of_disjoint G p hdis
    (PlanarDuality.determinedBy_openConnIn S a b) hdet
    (PlanarDuality.determinedBy_openConnIn S a b).measurableSet_of_finset hm,
    bondPercolation_cylinder G p he, mul_comm]


/-- Interior and exterior connections and the open edge between them factor
under Bernoulli bond percolation. -/
theorem interior_connection_inter_edge_inter_exterior_connection
    (G : SimpleGraph V) (p : unitInterval) (S T : Finset V)
    (a b x y c d : V) (hST : Disjoint S T) (hx : x ∈ S) (hy : y ∉ S)
    (he : s(x, y) ∈ G.edgeSet) :
    (bondPercolation G p).real
        ((openConnIn (↑S : Set V) a b ∩ {ω | s(x, y) ∈ ω}) ∩
          openConnIn (↑T : Set V) c d) =
      (p : ℝ) * (bondPercolation G p).real (openConnIn (↑S : Set V) a b) *
        (bondPercolation G p).real (openConnIn (↑T : Set V) c d) := by
  classical
  have hxT : x ∉ T := fun h => (Finset.disjoint_left.mp hST) hx h
  have hdisST : Disjoint (↑S.sym2 : Set (Sym2 V)) ↑T.sym2 := by
    rw [Finset.disjoint_coe, Finset.disjoint_left]
    intro e hS hT
    induction e using Sym2.ind with
    | h u v =>
      rw [Finset.mk_mem_sym2_iff] at hS hT
      exact (Finset.disjoint_left.mp hST) hS.1 hT.1
  have hdisedge : Disjoint ({s(x, y)} : Set (Sym2 V)) ↑T.sym2 := by
    rw [Set.disjoint_singleton_left]
    intro h
    exact hxT ((Finset.mk_mem_sym2_iff.mp h).1)
  have hdetedge : DeterminedBy {ω : BondConfig V | s(x, y) ∈ ω} {s(x, y)} := by
    rw [determinedBy_iff]
    intro ω ω' h
    have := Set.ext_iff.mp h s(x, y)
    simpa using this
  have hmedge : MeasurableSet {ω : BondConfig V | s(x, y) ∈ ω} :=
    measurableSet_setOfPred.mpr (measurable_set_mem _)
  have hdet := (PlanarDuality.determinedBy_openConnIn S a b).mono
    (Set.subset_union_left : (↑S.sym2 : Set (Sym2 V)) ⊆ (↑S.sym2 : Set (Sym2 V)) ∪ {s(x, y)})
  have hdete := hdetedge.mono
    (Set.subset_union_right : ({s(x, y)} : Set (Sym2 V)) ⊆ (↑S.sym2 : Set (Sym2 V)) ∪ {s(x, y)})
  rw [bondPercolation_real_inter_of_disjoint G p (Set.disjoint_union_left.mpr ⟨hdisST, hdisedge⟩)
    (hdet.inter hdete) (PlanarDuality.determinedBy_openConnIn T c d)
    ((PlanarDuality.determinedBy_openConnIn S a b).measurableSet_of_finset.inter hmedge)
    (PlanarDuality.determinedBy_openConnIn T c d).measurableSet_of_finset,
    interior_connection_inter_boundary_edge G p S a b x y hy he]


omit [Countable V] in
/-- An open walk leaving a set contains an open edge leaving it, preceded by
an interior connection and followed by an open connection to the endpoint. -/
theorem exists_first_exit_edge {ω : BondConfig V} (S : Finset V) {a z : V}
    (ha : a ∈ S) (hz : z ∉ S) (h : (openGraph ω).Reachable a z) :
    ∃ x ∈ S, ∃ y ∉ S, s(x, y) ∈ ω ∧
      ω ∈ openConnIn (↑S : Set V) a x ∧ (openGraph ω).Reachable y z := by
  classical
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact (hz ha).elim
  | @cons u v z huv w ih =>
    by_cases hv : v ∈ S
    · obtain ⟨x, hx, y, hy, he, hc, hr⟩ := ih hv hz
      refine ⟨x, hx, y, hy, he, ?_, hr⟩
      exact PlanarDuality.openConnIn_trans
        (openConnIn_of_adj ha hv (openGraph_adj ω u v |>.mp huv).1 huv.ne) hc
    · exact ⟨u, ha, v, hv, (openGraph_adj ω u v |>.mp huv).1,
        openConnIn_refl ha, ⟨w⟩⟩

end FiniteSizeOneArm
