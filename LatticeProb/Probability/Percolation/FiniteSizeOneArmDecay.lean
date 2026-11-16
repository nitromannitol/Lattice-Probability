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

end FiniteSizeOneArm
