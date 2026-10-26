import LatticeProb.Prob.Percolation.DeletedBridgeRigidity
import LatticeProb.Prob.Percolation.InfiniteComponentDeletion
import LatticeProb.Prob.Percolation.CorrectedPlaneGrowth

/-!
# The actual carrier after a nonbridge singleton flip

The endpoint detour preserves connectedness on the full old component. Old and new
unique infinitude therefore identify their entire supports. The resulting graph
isomorphism fixes every ambient lattice position, hence the source balls and slopes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- The canonical unordered bond of an actual adjacent component pair. -/
def componentEdgeBond (C : OpenComponent ω) {a b : C}
    (hab : (componentGraph C).Adj a b) : Bond d :=
  bondOfAdjacent ((openGraph_adj_iff ω a.val b.val).mp hab).choose

/-- The literal singleton flip of an actual component edge. -/
def componentEdgeFlip (C : OpenComponent ω) {a b : C}
    (hab : (componentGraph C).Adj a b) : Configuration d :=
  finiteBondFlip {componentEdgeBond C hab} ω

variable (C : OpenComponent ω) (hOld : HasUniqueInfiniteOpenComponent ω)
  (hC : C.supp.Infinite) {a b : C} (hab : (componentGraph C).Adj a b)
  (hNew : HasUniqueInfiniteOpenComponent (componentEdgeFlip C hab))
  (hreach : ((openGraph (componentEdgeFlip C hab)).induce C.supp).Reachable a b)

include hreach in
/-- The actual deleted induced graph is connected on the entire old carrier. -/
theorem componentEdgeFlip_induce_connected :
    ((openGraph (componentEdgeFlip C hab)).induce C.supp).Connected := by
  rw [componentEdgeFlip, componentEdgeBond, singletonBondFlip_induce_eq_deleteEdges C hab]
  simpa only [Finset.coe_singleton] using
    C.connected_toSimpleGraph.connected_delete_edge_of_not_isBridge (x := a) (y := b) (by
      rw [SimpleGraph.isBridge_iff]
      rw [componentEdgeFlip, componentEdgeBond,
        singletonBondFlip_induce_eq_deleteEdges C hab] at hreach
      exact not_not.mpr (by simpa only [Finset.coe_singleton] using hreach))

include hOld hC hreach in
/-- The new selected infinite support is exactly the full old infinite support. -/
theorem componentEdgeFlip_uniqueInfiniteComponent_supp :
    (uniqueInfiniteComponent hNew).supp = C.supp := by
  have hEq : C = uniqueInfiniteComponent hOld :=
    (eq_uniqueInfiniteComponent_iff hOld C).mpr hC
  calc
    _ = (uniqueInfiniteComponent hOld).supp := ?_
    _ = C.supp := congrArg SimpleGraph.ConnectedComponent.supp hEq.symm
  apply uniqueInfiniteComponent_supp_eq_of_finiteBondFlip_of_retained_connected
    {componentEdgeBond C hab} hOld hNew
    (fun e he => by
      rw [Finset.mem_singleton.mp he]
      exact ((openGraph_adj_iff ω a.val b.val).mp hab).choose_spec)
  intro x hx y hy
  rw [← hEq] at hx hy
  exact ((componentEdgeFlip_induce_connected C hab hreach).preconnected
    (⟨x, hx⟩ : C) (⟨y, hy⟩ : C)).map (SimpleGraph.Embedding.induce C.supp).toHom

include hOld hC hreach in
/-- The complete vertex equivalence fixes lattice positions in both directions. -/
def nonBridgeComponentEquiv : C ≃ uniqueInfiniteComponent hNew where
  toFun x := ⟨x.val, by
    change x.val ∈ (uniqueInfiniteComponent hNew).supp
    rw [componentEdgeFlip_uniqueInfiniteComponent_supp C hOld hC hab hNew hreach]
    exact x.property⟩
  invFun y := ⟨y.val, by
    change y.val ∈ C.supp
    rw [← componentEdgeFlip_uniqueInfiniteComponent_supp C hOld hC hab hNew hreach]
    exact y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The forward vertex map preserves the exact ambient position. -/
theorem nonBridgeComponentEquiv_val (x : C) :
    (nonBridgeComponentEquiv C hOld hC hab hNew hreach x).val = x.val := rfl

/-- The inverse vertex map preserves the exact ambient position. -/
theorem nonBridgeComponentEquiv_symm_val (y : uniqueInfiniteComponent hNew) :
    ((nonBridgeComponentEquiv C hOld hC hab hNew hreach).symm y).val = y.val := rfl

/-- The whole old singleton-deletion graph is the actual new component graph. -/
def nonBridgeComponentIso :
    (componentGraph C).deleteEdges
      (({s(a, b)} : Finset (Sym2 C)) : Set (Sym2 C)) ≃g
        componentGraph (uniqueInfiniteComponent hNew) where
  toEquiv := nonBridgeComponentEquiv C hOld hC hab hNew hreach
  map_rel_iff' := by
    intro x y
    change (openGraph (componentEdgeFlip C hab)).Adj x.val y.val ↔ _
    change ((openGraph (componentEdgeFlip C hab)).induce C.supp).Adj x y ↔ _
    rw [componentEdgeFlip, componentEdgeBond, singletonBondFlip_induce_eq_deleteEdges C hab]

/-- Source Euclidean balls at every real radius are transported without moving the center. -/
theorem nonBridgeComponentEquiv_mem_ball (z : Vertex d) (R : ℝ) (x : C) :
    nonBridgeComponentEquiv C hOld hC hab hNew hreach x ∈
        componentEuclideanBall (uniqueInfiniteComponent hNew) z R ↔
      x ∈ componentEuclideanBall C z R := by
  rw [mem_componentEuclideanBall, mem_componentEuclideanBall]
  rfl

/-- Every coordinate slope is preserved with its literal ambient coordinates. -/
theorem nonBridgeComponentEquiv_slope (q : Fin d → ℝ) (x : C) :
    componentSlope (uniqueInfiniteComponent hNew) q
      (nonBridgeComponentEquiv C hOld hC hab hNew hreach x) = componentSlope C q x := rfl

end

end LatticeProb.Percolation
