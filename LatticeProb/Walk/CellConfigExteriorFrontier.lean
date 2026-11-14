import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid

/-!
# Frontier cells outside a bounded representative region

Local finiteness allows a ball to be chosen so that each cell meeting its
frontier has its representative outside a prescribed bounded set.
-/

set_option autoImplicit false

open Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigBoundary

/-- A ball containing a given point can be chosen with every frontier cell's
representative outside a prescribed bounded set. -/
theorem exists_ball_frontier_representatives_outside (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) {A : Set Plane}
    (hA : Bornology.IsBounded A) (z : Plane) :
    ∃ R : ℝ, 0 < R ∧ z ∈ Metric.ball (0 : Plane) R ∧
      ∀ K : H.cells, ((K.1 : Set Plane) ∩ frontier (Metric.ball (0 : Plane) R)).Nonempty →
        p K ∉ A := by
  let S : Set H.cells := {K | p K ∈ A}
  have hS : S.Finite := by
    apply ((CellConfig.finite_restrict_of_isCompact hH hA.isCompact_closure).preimage
      Subtype.val_injective.injOn).subset
    intro K hK
    exact ⟨K.2, p K, hp K, subset_closure hK⟩
  have hbounded : Bornology.IsBounded (⋃ K ∈ S, (K.1 : Set Plane)) :=
    (hS.isCompact_biUnion fun K _ => K.1.isCompact).isBounded
  obtain ⟨R, hR, hsub⟩ := (hbounded.union (Bornology.isBounded_singleton :
    Bornology.IsBounded ({z} : Set Plane))).subset_ball_lt 0 (0 : Plane)
  refine ⟨R, hR, hsub (mem_union_right _ (mem_singleton z)), ?_⟩
  intro K ⟨w, hwK, hwfront⟩ hpA
  have hwball : w ∈ Metric.ball (0 : Plane) R :=
    hsub (mem_union_left _ (mem_iUnion₂.mpr ⟨K, hpA, hwK⟩))
  have hwsphere := Metric.frontier_ball_subset_sphere hwfront
  exact (ne_of_lt (Metric.mem_ball.mp hwball)) (Metric.mem_sphere.mp hwsphere)

end LatticeProb.CellConfigBoundary
