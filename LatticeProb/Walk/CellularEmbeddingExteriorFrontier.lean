import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells

/-!
# Frontier cells with representatives outside a bounded set

A locally finite cellular embedding admits an enclosing ball whose frontier
meets only cells with representatives outside a given bounded set.
-/

set_option autoImplicit false

open Set

namespace MatedCRTHarmonic.GMS3

/-- In a cellular embedding, a ball containing a given point can be chosen so
that every cell meeting its frontier has its representative outside a given
bounded set. -/
theorem exists_ball_frontier_representatives_outside
    {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)
    (p : V → ℂ) (hp : ∀ v, p v ∈ H.cell v) {A : Set ℂ}
    (hA : Bornology.IsBounded A) (z : ℂ) :
    ∃ R : ℝ, 0 < R ∧ z ∈ Metric.ball (0 : ℂ) R ∧
      ∀ v ∈ verticesMeeting H.cell (frontier (Metric.ball (0 : ℂ) R)), p v ∉ A := by
  let S : Set V := {v | p v ∈ A}
  have hS : S.Finite := (finite_verticesMeeting H hA).subset fun v hv =>
    ⟨p v, hp v, hv⟩
  have hbounded : Bornology.IsBounded (⋃ v ∈ S, H.cell v) :=
    (hS.isCompact_biUnion fun v _ => H.isCompact_cell v).isBounded
  obtain ⟨R, hR, hsub⟩ := (hbounded.union (Bornology.isBounded_singleton :
    Bornology.IsBounded ({z} : Set ℂ))).subset_ball_lt 0 (0 : ℂ)
  refine ⟨R, hR, hsub (mem_union_right _ (mem_singleton z)), ?_⟩
  intro v ⟨w, hwcell, hwfront⟩ hpA
  have hwball : w ∈ Metric.ball (0 : ℂ) R :=
    hsub (mem_union_left _ (mem_iUnion₂.mpr ⟨v, hpA, hwcell⟩))
  have hwsphere := Metric.frontier_ball_subset_sphere hwfront
  exact (ne_of_lt (Metric.mem_ball.mp hwball)) (Metric.mem_sphere.mp hwsphere)

end MatedCRTHarmonic.GMS3
