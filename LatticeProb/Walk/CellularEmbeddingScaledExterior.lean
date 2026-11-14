import LatticeProb.Walk.CellularEmbeddingExteriorFrontier

/-!
# Scaled representatives outside a bounded set

An enclosing ball separates the frontier cells from a bounded set of scaled
representatives, when the scaling factor is nonzero.
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace MatedCRTHarmonic.GMS3

/-- A ball containing a prescribed point has scaled representatives of all
frontier cells outside a given bounded set. -/
theorem exists_ball_frontier_scaled_representatives_outside
    {V E α : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)
    (e : V → α) (p : α → ℂ) (hp : ∀ v, p (e v) ∈ H.cell v)
    {s : ℝ} (hs : s ≠ 0) {U : Set ℂ} (hU : Bornology.IsBounded U) (z : ℂ) :
    ∃ R : ℝ, 0 < R ∧ z ∈ Metric.ball (0 : ℂ) R ∧
      ∀ v ∈ verticesMeeting H.cell (frontier (Metric.ball (0 : ℂ) R)),
        s • p (e v) ∉ U := by
  let A : Set ℂ := {w | s • w ∈ U}
  have hA : Bornology.IsBounded A := by
    apply (hU.smul₀ s⁻¹).subset
    intro w hw
    change s • w ∈ U at hw
    refine ⟨s • w, hw, ?_⟩
    simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]
  exact exists_ball_frontier_representatives_outside H (fun v => p (e v)) hp hA z

end MatedCRTHarmonic.GMS3
