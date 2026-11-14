import LatticeProb.Walk.CellularEmbeddingScaledExterior

/-!
# Exterior frontier cells in isometric coordinates

An isometric change of coordinates preserves boundedness of the target set
when choosing an enclosing frontier in a cellular embedding.
-/

set_option autoImplicit false

open Set

namespace MatedCRTHarmonic.GMS3

/-- A ball around the origin can be chosen so that scaled representatives of
its frontier cells lie outside a bounded set in isometric coordinates. -/
theorem exists_ball_frontier_isometric_scaled_representatives_outside
    {V E α F : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : V → α) (p : α → ℂ) (hp : ∀ v, p (e v) ∈ H.cell v)
    (f : ℂ ≃ₗᵢ[ℝ] F) {s : ℝ} (hs : s ≠ 0) {U : Set F}
    (hU : Bornology.IsBounded U) (z : ℂ) :
    ∃ R : ℝ, 0 < R ∧ z ∈ Metric.ball (0 : ℂ) R ∧
      ∀ v ∈ verticesMeeting H.cell (frontier (Metric.ball (0 : ℂ) R)),
        s • f (p (e v)) ∉ U := by
  have hbounded : Bornology.IsBounded (f ⁻¹' U) :=
    f.isometry.antilipschitzWith.isBounded_preimage hU
  obtain ⟨R, hR, hz, hfront⟩ :=
    exists_ball_frontier_scaled_representatives_outside H e p hp hs hbounded z
  refine ⟨R, hR, hz, ?_⟩
  intro v hv
  simpa only [Set.mem_preimage, map_smul] using hfront v hv

end MatedCRTHarmonic.GMS3
