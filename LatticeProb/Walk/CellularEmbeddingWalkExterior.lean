import LatticeProb.Walk.CellularEmbeddingExteriorFrontier
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15CBoundary

/-! # Exterior visits by walks on cellular embeddings -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMS3
open MatedCRTHarmonic.GMSMain MatedCRTHarmonic.Harmonic

namespace LatticeProb

/-- A walk on a connected cellular embedding visits a representative outside
any bounded set with probability one. -/
theorem walkLaw_visit_representative_outside
    {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)
    (hconn : G.adj.Connected) (p : V → ℂ) (hp : ∀ v, p v ∈ H.cell v)
    {A : Set ℂ} (hA : Bornology.IsBounded A) (x : V) :
    G.walkLaw x {ω | ∃ n : ℕ, p (G.vertexPath ω n) ∉ A} = 1 := by
  obtain ⟨R, _, hx, hsep⟩ :=
    exists_ball_frontier_representatives_outside H p hp hA (p x)
  have hh := t15c_walkLaw_hitTime_ne_top (H := H) hconn Metric.isOpen_ball
    Metric.isBounded_ball (x := x) ⟨p x, hp x, hx⟩
  apply le_antisymm prob_le_one
  calc
    1 = G.walkLaw x {ω | hitTime (verticesMeeting H.cell
        (frontier (Metric.ball (0 : ℂ) R))) (G.vertexPath ω) ≠ ⊤} := hh.symm
    _ ≤ G.walkLaw x {ω | ∃ n : ℕ, p (G.vertexPath ω n) ∉ A} := by
      apply measure_mono
      intro ω hω
      obtain ⟨n, hn⟩ := hitTime_ne_top_iff.mp hω
      exact ⟨n, hsep _ hn⟩

end LatticeProb
end
