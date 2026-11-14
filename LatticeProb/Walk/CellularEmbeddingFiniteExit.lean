import LatticeProb.Walk.CellularEmbeddingIsometricExterior
import LatticeProb.Walk.CellConfigFiniteExit

/-!
# Finite exit from cellular frontier visits

Frontier visits in a cellular embedding give finite exit of an interpolated
cell walk when the representatives and the two cell indexings correspond.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic MatedCRTHarmonic.GMS3
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- An interpolated walk exits a bounded domain in finite time if it visits
the images of all enclosing frontiers almost surely. -/
theorem ae_continuousExitTime_ne_top_of_cellular_frontier_visits
    {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)
    (C : CellConfig) (e : V → C.cells) (p : C.cells → Plane)
    (f : ℂ ≃ₗᵢ[ℝ] Plane) (hp : ∀ v, f.symm (p (e v)) ∈ H.cell v)
    (hpos : ∀ K, 0 < C.holding K) {ε : ℝ≥0} (hε : 0 < ε)
    {U : Set Plane} (hU : Bornology.IsBounded U) (z : ℂ)
    (Q : Measure (ℕ → C.cells)) (hunb : ∀ᵐ ω ∂Q, C.JumpTimesUnbounded ω)
    (hvisit : ∀ R : ℝ, 0 < R → z ∈ Metric.ball (0 : ℂ) R →
      ∀ᵐ ω ∂Q, ∃ n v, v ∈ verticesMeeting H.cell
        (frontier (Metric.ball (0 : ℂ) R)) ∧ ω n = e v) :
    ∀ᵐ ω ∂Q, continuousExitTime U 0 (C.interpolatedWalk p ε ω) ≠ ∞ := by
  have he : (ε : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
  obtain ⟨R, hR, hz, hfront⟩ :=
    exists_ball_frontier_isometric_scaled_representatives_outside H e
      (fun K => f.symm (p K)) hp f he hU z
  apply ae_continuousExitTime_ne_top_of_visit C p hpos hε U Q hunb
  filter_upwards [hvisit R hR hz] with ω ⟨n, v, hv, hn⟩
  refine ⟨n, ?_⟩
  rw [hn]
  simpa only [f.apply_symm_apply] using hfront v hv

/-- Recurrence supplies unbounded jump times in the frontier-visit criterion. -/
theorem ae_continuousExitTime_ne_top_of_recurrent_cellular_frontier_visits
    {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)
    (C : CellConfig) (e : V → C.cells) (p : C.cells → Plane)
    (f : ℂ ≃ₗᵢ[ℝ] Plane) (hp : ∀ v, f.symm (p (e v)) ∈ H.cell v)
    (hpos : ∀ K, 0 < C.holding K) (hrec : C.Recurrent)
    {ε : ℝ≥0} (hε : 0 < ε) {U : Set Plane} (hU : Bornology.IsBounded U)
    (z : ℂ) {x : C.cells} {Q : Measure (ℕ → C.cells)} (hQ : C.IsSRWLaw x Q)
    (hvisit : ∀ R : ℝ, 0 < R → z ∈ Metric.ball (0 : ℂ) R →
      ∀ᵐ ω ∂Q, ∃ n v, v ∈ verticesMeeting H.cell
        (frontier (Metric.ball (0 : ℂ) R)) ∧ ω n = e v) :
    ∀ᵐ ω ∂Q, continuousExitTime U 0 (C.interpolatedWalk p ε ω) ≠ ∞ :=
  ae_continuousExitTime_ne_top_of_cellular_frontier_visits H C e p f hp hpos
    hε hU z Q (CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hQ) hvisit

end LatticeProb.CellConfigInterpolation
end
