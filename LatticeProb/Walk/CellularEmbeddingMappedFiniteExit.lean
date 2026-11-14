import LatticeProb.Walk.CellularEmbeddingIsometricExterior
import LatticeProb.Walk.CellConfigFiniteExit
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15CBoundary

/-! # Finite exit of mapped cellular graph walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMS3
open MatedCRTHarmonic.GMSMain MatedCRTHarmonic.Harmonic
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- A recurrent interpolated cell walk exits every bounded domain in finite
 time when its law is a measurable relabelling of a connected cellular graph
 walk, with corresponding representatives. -/
theorem ae_continuousExitTime_ne_top_of_mapped_graph_walk
    {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)
    (hconn : G.adj.Connected) (C : CellConfig) [Countable C.cells]
    (e : V → C.cells) (p : C.cells → Plane) (f : ℂ ≃ₗᵢ[ℝ] Plane)
    (hp : ∀ v, f.symm (p (e v)) ∈ H.cell v)
    (hpos : ∀ K, 0 < C.holding K) (hrec : C.Recurrent)
    {ε : ℝ≥0} (hε : 0 < ε) {U : Set Plane} (hU : Bornology.IsBounded U)
    (x : V) (Q : Measure (ℕ → C.cells)) (hQ : C.IsSRWLaw (e x) Q)
    (hmap : Measurable (fun ω : ℕ → G.State => fun n => e (G.vertexPath ω n)))
    (hlaw : Q = (G.walkLaw x).map (fun ω n => e (G.vertexPath ω n))) :
    ∀ᵐ ω ∂Q, continuousExitTime U 0 (C.interpolatedWalk p ε ω) ≠ ∞ := by
  have he : (ε : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
  obtain ⟨R, _, hx, hfront⟩ :=
    exists_ball_frontier_isometric_scaled_representatives_outside H e
      (fun K => f.symm (p K)) hp f he hU (f.symm (p (e x)))
  let A : Set C.cells := {K | (ε : ℝ) • p K ∉ U}
  have htarget : MeasurableSet {ω : ℕ → C.cells | hitTime A ω ≠ ⊤} :=
    (measurableSet_hitTime_eq_top (MeasurableSet.of_discrete : MeasurableSet A)).compl
  have hhit := t15c_walkLaw_hitTime_ne_top (H := H) hconn Metric.isOpen_ball
    Metric.isBounded_ball (x := x) ⟨f.symm (p (e x)), hp x, hx⟩
  have hsource : ∀ᵐ ω ∂G.walkLaw x,
      hitTime A (fun n => e (G.vertexPath ω n)) ≠ ⊤ := by
    apply (mem_ae_iff_prob_eq_one (hmap htarget)).2
    apply le_antisymm prob_le_one
    calc
      1 = G.walkLaw x {ω | hitTime (verticesMeeting H.cell
        (frontier (Metric.ball (0 : ℂ) R))) (G.vertexPath ω) ≠ ⊤} := hhit.symm
      _ ≤ G.walkLaw x {ω | hitTime A (fun n => e (G.vertexPath ω n)) ≠ ⊤} := by
        apply measure_mono
        intro ω hω
        obtain ⟨n, hn⟩ := hitTime_ne_top_iff.mp hω
        apply hitTime_ne_top_iff.mpr
        refine ⟨n, ?_⟩
        simpa only [A, Set.mem_ofPred_eq, f.apply_symm_apply] using
          hfront (G.vertexPath ω n) hn
  have hvisit : ∀ᵐ ω ∂Q, ∃ n, (ε : ℝ) • p (ω n) ∉ U := by
    rw [hlaw]
    have hm := (ae_map_iff hmap.aemeasurable htarget).2 hsource
    filter_upwards [hm] with ω hω
    exact hitTime_ne_top_iff.mp hω
  exact ae_continuousExitTime_ne_top_of_recurrent_visit C p hpos hrec hε U hQ hvisit

end LatticeProb.CellConfigInterpolation
end
