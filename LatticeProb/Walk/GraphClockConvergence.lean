import LatticeProb.Walk.ConstantStepGraphClocks
import LatticeProb.Topology.OrderedClockConvergence

/-! # Convergence of graph boundary and exit clocks -/

set_option autoImplicit false
noncomputable section

open Filter Set Metric MatedCRTHarmonic.Markov
open scoped Topology NNReal

namespace LatticeProb.ConstantStepInterpolation

/-- For a convergent family of embedded graph paths, vanishing boundary and
edge errors identify both the inner-boundary and vertex-exit clocks with a
regular limiting exit time. -/
theorem tendsto_graph_clocks_of_regular_exit
    {V E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter α}
    (G : α → SimpleGraph V) (A : α → Set V) (x : α → ℕ → V)
    (p : α → V → E) (m : α → ℝ≥0) (N : α → ℕ)
    (F : α → C(ℝ≥0, E)) (f : C(ℝ≥0, E)) (δ : α → ℝ)
    (K C : Set E) (τ : ℝ≥0)
    (hK : IsClosed K) (hKne : K.Nonempty) (hC : IsClosed C) (hCne : C.Nonempty)
    (hm : ∀ i, 0 < m i)
    (hexit : ∀ i, hitTime (A i)ᶜ (x i) = N i)
    (hstart : ∀ i, x i 0 ∈ A i)
    (hstep : ∀ i n, x i (n + 1) = x i n ∨ (G i).Adj (x i n) (x i (n + 1)))
    (hinside : ∀ i v, v ∈ A i → p i v ∈ C)
    (hedge : ∀ i j, j < N i → dist (p i (x i j)) (p i (x i (j + 1))) ≤ δ i)
    (hpath : ∀ i t, F i t = path (m i) (p i ∘ x i) t)
    (hF : Tendsto F l (𝓝 f))
    (hboundary : Tendsto (fun i => infDist
      (p i (x i (hitTime (Graph.innerBoundary (G i) (A i)) (x i)).toNat)) K) l (𝓝 0))
    (hδ : Tendsto δ l (𝓝 0))
    (hbefore : ∀ s < τ, f s ∉ K)
    (hafter : ∀ t > τ, ∃ s < t, f s ∉ C) :
    let a := fun i => knot (m i) (hitTime (Graph.innerBoundary (G i) (A i)) (x i)).toNat
    let b := fun i => knot (m i) (N i)
    Tendsto a l (𝓝 τ) ∧ Tendsto b l (𝓝 τ) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ s ∈ Icc (a i) (b i),
        ∀ t ∈ Icc (a i) (b i), dist (F i s) (F i t) < ε := by
  dsimp only
  let a := fun i => knot (m i) (hitTime (Graph.innerBoundary (G i) (A i)) (x i)).toNat
  let b := fun i => knot (m i) (N i)
  have hgraph : ∀ i, a i < b i ∧
      F i (a i) = p i (x i (hitTime (Graph.innerBoundary (G i) (A i)) (x i)).toNat) ∧
      ∀ t < b i, infDist (F i t) C ≤ δ i := by
    intro i
    obtain ⟨_, ho, _, hp, hb⟩ := graph_boundary_and_exit_clocks (G i) (A i) C
      (x i) (p i) (hm i) (hexit i) (hstart i) (hstep i) (hinside i) (hedge i)
    refine ⟨ho, ?_, ?_⟩
    · rw [hpath]
      exact hp
    · intro t ht
      rw [hpath]
      exact hb t ht
  have ha : Tendsto (fun i => infDist (F i (a i)) K) l (𝓝 0) := by
    convert hboundary using 1
    funext i
    rw [(hgraph i).2.1]
  have hb : ∀ᶠ i in l, ∀ s < b i, infDist (F i s) C ≤ δ i :=
    Filter.Eventually.of_forall (fun i => (hgraph i).2.2)
  have ho : ∀ᶠ i in l, a i ≤ b i :=
    Filter.Eventually.of_forall (fun i => (hgraph i).1.le)
  have hc := tendsto_ordered_clocks_of_regular_exit hK hKne hC hCne hF ha hδ hb ho hbefore hafter
  refine ⟨hc.1, hc.2, ?_⟩
  intro ε hε
  exact eventually_ordered_clock_oscillation_lt hK hKne hC hCne hF ha hδ hb ho hbefore hafter hε

end LatticeProb.ConstantStepInterpolation
end
