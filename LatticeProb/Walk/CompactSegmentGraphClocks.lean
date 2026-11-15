import LatticeProb.Walk.AreaCurveGraphClockConvergence

/-! # Graph clocks for compact curve-segment domains -/

set_option autoImplicit false
noncomputable section

open Filter Set Metric MeasureTheory MatedCRTHarmonic.Markov
open scoped ENNReal Topology NNReal

namespace LatticeProb.ConstantStepInterpolation

/-- For a compact curve-segment domain in a nontrivial real normed space,
the closure and frontier required for graph-clock convergence are nonempty. -/
theorem tendsto_compact_segment_graph_clocks_of_regular_exit
    {E V α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {l : Filter α}
    (η : ℝ → E) (μ : Measure E) (hη : Continuous η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    (G : α → SimpleGraph V) (r : α → V → ℝ) {U : Set E} (hU : IsOpen U)
    {a b : ℝ} (hab : a < b) (himage : η '' Icc a b = closure U)
    (x : α → ℕ → V) (m : α → ℝ≥0) (N : α → ℕ)
    (F : α → C(ℝ≥0, E)) (f : C(ℝ≥0, E)) (δ ε : α → ℝ) (τ : ℝ≥0)
    (hm : ∀ i, 0 < m i)
    (hexit : ∀ i, hitTime {v | r i v ∈ Icc a b}ᶜ (x i) = N i)
    (hstart : ∀ i, r i (x i 0) ∈ Icc a b)
    (hstep : ∀ i n, x i (n + 1) = x i n ∨ (G i).Adj (x i n) (x i (n + 1)))
    (hcross : ∀ i v w, (G i).Adj v w → r i v ∈ Icc a b → r i w ∉ Icc a b →
      dist (η (r i v)) (η (r i w)) ≤ ε i)
    (hedge : ∀ i j, j < N i → dist (η (r i (x i j))) (η (r i (x i (j + 1)))) ≤ δ i)
    (hpath : ∀ i t, F i t = path (m i) ((η ∘ r i) ∘ x i) t)
    (hF : Tendsto F l (𝓝 f)) (hδ : Tendsto δ l (𝓝 0)) (hε : Tendsto ε l (𝓝 0))
    (hbefore : ∀ s < τ, f s ∉ frontier U)
    (hafter : ∀ t > τ, ∃ s < t, f s ∉ closure U) :
    let c := fun i => knot (m i)
      (hitTime (Graph.innerBoundary (G i) {v | r i v ∈ Icc a b}) (x i)).toNat
    let d := fun i => knot (m i) (N i)
    Tendsto c l (𝓝 τ) ∧ Tendsto d l (𝓝 τ) ∧
      ∀ q : ℝ, 0 < q → ∀ᶠ i in l, ∀ s ∈ Icc (c i) (d i),
        ∀ t ∈ Icc (c i) (d i), dist (F i s) (F i t) < q := by
  have hclosure : (closure U).Nonempty := by
    rw [← himage]
    exact ⟨η a, a, ⟨le_rfl, hab.le⟩, rfl⟩
  have hcompact : IsCompact (closure U) := by
    rw [← himage]
    exact isCompact_Icc.image hη
  have hfrontier : (frontier U).Nonempty := by
    apply nonempty_frontier_iff.mpr
    refine ⟨closure_nonempty_iff.mp hclosure, ?_⟩
    intro hUuniv
    apply hcompact.ne_univ
    rw [hUuniv, closure_univ]
  exact tendsto_area_curve_graph_clocks_of_regular_exit η μ hη hμ G r hU hab himage
    x m N F f δ ε τ hfrontier hclosure hm hexit hstart hstep hcross hedge hpath
    hF hδ hε hbefore hafter

end LatticeProb.ConstantStepInterpolation
end
