import LatticeProb.Walk.CompactSegmentGraphClocks

/-! # Graph clocks with eventual edge bounds -/

set_option autoImplicit false
noncomputable section

open Filter Set Metric MeasureTheory MatedCRTHarmonic.Markov
open scoped ENNReal Topology NNReal

namespace LatticeProb.ConstantStepInterpolation

/-- Compact-segment graph clocks converge when the edge estimates hold eventually. -/
theorem tendsto_compact_segment_graph_clocks_of_eventual_bounds
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
    (hbound : ∀ᶠ i in l,
      (∀ v w, (G i).Adj v w → r i v ∈ Icc a b → r i w ∉ Icc a b →
        dist (η (r i v)) (η (r i w)) ≤ ε i) ∧
      (∀ j, j < N i → dist (η (r i (x i j))) (η (r i (x i (j + 1)))) ≤ δ i))
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
  let S : Set α := {i |
    (∀ v w, (G i).Adj v w → r i v ∈ Icc a b → r i w ∉ Icc a b →
      dist (η (r i v)) (η (r i w)) ≤ ε i) ∧
    (∀ j, j < N i → dist (η (r i (x i j))) (η (r i (x i (j + 1)))) ≤ δ i)}
  have hS : S ∈ l := hbound
  have hrange : Set.range (Subtype.val : S → α) ∈ l := by
    simpa only [Subtype.range_val] using hS
  have hmap : (l.comap (Subtype.val : S → α)).map Subtype.val = l :=
    Filter.map_comap_of_mem hrange
  have hsub := tendsto_compact_segment_graph_clocks_of_regular_exit
    (l := l.comap (Subtype.val : S → α)) η μ hη hμ (G ∘ Subtype.val)
    (r ∘ Subtype.val) hU hab himage (x ∘ Subtype.val) (m ∘ Subtype.val)
    (N ∘ Subtype.val) (F ∘ Subtype.val) f (δ ∘ Subtype.val) (ε ∘ Subtype.val) τ
    (fun i => hm i) (fun i => hexit i) (fun i => hstart i) (fun i => hstep i)
    (fun i => i.property.1) (fun i => i.property.2) (fun i => hpath i)
    (hF.comp tendsto_comap) (hδ.comp tendsto_comap) (hε.comp tendsto_comap)
    hbefore hafter
  refine ⟨?_, ?_, ?_⟩
  · exact (tendsto_comap'_iff hrange).mp hsub.1
  · exact (tendsto_comap'_iff hrange).mp hsub.2.1
  · intro q hq
    have h := hsub.2.2 q hq
    change {i : S | ∀ s ∈ Icc (knot (m i)
      (hitTime (Graph.innerBoundary (G i) {v | r i v ∈ Icc a b}) (x i)).toNat)
      (knot (m i) (N i)), ∀ t ∈ Icc (knot (m i)
      (hitTime (Graph.innerBoundary (G i) {v | r i v ∈ Icc a b}) (x i)).toNat)
      (knot (m i) (N i)), dist (F i s) (F i t) < q} ∈ l.comap Subtype.val at h
    rw [← hmap]
    exact h

end LatticeProb.ConstantStepInterpolation
end
