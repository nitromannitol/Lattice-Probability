import LatticeProb.Prob.Percolation.AntalPisztoraEvent

/-!
# Gluing finite-box crossing components

A crossing path in a shared integer cube attaches to a second outer component
when that component absorbs every sufficiently wide walk in its own box.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ} [NeZero d]

/-- A crossing component and an absorbing component share a vertex when their boxes
contain the same integer-side cube. -/
theorem ap_crossing_component_intersects_absorbing_component
    (ω : Configuration d) (c₁ c₂ q : Vertex d) (N : {n : ℕ // 0 < n})
    (h₁ : apInner q N ⊆ apOuter c₁ N) (h₂ : apInner q N ⊆ apOuter c₂ N)
    (C₁ : ((openGraph ω).induce (apOuter c₁ N : Set (Vertex d))).ConnectedComponent)
    (C₂ : ((openGraph ω).induce (apOuter c₂ N : Set (Vertex d))).ConnectedComponent)
    (hcross : apComponentCrossesInner c₁ N
      ((openGraph ω).induce (apOuter c₁ N : Set (Vertex d))) C₁ q)
    (hattach : ∀ x y : {z : Vertex d // z ∈ apOuter c₂ N},
      ∀ w : ((openGraph ω).induce (apOuter c₂ N : Set (Vertex d))).Walk x y,
        (∃ u ∈ w.support, ∃ v ∈ w.support, ∃ i : Fin d,
          (N.val : ℝ) / 2 < |(u.val i : ℝ) - (v.val i : ℝ)|) → x ∈ C₂.supp) :
    ∃ z : Vertex d, ∃ hz₁ : z ∈ apOuter c₁ N, ∃ hz₂ : z ∈ apOuter c₂ N,
      (⟨z, hz₁⟩ : {z : Vertex d // z ∈ apOuter c₁ N}) ∈ C₁.supp ∧
      (⟨z, hz₂⟩ : {z : Vertex d // z ∈ apOuter c₂ N}) ∈ C₂.supp := by
  classical
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  obtain ⟨x, y, hxface, hyface, w, hw⟩ := hcross i
  have hx := hw x w.start_mem_support
  have hy := hw y w.end_mem_support
  let H := openGraph ω
  let G₁ := H.induce (apOuter c₁ N : Set (Vertex d))
  let G₂ := H.induce (apOuter c₂ N : Set (Vertex d))
  let e₁ : G₁ →g H := (SimpleGraph.Embedding.induce _).toHom
  let wa : H.Walk x.val y.val := w.map e₁
  have hwa : ∀ z ∈ wa.support, z ∈ (apInner q N : Set (Vertex d)) := by
    intro z hz
    change z ∈ (w.map e₁).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    exact (hw u hu).2
  let wi := wa.induce (apInner q N : Set (Vertex d)) hwa
  let inc : H.induce (apInner q N : Set (Vertex d)) →g G₂ :=
    (H.induceHomOfLE (by intro z hz; exact h₂ hz)).toHom
  let w₂ := wi.map inc
  have hgap : (N.val : ℝ) / 2 < |(x.val i : ℝ) - (y.val i : ℝ)| := by
    have hl := (mem_apInnerLower_iff q x.val N i).mp hxface
    have hu := (mem_apInnerUpper_iff q y.val N i).mp hyface
    have hN : (0 : ℝ) < N.val := by exact_mod_cast N.property
    have hreal : (y.val i : ℝ) = (x.val i : ℝ) + N.val := by
      rw [hl.2, hu.2]
      push_cast
      rfl
    rw [abs_of_nonpos (by linarith : (x.val i : ℝ) - (y.val i : ℝ) ≤ 0)]
    linarith
  have hwide : ∃ u ∈ w₂.support, ∃ v ∈ w₂.support, ∃ j : Fin d,
      (N.val : ℝ) / 2 < |(u.val j : ℝ) - (v.val j : ℝ)| := by
    refine ⟨_, w₂.start_mem_support, _, w₂.end_mem_support, i, ?_⟩
    exact hgap
  have hC₂ := hattach _ _ w₂ hwide
  exact ⟨x.val, h₁ hx.2, h₂ hx.2, hx.1, hC₂⟩

/-- Two actual projected-box witnesses glue through their shared inner cube. -/
theorem ap_projected_components_intersect
    (ω : Configuration d) (c₁ c₂ q : Vertex d) (N : {n : ℕ // 0 < n})
    (h₁ : apInner q N ⊆ apOuter c₁ N) (h₂ : apInner q N ⊆ apOuter c₂ N)
    (hp₁ : apProjectedProperty c₁ N ((openGraph ω).induce (apOuter c₁ N : Set (Vertex d))))
    (hp₂ : apProjectedProperty c₂ N ((openGraph ω).induce (apOuter c₂ N : Set (Vertex d)))) :
    ∃ C₁ : ((openGraph ω).induce (apOuter c₁ N : Set (Vertex d))).ConnectedComponent,
    ∃ C₂ : ((openGraph ω).induce (apOuter c₂ N : Set (Vertex d))).ConnectedComponent,
      latticeCubeComponentCrosses (fun i => (c₁ i : ℝ))
        ⟨5 * (N.val : ℝ) / 4, by
          simp only [Set.mem_Ioi]
          have h : (0 : ℝ) < N.val := by exact_mod_cast N.property
          positivity⟩ _ C₁ ∧
      latticeCubeComponentCrosses (fun i => (c₂ i : ℝ))
        ⟨5 * (N.val : ℝ) / 4, by
          simp only [Set.mem_Ioi]
          have h : (0 : ℝ) < N.val := by exact_mod_cast N.property
          positivity⟩ _ C₂ ∧
      ∃ z : Vertex d, ∃ hz₁ : z ∈ apOuter c₁ N, ∃ hz₂ : z ∈ apOuter c₂ N,
        (⟨z, hz₁⟩ : {z : Vertex d // z ∈ apOuter c₁ N}) ∈ C₁.supp ∧
        (⟨z, hz₂⟩ : {z : Vertex d // z ∈ apOuter c₂ N}) ∈ C₂.supp := by
  obtain ⟨C₁, hc₁, _, _, hi₁⟩ := hp₁
  obtain ⟨C₂, hc₂, _, ha₂, _⟩ := hp₂
  exact ⟨C₁, C₂, hc₁, hc₂,
    ap_crossing_component_intersects_absorbing_component ω c₁ c₂ q N h₁ h₂ C₁ C₂
      (hi₁ q h₁) ha₂⟩

end
end LatticeProb.Percolation
