import LatticeProb.Prob.Percolation.LatticeBondInfiniteEvent

/-!
# Selection of the unique actual infinite component

Selection is defined only given existence and uniqueness of an infinite actual component.
Its support consists exactly of the vertices whose actual open component is infinite.
The fully open positive-dimensional lattice supplies an unconditional consumer.
-/

namespace LatticeProb.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- Unique infinitude is equivalent to existence and reachability of all infinite vertices. -/
theorem hasUniqueInfiniteOpenComponent_iff_vertices (ω : Configuration d) :
    HasUniqueInfiniteOpenComponent ω ↔
      (∃ x, ω ∈ infiniteComponentEvent x) ∧
      ∀ x y, ω ∈ infiniteComponentEvent x → ω ∈ infiniteComponentEvent y →
        (openGraph ω).Reachable x y := by
  constructor
  · rintro ⟨C, hC, huniq⟩
    obtain ⟨x, hx⟩ := C.nonempty_supp
    have hxC := (SimpleGraph.ConnectedComponent.mem_supp_iff C x).mp hx
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change ((openGraph ω).connectedComponentMk x).supp.Infinite
      rw [hxC]
      exact hC
    · intro x y hx hy
      exact SimpleGraph.ConnectedComponent.exact ((huniq _ hx).trans (huniq _ hy).symm)
  · rintro ⟨⟨x, hx⟩, hr⟩
    refine ⟨(openGraph ω).connectedComponentMk x, hx, ?_⟩
    intro C hC
    obtain ⟨y, hy⟩ := C.nonempty_supp
    have hyC := (SimpleGraph.ConnectedComponent.mem_supp_iff C y).mp hy
    have hyinf : ω ∈ infiniteComponentEvent y := by
      change ((openGraph ω).connectedComponentMk y).supp.Infinite
      rw [hyC]
      exact hC
    exact hyC.symm.trans (SimpleGraph.ConnectedComponent.sound (hr y x hyinf hx))

/-- The unique infinite actual component, with no value on configurations lacking uniqueness. -/
noncomputable def uniqueInfiniteComponent (h : HasUniqueInfiniteOpenComponent ω) :
    OpenComponent ω := h.exists.choose

/-- The selected actual component has infinite support. -/
theorem uniqueInfiniteComponent_infinite (h : HasUniqueInfiniteOpenComponent ω) :
    (uniqueInfiniteComponent h).supp.Infinite := h.exists.choose_spec

/-- Every actual component is selected exactly when its support is infinite. -/
theorem eq_uniqueInfiniteComponent_iff (h : HasUniqueInfiniteOpenComponent ω)
    (C : OpenComponent ω) : C = uniqueInfiniteComponent h ↔ C.supp.Infinite := by
  constructor
  · rintro rfl
    exact uniqueInfiniteComponent_infinite h
  · intro hC
    exact h.unique hC (uniqueInfiniteComponent_infinite h)

/-- Membership in the selected support is exactly infinitude of the vertex's own component. -/
theorem mem_uniqueInfiniteComponent_iff (h : HasUniqueInfiniteOpenComponent ω)
    (x : Vertex d) : x ∈ (uniqueInfiniteComponent h).supp ↔
      ω ∈ infiniteComponentEvent x :=
  (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).trans
    (eq_uniqueInfiniteComponent_iff h _)

/-- The graph on the selected actual vertex subtype is connected. -/
theorem uniqueInfiniteComponent_connected (h : HasUniqueInfiniteOpenComponent ω) :
    (componentGraph (uniqueInfiniteComponent h)).Connected :=
  (uniqueInfiniteComponent h).connected_toSimpleGraph

/-- The selected component's actual graph has degree at most twice the dimension. -/
theorem uniqueInfiniteComponent_degree_le (h : HasUniqueInfiniteOpenComponent ω)
    (x : uniqueInfiniteComponent h) :
    (componentGraph (uniqueInfiniteComponent h)).degree x ≤ 2 * d :=
  componentGraph_degree_le _ x

/-- In positive dimension the fully open lattice has a unique infinite actual component. -/
theorem allOpen_hasUniqueInfiniteOpenComponent (d : ℕ) [NeZero d] :
    HasUniqueInfiniteOpenComponent (allOpen d) := by
  rw [hasUniqueInfiniteOpenComponent_iff_vertices]
  refine ⟨⟨0, allOpen_mem_infiniteComponentEvent 0⟩, ?_⟩
  intro x y _ _
  rw [openGraph_allOpen]
  exact (Graph.Zd.latticeConnected d).preconnected x y

/-- The selected fully open positive-dimensional component contains every lattice vertex. -/
theorem uniqueInfiniteComponent_allOpen_supp (d : ℕ) [NeZero d] :
    (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent d)).supp = Set.univ := by
  ext x
  exact (mem_uniqueInfiniteComponent_iff _ x).trans
    (iff_true_intro (allOpen_mem_infiniteComponentEvent x))

end LatticeProb.Percolation
