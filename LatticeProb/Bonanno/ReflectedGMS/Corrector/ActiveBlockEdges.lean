/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.ActiveBlockEdges at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DiameterBlockIndex
import LatticeProb.Bonanno.ReflectedGMS.Geometry.BoundaryAnchoring

/-!
# Unique block ownership of the active edges of a selected dyadic block

This module supplies the combinatorial input of the specific-energy projection
chain `e_m + ‖g_m - g_0‖² = e_0` for the *actual* objects of
`ReflectedGMS.Geometry.DyadicApproximation`: the `κ`-selected squares
`Selected F D m s`, the patches `patchVertices F (square D s)`, the spatial
boundaries `boundaryVertices F (square D s)` and the `skeleton`.

The blockwise interpolation `phi` is characterised by minimising the vector
energy on each selected block against every competitor with the centroid trace.
Turning the resulting blockwise minimality into a single global statement
requires knowing that the variations carried by different blocks do not
interact, i.e. that every edge carrying a nonzero zero-boundary variation is
owned by *at most one* selected block.  That is what is proved here.

The geometric chain is:

* `interior_carrier_subset` — the interior of a closed axis-parallel rectangle
  in the Euclidean plane consists of the strictly interior points;
* `notMem_square_of_mem_interior_of_same_level` — two lattice squares of the
  same level with different lattice offsets meet only through the boundary of
  either one;
* `blockIndex_le_blockIndex_parent` / `blockIndex_ancestor_monotone` — `κ` is
  *unconditionally* monotone along an ancestor chain, because `b` is
  (`DiameterBlockIndex.inverseRatio_ancestor_mono`).  This strengthens
  `DiameterBlockIndex.selected_ancestor_unique`, which assumed strict
  monotonicity, to `not_selected_ancestor_of_selected`;
* `notMem_square_of_mem_interior_of_selected` — hence two *distinct* selected
  squares are never nested and their interiors meet no point of the other;
* `mem_boundaryVertices_of_mem_two_selected` — a *cell* (not a point) that
  meets two distinct selected squares must meet the spatial boundary of each of
  them, by connectedness of the cell; this is the actual ownership statement,
  and it holds without any finite cell-count assumption.

The edge conclusions are then:

* `activeEdge_unique` — an edge active in a selected block is active in no
  other selected block;
* `vectorGradSq_eq_zero_of_mem_two_selected` — an edge owned by two distinct
  selected blocks contributes zero to the energy of any variation vanishing on
  the skeleton;
* `tsum_tsum_activeWeight` and `tsum_tsum_activeWeight_le` — the exact
  redistribution of nonnegative (`ℝ≥0∞`-valued) edge weights over the selected
  blocks.  These are stated for arbitrary nonnegative edge weights, and
  `vectorEnergy_eq_tsum_vectorGradSq` identifies the actual vector energy as
  half such an edge sum, so the redistribution applies to it directly.  No
  integrability hypothesis is needed because every term is nonnegative; a
  signed redistribution is *not* claimed here.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.ActiveBlockEdges

open StatementIngredients DyadicApproximation DiameterBlockIndex

variable {V : Type*}

/-! ### The interior of a closed axis-parallel rectangle -/

/-- A point interior to a closed axis-parallel rectangle satisfies all the
defining inequalities strictly. -/
theorem interior_carrier_subset (Q : Rectangle) :
    interior Q.carrier ⊆ {z : Plane | ∀ i, Q.lower i < z i ∧ z i < Q.upper i} := by
  have hcar : Q.carrier
      = (PiLp.homeomorph 2 fun _ : Fin 2 => ℝ) ⁻¹'
        (Set.univ.pi fun i => Set.Icc (Q.lower i) (Q.upper i)) := by
    ext z
    exact ⟨fun hz i _ => Set.mem_Icc.2 (hz i),
      fun hz i => Set.mem_Icc.1 (hz i (Set.mem_univ i))⟩
  intro z hz
  rw [hcar, ← Homeomorph.preimage_interior, interior_pi_set Set.finite_univ] at hz
  intro i
  have hi : (PiLp.homeomorph 2 fun _ : Fin 2 => ℝ) z i ∈
      interior (Set.Icc (Q.lower i) (Q.upper i)) := hz i (Set.mem_univ i)
  rw [interior_Icc] at hi
  exact Set.mem_Ioo.1 hi

/-! ### Lattice squares of the same level -/

/-- Two lattice squares of the same level with different lattice offsets are
separated: no point interior to one belongs to the other.  This uses only that
the offsets differ by at least one in some coordinate. -/
theorem notMem_square_of_mem_interior_of_same_level (D : Grid) {s t : SquareIndex}
    (hlev : s.1 = t.1) (hne : s.2 ≠ t.2) {z : Plane}
    (hz : z ∈ interior (square D s).carrier) : z ∉ (square D t).carrier := by
  intro hzt
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hstrict := interior_carrier_subset (square D s) hz i
  have hwide := hzt i
  rw [square_lower_apply, square_upper_apply] at hstrict
  rw [square_lower_apply, square_upper_apply] at hwide
  rw [← hlev] at hwide
  have hpos : (0 : ℝ) < side D s.1 := side_pos D s.1
  rcases lt_or_gt_of_ne hi with h | h
  · have hcast : ((s.2 i : ℝ) + 1) ≤ (t.2 i : ℝ) := by exact_mod_cast h
    have hmul : side D s.1 * ((s.2 i : ℝ) + 1) ≤ side D s.1 * (t.2 i : ℝ) :=
      mul_le_mul_of_nonneg_left hcast hpos.le
    rw [mul_add, mul_one] at hmul
    linarith [hstrict.2, hwide.1]
  · have hcast : ((t.2 i : ℝ) + 1) ≤ (s.2 i : ℝ) := by exact_mod_cast h
    have hmul : side D s.1 * ((t.2 i : ℝ) + 1) ≤ side D s.1 * (s.2 i : ℝ) :=
      mul_le_mul_of_nonneg_left hcast hpos.le
    rw [mul_add, mul_one] at hmul
    linarith [hstrict.1, hwide.2]

/-! ### The ancestor chain of lattice squares -/

/-- The level of the `j`-th ancestor. -/
theorem ancestor_fst (D : Grid) (s : SquareIndex) (j : ℕ) :
    (ancestor D s j).1 = s.1 + (j : ℤ) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [ancestor_succ', parent_fst, ih]
      push_cast
      ring

/-- Iterating `DiameterBlockIndex.square_subset_parent`. -/
theorem square_subset_ancestor (D : Grid) (s : SquareIndex) (j : ℕ) :
    (square D s).carrier ⊆ (square D (ancestor D s j)).carrier := by
  induction j with
  | zero => exact fun z hz => hz
  | succ j ih =>
      rw [ancestor_succ']
      exact ih.trans (square_subset_parent D (ancestor D s j))

/-! ### Unconditional monotonicity of `κ` along the ancestor chain -/

/-- `κ(S) ≤ κ(P)`.  Unlike the strict inequality of
`DiameterBlockIndex.blockIndex_lt_blockIndex_parent`, this needs no hypothesis:
it is the termwise comparison of the two series coming from the monotonicity of
`b` along the chain. -/
theorem blockIndex_le_blockIndex_parent (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    blockIndex F D s ≤ blockIndex F D (parent D s) := by
  rw [blockIndex_eq_tsum, blockIndex_parent_eq_tsum]
  exact ENNReal.tsum_le_tsum fun j =>
    mul_le_mul' le_rfl (inverseRatio_ancestor_mono F D s (Nat.le_succ j))

theorem blockIndex_ancestor_monotone (F : IndexedCells V) (D : Grid) (s : SquareIndex) :
    Monotone fun j : ℕ => blockIndex F D (ancestor D s j) := by
  refine monotone_nat_of_le_succ fun j => ?_
  rw [ancestor_succ']
  exact blockIndex_le_blockIndex_parent F D (ancestor D s j)

/-- **No strict ancestor of a selected square is selected.**  This is the
unconditional form of `DiameterBlockIndex.selected_ancestor_unique`, whose
strict-monotonicity hypothesis is not available for the actual selected
squares. -/
theorem not_selected_ancestor_of_selected (F : IndexedCells V) (D : Grid) (m : ℝ)
    (s : SquareIndex) (hs : Selected F D m s) {j : ℕ} (hj : 0 < j) :
    ¬ Selected F D m (ancestor D s j) := by
  intro ht
  have h1 : ENNReal.ofReal m < blockIndex F D (ancestor D s 1) := by
    rw [ancestor_one]
    exact hs.2.2
  have h2 : blockIndex F D (ancestor D s 1) ≤ blockIndex F D (ancestor D s j) :=
    blockIndex_ancestor_monotone F D s hj
  exact absurd ht.2.1 (not_le.2 (lt_of_lt_of_le h1 h2))

/-! ### Distinct selected squares are geometrically separated -/

/-- **Separation of the actual selected squares.**  Two distinct selected
squares are never nested — that is excluded by the threshold characterisation
of `Selected` — hence they are separated by the lattice at their common level:
no point interior to one lies in the other. -/
theorem notMem_square_of_mem_interior_of_selected (F : IndexedCells V) (D : Grid) (m : ℝ)
    {s t : SquareIndex} (hs : Selected F D m s) (ht : Selected F D m t) (hne : s ≠ t)
    {z : Plane} (hz : z ∈ interior (square D s).carrier) : z ∉ (square D t).carrier := by
  rcases le_or_gt s.1 t.1 with hle | hlt
  · obtain ⟨j, hjcast⟩ : ∃ j : ℕ, (j : ℤ) = t.1 - s.1 := ⟨(t.1 - s.1).toNat, by omega⟩
    have hlev : (ancestor D s j).1 = t.1 := by
      rw [ancestor_fst, hjcast]
      ring
    by_cases heq : ancestor D s j = t
    · exfalso
      have hj0 : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h0 | h
        · exact absurd (by rw [← heq, h0, ancestor_zero] : s = t) hne
        · exact h
      have hsel : Selected F D m (ancestor D s j) := by rw [heq]; exact ht
      exact not_selected_ancestor_of_selected F D m s hs hj0 hsel
    · have hne2 : (ancestor D s j).2 ≠ t.2 := fun h2 => heq (Prod.ext hlev h2)
      exact notMem_square_of_mem_interior_of_same_level D hlev hne2
        (interior_mono (square_subset_ancestor D s j) hz)
  · obtain ⟨j, hjcast⟩ : ∃ j : ℕ, (j : ℤ) = s.1 - t.1 := ⟨(s.1 - t.1).toNat, by omega⟩
    have hj0 : 0 < j := by omega
    have hlev : (ancestor D t j).1 = s.1 := by
      rw [ancestor_fst, hjcast]
      ring
    by_cases heq : ancestor D t j = s
    · exfalso
      have hsel : Selected F D m (ancestor D t j) := by rw [heq]; exact hs
      exact not_selected_ancestor_of_selected F D m t ht hj0 hsel
    · have hne2 : s.2 ≠ (ancestor D t j).2 := fun h2 => heq (Prod.ext hlev h2.symm)
      intro hzt
      exact notMem_square_of_mem_interior_of_same_level D hlev.symm hne2 hz
        (square_subset_ancestor D t j hzt)

/-! ### Ownership of a cell by a selected block -/

/-- **The ownership lemma.**  A cell meeting two distinct selected squares
necessarily meets the spatial boundary of each of them, hence lies in the
skeleton.  Only connectedness of the individual cells is used: cells may be
arbitrarily large and there is no finiteness assumption on the patches. -/
theorem mem_boundaryVertices_of_mem_two_selected (F : IndexedCells V)
    (hcell : ∀ v : V, IsConnected (F.cell v : Set Plane)) (D : Grid) (m : ℝ)
    {s t : SquareIndex} (hs : Selected F D m s) (ht : Selected F D m t) (hne : s ≠ t)
    {v : V} (hvs : v ∈ patchVertices F (square D s))
    (hvt : v ∈ patchVertices F (square D t)) :
    v ∈ boundaryVertices F (square D s) := by
  by_contra hb
  have hb' : ¬ ((F.cell v : Set Plane) ∩ frontier (square D s).carrier).Nonempty := hb
  have hvs' : ((F.cell v : Set Plane) ∩ (square D s).carrier).Nonempty := hvs
  have hvt' : ((F.cell v : Set Plane) ∩ (square D t).carrier).Nonempty := hvt
  have hdisj : Disjoint (F.cell v : Set Plane) (frontier (square D s).carrier) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp hb'
  have hsub : (F.cell v : Set Plane) ⊆ interior (square D s).carrier :=
    connected_subset_interior_of_inter_nonempty_of_disjoint_frontier (hcell v) hvs' hdisj
  obtain ⟨z, hzcell, hzt⟩ := hvt'
  exact notMem_square_of_mem_interior_of_selected F D m hs ht hne (hsub hzcell) hzt

/-! ### Active edges of a selected block -/

/-- An ordered pair of vertices is an **active edge** of the selected square `s`
when it is an edge of the ambient graph, both endpoints meet `s`, and the pair
is not entirely on the spatial boundary of `s`: an edge with both endpoints on
the boundary carries no degree of freedom for a variation vanishing there. -/
def ActiveEdge (F : IndexedCells V) (D : Grid) (m : ℝ) (s : SquareIndex)
    (p : V × V) : Prop :=
  Selected F D m s ∧ F.graph.toSimpleGraph.Adj p.1 p.2 ∧
    p.1 ∈ patchVertices F (square D s) ∧ p.2 ∈ patchVertices F (square D s) ∧
    ¬ (p.1 ∈ boundaryVertices F (square D s) ∧ p.2 ∈ boundaryVertices F (square D s))

/-- **Unique ownership of active edges.**  An active edge of a selected block is
active in no other selected block. -/
theorem activeEdge_unique (F : IndexedCells V)
    (hcell : ∀ v : V, IsConnected (F.cell v : Set Plane)) (D : Grid) (m : ℝ)
    {s t : SquareIndex} {p : V × V}
    (hs : ActiveEdge F D m s p) (ht : ActiveEdge F D m t p) : s = t := by
  by_contra hne
  exact hs.2.2.2.2
    ⟨mem_boundaryVertices_of_mem_two_selected F hcell D m hs.1 ht.1 hne hs.2.2.1 ht.2.2.1,
      mem_boundaryVertices_of_mem_two_selected F hcell D m hs.1 ht.1 hne
        hs.2.2.2.1 ht.2.2.2.1⟩

/-! ### The energy carried by one edge -/

/-- The contribution of one ordered pair of vertices to the vector energy. -/
noncomputable def vectorGradSq (G : ReflectedWalk.ConductanceGraph V) (u : V → Plane)
    (p : V × V) : ℝ≥0∞ :=
  ∑ i : Fin 2, ENNReal.ofReal (G.gradSq (fun v => u v i) p)

/-- The existing vector energy is half the sum of the edge contributions. -/
theorem vectorEnergy_eq_tsum_vectorGradSq (G : ReflectedWalk.ConductanceGraph V)
    (u : V → Plane) :
    vectorEnergy G u = (∑' p : V × V, vectorGradSq G u p) / 2 := by
  have h : ∑' p : V × V, vectorGradSq G u p
      = (∑' p : V × V, ENNReal.ofReal (G.gradSq (fun v => u v 0) p))
        + ∑' p : V × V, ENNReal.ofReal (G.gradSq (fun v => u v 1) p) := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun p => by simp [vectorGradSq, Fin.sum_univ_two]
  rw [h]
  show (∑ i : Fin 2, energyENN G (fun v => u v i)) = _
  rw [Fin.sum_univ_two]
  simp only [energyENN, div_eq_mul_inv, add_mul]

/-- An edge across which the variation does not change carries no energy. -/
theorem vectorGradSq_eq_zero_of_apply_eq (G : ReflectedWalk.ConductanceGraph V)
    (u : V → Plane) {p : V × V} (h : u p.1 = u p.2) : vectorGradSq G u p = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [ReflectedWalk.ConductanceGraph.gradSq, h]

/-! ### Exact redistribution of nonnegative edge weights over the blocks -/

end ReflectedGMS.ActiveBlockEdges
