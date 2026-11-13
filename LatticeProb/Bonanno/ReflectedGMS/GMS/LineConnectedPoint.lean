/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.LineConnectedPoint at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid
import Mathlib.Util.AssertNoSorry

/-!
# Connectedness along lines is connectedness at points

GMS's connectedness along lines (`CellConfig.LineConnected`, Theorem 1.16 hypothesis 3, source
line 612 of `work/gms/src/lqg-walks-final.tex`) quantifies over the uncountably many nondegenerate
horizontal and vertical segments.  For a cell configuration it is equivalent to a pointwise
condition:

* `lineConnected_iff_forall_singleton` — `H.LineConnected ↔ ∀ z, (H.inducedGraph {z}).Connected`.
  (⇒) a short nondegenerate horizontal segment through `z` meets exactly the cells containing `z`
  (`exists_pos_mem_of_inter_closedBall`, `GMS/CodingValid.lean`: cells missing `z` are at positive distance and only
  finitely many cells come near `z`).  (⇐) the cells meeting a compact connected set `L` form a
  finite closed cover of `L`; if the induced graph were disconnected, a reachability class and its
  complement would cut `L` into two closed pieces, and a common point `p` would carry two cells in
  different classes, although `H({p})` is connected (`inducedGraph_connected_of_isCompact`).

The file also proves that connectedness along lines is invariant under the positive similarities
`H ↦ C(H − u)` (`lineConnected_similarity_iff`, `lineConnected_iff_of_isSimilar`), with no
cell-configuration hypothesis: a positive similarity carries horizontal (vertical) segments onto
horizontal (vertical) segments and the cells of `H` meeting `A` onto the cells of `C(H − u)` meeting
`C(A − u)`, with the same adjacency (`inducedGraphSimilarityIso`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace ReflectedGMS.GMS

namespace CellConfig

variable {H : CellConfig}

/-! ## Cells near a point

`exists_pos_mem_of_inter_closedBall` (`GMS/CodingValid.lean`): some closed ball `B̄(z, δ)` meets
only cells containing `z`. -/

/-- The horizontal segment `[z₀ − δ, z₀ + δ] × {z₁}` lies in the closed ball `B̄(z, δ)`. -/
theorem mem_closedBall_of_mem_horizontal {z p : Plane} {δ : ℝ}
    (hp : p ∈ horizontal (z 0 - δ) (z 0 + δ) (z 1)) : p ∈ Metric.closedBall z δ := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hδ : 0 ≤ δ := by linarith
  have habs : |p 0 - z 0| ≤ δ := abs_le.2 ⟨by linarith, by linarith⟩
  rw [Metric.mem_closedBall, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, h3, sub_self, abs_zero, Real.sqrt_le_left hδ]
  nlinarith [abs_nonneg (p 0 - z 0)]

/-! ## Lines ⇒ points -/

/-- **Connectedness along lines gives connectedness at every point**: a short nondegenerate
horizontal segment through `z` meets exactly the cells containing `z`. -/
theorem inducedGraph_singleton_connected_of_lineConnected (hH : H.IsCellConfiguration)
    (hL : H.LineConnected) (z : Plane) : (H.inducedGraph {z}).Connected := by
  obtain ⟨δ, hδ, hnear⟩ := exists_pos_mem_of_inter_closedBall hH z
  have hset :
      {K : H.cells | ((K : Set Plane) ∩ horizontal (z 0 - δ) (z 0 + δ) (z 1)).Nonempty} =
        {K : H.cells | ((K : Set Plane) ∩ {z}).Nonempty} := by
    ext K
    simp only [Set.mem_setOf_eq, Set.inter_singleton_nonempty]
    constructor
    · rintro ⟨p, hpK, hpL⟩
      exact hnear K K.2 ⟨p, hpK, mem_closedBall_of_mem_horizontal hpL⟩
    · intro hzK
      exact ⟨z, hzK, by linarith, by linarith, rfl⟩
  have h := hL.1 (z 0 - δ) (z 0 + δ) (z 1) (by linarith)
  unfold inducedGraph at h ⊢
  rw [hset] at h
  exact h

/-! ## Points ⇒ compact connected sets -/

/-- **Connectedness at points gives connectedness along every compact connected set.**  If every
point graph `H({z})` is preconnected, then for every compact connected `L` the graph `H(L)` of the
cells meeting `L` is connected. -/
theorem inducedGraph_connected_of_isCompact (hH : H.IsCellConfiguration)
    (hpt : ∀ z : Plane, (H.inducedGraph {z}).Preconnected) {L : Set Plane} (hLc : IsCompact L)
    (hLconn : IsConnected L) : (H.inducedGraph L).Connected := by
  classical
  have hWfin : {K : H.cells | ((K : Set Plane) ∩ L).Nonempty}.Finite :=
    ((finite_restrict_of_isCompact hH hLc).preimage Subtype.val_injective.injOn).subset
      fun K hK => ⟨K.2, hK⟩
  haveI : Finite {K : H.cells | ((K : Set Plane) ∩ L).Nonempty} := hWfin.to_subtype
  have hcover : ∀ p ∈ L, ∃ K : {K : H.cells | ((K : Set Plane) ∩ L).Nonempty},
      p ∈ (((K : H.cells) : Cell) : Set Plane) := by
    intro p hp
    have hp' : p ∈ ⋃ K ∈ H.cells, (K : Set Plane) := by
      rw [hH.iUnion_eq_univ]
      exact Set.mem_univ p
    obtain ⟨K, hK, hpK⟩ := Set.mem_iUnion₂.1 hp'
    exact ⟨⟨⟨K, hK⟩, p, hpK, hp⟩, hpK⟩
  have hpre : (H.inducedGraph L).Preconnected := by
    intro u₀ w₀
    by_contra hnr
    let R : Set {K : H.cells | ((K : Set Plane) ∩ L).Nonempty} :=
      {q | (H.inducedGraph L).Reachable u₀ q}
    have hFA : IsClosed (⋃ q ∈ R, (((q : H.cells) : Cell) : Set Plane)) :=
      (Set.toFinite R).isClosed_biUnion fun q _ => ((q : H.cells) : Cell).isCompact.isClosed
    have hFB : IsClosed (⋃ q ∈ Rᶜ, (((q : H.cells) : Cell) : Set Plane)) :=
      (Set.toFinite Rᶜ).isClosed_biUnion fun q _ => ((q : H.cells) : Cell).isCompact.isClosed
    have hcov : L ⊆ (⋃ q ∈ R, (((q : H.cells) : Cell) : Set Plane)) ∪
        ⋃ q ∈ Rᶜ, (((q : H.cells) : Cell) : Set Plane) := by
      intro p hp
      obtain ⟨K, hpK⟩ := hcover p hp
      by_cases hK : K ∈ R
      · exact Or.inl (Set.mem_biUnion hK hpK)
      · exact Or.inr (Set.mem_biUnion hK hpK)
    have hA : (L ∩ ⋃ q ∈ R, (((q : H.cells) : Cell) : Set Plane)).Nonempty := by
      obtain ⟨p, hpc, hpL⟩ := u₀.2
      exact ⟨p, hpL, Set.mem_biUnion (show u₀ ∈ R from SimpleGraph.Reachable.refl u₀) hpc⟩
    have hB : (L ∩ ⋃ q ∈ Rᶜ, (((q : H.cells) : Cell) : Set Plane)).Nonempty := by
      obtain ⟨p, hpc, hpL⟩ := w₀.2
      exact ⟨p, hpL, Set.mem_biUnion (show w₀ ∈ Rᶜ from hnr) hpc⟩
    obtain ⟨p, hpL, hpA, hpB⟩ :=
      isPreconnected_closed_iff.1 hLconn.isPreconnected _ _ hFA hFB hcov hA hB
    obtain ⟨q, hqR, hpq⟩ := Set.mem_iUnion₂.1 hpA
    obtain ⟨q', hq'R, hpq'⟩ := Set.mem_iUnion₂.1 hpB
    have hle : {K : H.cells | ((K : Set Plane) ∩ {p}).Nonempty} ≤
        {K : H.cells | ((K : Set Plane) ∩ L).Nonempty} := fun K hK =>
      ⟨p, Set.inter_singleton_nonempty.1 hK, hpL⟩
    have hr : (H.inducedGraph {p}).Reachable
        ⟨(q : H.cells), Set.inter_singleton_nonempty.2 hpq⟩
        ⟨(q' : H.cells), Set.inter_singleton_nonempty.2 hpq'⟩ := hpt p _ _
    have hr' := hr.map (H.graph.induceHomOfLE hle).toHom
    exact hq'R (hqR.trans hr')
  obtain ⟨p, hp⟩ := hLconn.nonempty
  obtain ⟨K, -⟩ := hcover p hp
  exact (SimpleGraph.connected_iff _).2 ⟨hpre, ⟨K⟩⟩

/-- **Connectedness along lines is connectedness at points.**  For a cell configuration, `H(L)` is
connected for every nondegenerate horizontal or vertical segment `L` if and only if `H({z})` is
connected for every point `z`. -/
theorem lineConnected_iff_forall_singleton (hH : H.IsCellConfiguration) :
    H.LineConnected ↔ ∀ z : Plane, (H.inducedGraph {z}).Connected := by
  refine ⟨fun hL z => inducedGraph_singleton_connected_of_lineConnected hH hL z, fun hpt => ?_⟩
  have hpre : ∀ z : Plane, (H.inducedGraph {z}).Preconnected := fun z => (hpt z).preconnected
  refine ⟨fun a b y hab => ?_, fun x a b hab => ?_⟩
  · refine inducedGraph_connected_of_isCompact hH hpre (isCompact_horizontal a b y)
      ⟨?_, isPreconnected_horizontal a b y⟩
    rw [horizontal_eq_image]
    exact (Set.nonempty_Icc.2 hab.le).image _
  · exact inducedGraph_connected_of_isCompact hH hpre (isCompact_vertical x a b)
      ⟨vertical_nonempty hab.le, isPreconnected_vertical x a b⟩

/-! ## Invariance under positive similarities -/

section Similarity

variable (s : ℝ) (u : Plane) (hs : 0 < s)

/-! The cell-level helpers `mapCell_symm_transformCell`, `transformCell_mapCell_symm`,
`transformCell_injective`, `similarity_c_transformCell` and the forward direction
`lineConnected_similarity` are in `GMS/CodingValid.lean`. -/

/-- **A positive similarity is an isomorphism of induced graphs**: the cells of `H` meeting `A`
correspond to the cells of `C(H − u)` meeting `C(A − u)`, with the same adjacency. -/
noncomputable def inducedGraphSimilarityIso (H : CellConfig) (A : Set Plane) :
    H.inducedGraph A ≃g
      (H.similarity s u hs).inducedGraph (positiveSimilarity s u '' A) where
  toFun K := ⟨⟨transformCell s u hs K.1.1, K.1.1, K.1.2, rfl⟩, by
    obtain ⟨p, hpK, hpA⟩ := K.2
    exact ⟨positiveSimilarity s u p, Set.mem_image_of_mem _ hpK, Set.mem_image_of_mem _ hpA⟩⟩
  invFun K := ⟨⟨mapCell (positiveSimilarityHomeomorph s u hs).symm K.1.1, by
      obtain ⟨K₀, hK₀, hK⟩ := K.1.2
      rw [← hK, mapCell_symm_transformCell]
      exact hK₀⟩, by
    obtain ⟨p, hpK, a, ha, hfa⟩ := K.2
    refine ⟨a, ?_, ha⟩
    show a ∈ (positiveSimilarityHomeomorph s u hs).symm '' (K.1.1 : Set Plane)
    refine ⟨p, hpK, ?_⟩
    rw [← hfa]
    exact positiveSimilarity_inverse_left s u a hs⟩
  left_inv K := Subtype.ext (Subtype.ext (mapCell_symm_transformCell s u hs K.1.1))
  right_inv K := Subtype.ext (Subtype.ext (transformCell_mapCell_symm s u hs K.1.1))
  map_rel_iff' {K K'} := by
    change (_ ≠ _ ∧ 0 < (H.similarity s u hs).c (transformCell s u hs K.1.1)
        (transformCell s u hs K'.1.1) ∧
        0 < (H.similarity s u hs).c (transformCell s u hs K'.1.1) (transformCell s u hs K.1.1)) ↔
      ((K : H.cells) ≠ K' ∧ 0 < H.c K.1 K'.1 ∧ 0 < H.c K'.1 K.1)
    rw [similarity_c_transformCell, similarity_c_transformCell]
    refine and_congr (not_congr ⟨fun h => ?_, fun h => ?_⟩) Iff.rfl
    · have h' : transformCell s u hs K.1.1 = transformCell s u hs K'.1.1 :=
        congrArg Subtype.val h
      exact Subtype.ext (transformCell_injective s u hs h')
    · exact Subtype.ext (congrArg (fun L : H.cells => transformCell s u hs (L : Cell)) h)

theorem inducedGraph_similarity_image_connected_iff (H : CellConfig) (A : Set Plane) :
    ((H.similarity s u hs).inducedGraph (positiveSimilarity s u '' A)).Connected ↔
      (H.inducedGraph A).Connected :=
  (inducedGraphSimilarityIso s u hs H A).connected_iff.symm

/-- **Connectedness along lines is invariant under positive similarities** `H ↦ C(H − u)`. -/
theorem lineConnected_similarity_iff (H : CellConfig) :
    (H.similarity s u hs).LineConnected ↔ H.LineConnected := by
  have hinv : 0 < s⁻¹ := inv_pos.2 hs
  have himg : ∀ A : Set Plane,
      positiveSimilarity s u '' A = positiveSimilarity s⁻¹ (-s • u) ⁻¹' A := fun A =>
    congrFun (Set.image_eq_preimage_of_inverse
      (fun z => positiveSimilarity_inverse_left s u z hs)
      (fun z => positiveSimilarity_inverse_right s u z hs)) A
  refine ⟨fun hL' => ?_, lineConnected_similarity s u hs⟩
  obtain ⟨hh, hv⟩ := hL'
  refine ⟨fun a b y hab => ?_, fun x a b hab => ?_⟩
  · rw [← inducedGraph_similarity_image_connected_iff s u hs H, himg,
      preimage_positiveSimilarity_horizontal s⁻¹ (-s • u) hinv, inv_inv]
    exact hh _ _ _ (by linarith [mul_lt_mul_of_pos_left hab hs])
  · rw [← inducedGraph_similarity_image_connected_iff s u hs H, himg,
      preimage_positiveSimilarity_vertical s⁻¹ (-s • u) hinv, inv_inv]
    exact hv _ _ _ (by linarith [mul_lt_mul_of_pos_left hab hs])

/-- The same invariance in the direction `H ⇒ C(H − u)`. -/
theorem lineConnected_iff_lineConnected_similarity (H : CellConfig) :
    H.LineConnected ↔ (H.similarity s u hs).LineConnected :=
  (lineConnected_similarity_iff s u hs H).symm

end Similarity

end CellConfig

/-- **Connectedness along lines is similarity invariant on the GMS space**: for `H' = C(H − u)`,
`H` is connected along lines iff `H'` is. -/
theorem lineConnected_iff_of_isSimilar {s : ℝ} {u : Plane} {hs : 0 < s} {H H' : GMSSpace}
    (h : IsSimilar s u hs H H') : H.1.LineConnected ↔ H'.1.LineConnected := by
  rw [h, CellConfig.lineConnected_similarity_iff]

end ReflectedGMS.GMS

assert_no_sorry ReflectedGMS.GMS.CellConfig.inducedGraph_singleton_connected_of_lineConnected
assert_no_sorry ReflectedGMS.GMS.CellConfig.inducedGraph_connected_of_isCompact
assert_no_sorry ReflectedGMS.GMS.CellConfig.lineConnected_iff_forall_singleton
assert_no_sorry ReflectedGMS.GMS.CellConfig.inducedGraphSimilarityIso
assert_no_sorry ReflectedGMS.GMS.CellConfig.lineConnected_similarity_iff
assert_no_sorry ReflectedGMS.GMS.lineConnected_iff_of_isSimilar

#print axioms ReflectedGMS.GMS.CellConfig.lineConnected_iff_forall_singleton
#print axioms ReflectedGMS.GMS.CellConfig.lineConnected_similarity_iff
#print axioms ReflectedGMS.GMS.lineConnected_iff_of_isSimilar
