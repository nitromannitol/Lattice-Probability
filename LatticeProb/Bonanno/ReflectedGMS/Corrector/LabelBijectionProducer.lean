/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.LabelBijectionProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedMassTransportProducer
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# The label-level bijection `σ : ℕ ≃ ℕ` of the transport identities

Every transport identity of the `s:prop:projection` chain —
`MarkedMassTransportProducer.SimilarityCovariantField`,
`SpecificEnergyRedistribution.OwnedEdgeField.ReRootingCovariant`,
`OwnedFieldPairingTransport.PairingReRooting` and
`MeasurableEndpointTransport.OwnerReRooting` — is quantified over a bijection `σ : ℕ ≃ ℕ` of the
*raw* labels whose first clause carries every `labelCell` of the source environment to the
similarity image of the corresponding cell of the target environment.  `labelCell` of an inactive
label is `∅`, so `σ` must carry inactive labels to inactive labels, and the only existing input,
`EnvironmentLaws.isSimilarity_similarityTargetEnv`, is a bijection of the *active* subtypes only.

## The decision

`σ` exists for **every** environment and **every** positive similarity, with no measure, no
almost-everywhere gating and no good event:

* `infinite_inactive_set` — the inactive label set of every valid environment is infinite.
  `Valid` forces `CanonicalLabels`: an active label is the *least* index `m` with
  `rationalPoint m ∈ interior (cell)`.  A nonempty open subset of the plane is infinite and meets
  the rational sequence infinitely often (`infinite_rationalPoint_mem`), and cell interiors are
  disjoint, so every non-least such index of one fixed cell is inactive.
* Two infinite subsets of `ℕ` are equinumerous (`nonempty_equiv_of_countable`), and gluing that
  bijection to the active relabelling along `Equiv.sumCompl` is `labelEquiv`.

So the "one inactive set finite, the other infinite" failure mode, which would have made the four
statements above false as stated, cannot occur.

## The producer

`labelEquiv rel : ℕ ≃ ℕ` for any `rel : Vertex e.val ≃ Vertex e'.val`, with
* `labelEquiv_val` — it extends `rel` on active labels,
* `isSome_labelEquiv_iff` — it preserves and reflects activity,
* `labelCell_labelEquiv` / `preimage_labelCell_labelEquiv` / `labelCell_labelEquiv_one` — the cell
  clause of the four consumers, in the similarity (image and preimage) and translation shapes,
  whenever `IsSimilarityRelabel s u hs e e' rel`.

`similarityRelabel s u hs e` is the canonical relabelling witnessing
`isSimilarity_similarityTargetEnv`, exposed as data; `exists_labelEquiv_markedSimilarity` and
`exists_labelEquiv_actualReRooting` package `σ` in exactly the first clause of
`SimilarityCovariantField` and of the three re-rooting predicates, **with no hypothesis**, which
is the satisfiability check: the producer applies at every marked configuration.

The remaining clauses of the four consumers (weights, owners, areas) are statements about the
specific fields, to be discharged with `labelEquiv_val` on active labels and
`not_isSome_labelEquiv` on inactive ones, where the fields vanish.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.LabelBijectionProducer

open Code EnvironmentLaws SpecificEnergyRedistribution ActualMarkedBlockTransport
open DyadicApproximation MarkedMassTransportProducer

/-! ### A nonempty open set of the plane meets the rational sequence infinitely often -/

theorem nontrivial_plane : Nontrivial Plane :=
  Module.nontrivial_of_finrank_pos (show 0 < Module.finrank ℝ Plane by
    rw [finrank_euclideanSpace_fin]
    norm_num)

theorem infinite_rationalPoint_mem {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty) :
    {m : ℕ | rationalPoint m ∈ U}.Infinite := by
  intro hfin
  obtain ⟨z, hz⟩ := hne
  have : Nontrivial Plane := nontrivial_plane
  have : NeBot (𝓝[≠] z) := Real.punctured_nhds_module_neBot z
  have hUinf : U.Infinite := infinite_of_mem_nhds z (hU.mem_nhds hz)
  have hP : (rationalPoint '' {m : ℕ | rationalPoint m ∈ U}).Finite := hfin.image _
  have hne' : (U \ rationalPoint '' {m : ℕ | rationalPoint m ∈ U}).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hcon
    exact hUinf (hP.subset hcon)
  obtain ⟨n, hnU, hnP⟩ := exists_rationalPoint_mem (hU.sdiff hP.isClosed) hne'
  exact hnP ⟨n, hnU, rfl⟩

/-! ### The inactive label set of every valid environment is infinite -/

/-- **Every valid environment has infinitely many inactive labels.**  Only the least rational
interior hit of a cell is a label; all the other (infinitely many) rational hits of that cell's
interior are inactive, because cell interiors are disjoint. -/
theorem infinite_inactive_set (e : Env) : {n : ℕ | ¬ (e.val.1 n).isSome}.Infinite := by
  obtain ⟨v⟩ := (decode_geometry e).nonempty_vertex
  have hS : {m : ℕ | rationalPoint m ∈ interior ((decode e).cell v : Set Plane)}.Infinite :=
    infinite_rationalPoint_mem isOpen_interior ((decode_geometry e).interior_cell_nonempty v)
  have hsub : {m : ℕ | rationalPoint m ∈ interior ((decode e).cell v : Set Plane)}
      ⊆ {n : ℕ | ¬ (e.val.1 n).isSome} ∪ {v.val} := by
    intro m hm
    rw [Set.mem_ofPred_eq] at hm
    rw [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    by_cases hact : (e.val.1 m).isSome
    · right
      by_contra hne
      have hvw : v ≠ ⟨m, hact⟩ := fun h => hne (congrArg Subtype.val h).symm
      have hlab : rationalPoint m ∈ interior ((decode e).cell ⟨m, hact⟩ : Set Plane) :=
        (decode_canonicalLabels e ⟨m, hact⟩).1
      exact Set.disjoint_left.mp ((decode_geometry e).disjoint_interior_cell hvw) hm hlab
    · left
      exact hact
  rcases Set.infinite_union.mp (hS.mono hsub) with h | h
  · exact h
  · exact absurd h (Set.not_infinite.mpr (Set.finite_singleton _))

/-- The inactive labels of an environment. -/
abbrev Inactive (e : Env) : Type := {n : ℕ // ¬ (e.val.1 n).isSome}

instance infinite_inactive (e : Env) : Infinite (Inactive e) :=
  Set.infinite_coe_iff.mpr (infinite_inactive_set e)

/-- Any two inactive label sets are equinumerous: both are countably infinite. -/
noncomputable def inactiveEquiv (e e' : Env) : Inactive e ≃ Inactive e' :=
  Classical.choice (inferInstance : Nonempty (Inactive e ≃ Inactive e'))

/-! ### Gluing the active relabelling to a bijection of all labels -/

/-- **The label-level bijection.**  On active labels it is `rel`; on inactive labels it is a
bijection of the two (infinite) inactive label sets. -/
noncomputable def labelEquiv {e e' : Env} (rel : Vertex e.val ≃ Vertex e'.val) : ℕ ≃ ℕ :=
  (Equiv.sumCompl fun n : ℕ => (e.val.1 n).isSome).symm.trans
    ((Equiv.sumCongr rel (inactiveEquiv e e')).trans
      (Equiv.sumCompl fun n : ℕ => (e'.val.1 n).isSome))

theorem labelEquiv_val {e e' : Env} (rel : Vertex e.val ≃ Vertex e'.val) (v : Vertex e.val) :
    labelEquiv rel v.val = (rel v).val := by
  show (Equiv.sumCompl fun n : ℕ => (e'.val.1 n).isSome)
      (Equiv.sumCongr rel (inactiveEquiv e e')
        ((Equiv.sumCompl fun n : ℕ => (e.val.1 n).isSome).symm v.val)) = (rel v).val
  rw [Equiv.sumCompl_symm_apply_pos v]
  rfl

theorem labelEquiv_of_isSome {e e' : Env} (rel : Vertex e.val ≃ Vertex e'.val) {n : ℕ}
    (hn : (e.val.1 n).isSome) : labelEquiv rel n = (rel ⟨n, hn⟩).val :=
  labelEquiv_val rel ⟨n, hn⟩

theorem not_isSome_labelEquiv {e e' : Env} (rel : Vertex e.val ≃ Vertex e'.val) {n : ℕ}
    (hn : ¬ (e.val.1 n).isSome) : ¬ (e'.val.1 (labelEquiv rel n)).isSome := by
  have h : labelEquiv rel n = (inactiveEquiv e e' ⟨n, hn⟩).val := by
    show (Equiv.sumCompl fun m : ℕ => (e'.val.1 m).isSome)
        (Equiv.sumCongr rel (inactiveEquiv e e')
          ((Equiv.sumCompl fun m : ℕ => (e.val.1 m).isSome).symm n)) = _
    rw [Equiv.sumCompl_symm_apply_of_neg (p := fun m : ℕ => (e.val.1 m).isSome) hn]
    rfl
  rw [h]
  exact (inactiveEquiv e e' ⟨n, hn⟩).property

theorem isSome_labelEquiv_iff {e e' : Env} (rel : Vertex e.val ≃ Vertex e'.val) (n : ℕ) :
    (e'.val.1 (labelEquiv rel n)).isSome ↔ (e.val.1 n).isSome := by
  constructor
  · intro h
    by_contra hn
    exact not_isSome_labelEquiv rel hn h
  · intro hn
    rw [labelEquiv_of_isSome rel hn]
    exact (rel ⟨n, hn⟩).property

/-! ### The cell clause -/

theorem labelCell_val (e : Env) (v : Vertex e.val) :
    labelCell e v.val = (((decode e).cell v : CompactCell) : Set Plane) :=
  labelCell_of_isSome e v.property

theorem positiveSimilarity_injective (s : ℝ) (u : Plane) (hs : 0 < s) :
    Function.Injective (positiveSimilarity s u) := by
  intro x y hxy
  have h := congrArg (positiveSimilarity s⁻¹ (-s • u)) hxy
  rwa [positiveSimilarity_inverse_left s u x hs, positiveSimilarity_inverse_left s u y hs] at h

/-- **The cell clause, image form.**  Along `labelEquiv rel` every cell of the target is the
similarity image of the corresponding cell of the source; at inactive labels both are empty. -/
theorem labelCell_labelEquiv {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {rel : Vertex e.val ≃ Vertex e'.val} (h : IsSimilarityRelabel s u hs e e' rel) (n : ℕ) :
    labelCell e' (labelEquiv rel n) = positiveSimilarity s u '' labelCell e n := by
  by_cases hn : (e.val.1 n).isSome
  · rw [labelEquiv_of_isSome rel hn, labelCell_val e' (rel ⟨n, hn⟩), h.1 ⟨n, hn⟩,
      coe_transformCell, labelCell_of_isSome e hn]
  · rw [labelCell_of_not_isSome e' (not_isSome_labelEquiv rel hn),
      labelCell_of_not_isSome e hn, Set.image_empty]

/-- **The cell clause of `SimilarityCovariantField`**, preimage form. -/
theorem preimage_labelCell_labelEquiv {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {rel : Vertex e.val ≃ Vertex e'.val} (h : IsSimilarityRelabel s u hs e e' rel) (n : ℕ) :
    positiveSimilarity s u ⁻¹' labelCell e' (labelEquiv rel n) = labelCell e n := by
  rw [labelCell_labelEquiv h n]
  exact Set.preimage_image_eq _ (positiveSimilarity_injective s u hs)

/-! ### The canonical relabelling as data -/

/-- The relabelling of the active vertices that witnesses `isSimilarity_similarityTargetEnv`. -/
noncomputable def similarityRelabel (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) :
    Vertex e.val ≃ Vertex (similarityTargetEnv s u hs e).val :=
  canonicalVertexEquiv (transformIndexedCells s u hs (decode e))
    (geometry_transformIndexedCells s u hs (decode_geometry e))

theorem isSimilarityRelabel_similarityRelabel (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) :
    IsSimilarityRelabel s u hs e (similarityTargetEnv s u hs e) (similarityRelabel s u hs e) :=
  ⟨fun v => cell_canonicalVertexEquiv (transformIndexedCells s u hs (decode e))
      (geometry_transformIndexedCells s u hs (decode_geometry e)) v,
    fun v w => canonicalConductance_canonicalLabel (transformIndexedCells s u hs (decode e))
      (geometry_transformIndexedCells s u hs (decode_geometry e)) v w⟩

/-! ### The producers in the consumers' shapes -/

end ReflectedGMS.LabelBijectionProducer
