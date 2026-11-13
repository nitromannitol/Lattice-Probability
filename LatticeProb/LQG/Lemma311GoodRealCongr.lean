import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15ACore
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Graph
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Walk
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.Chain
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph

/-!
# [18] Lemma 3.11's good event sees the boundary-length path only through the edge multiplicities

The `ε`-mated-CRT map `MatedCRT.graph ε ω h` of a boundary-length path `ω` has the explicit edge
type `MatedCRT.Edge ε ω` of labelled triples `(x, y, side)`, so two paths with the same edge
multiplicities give multigraphs on different edge types. This file shows that every ingredient of
[18] (3.35) is invariant under such a relabelling of the edges:

* `Markov.chainLaw_map_of_kernel_map`: the image of a Markov chain under a map intertwining the
  transition kernels is the chain of the image kernel;
* `LFMultigraph.adj_eq_of_edgeEquiv`, `LFMultigraph.disconnects_iff_of_edgeEquiv`: a bijection of
  the edges preserving both ends preserves the adjacency and graph disconnection;
* `LFMultigraph.walkLaw_vertexPath_of_edgeEquiv`: it preserves the law of the vertex path of simple
  random walk (the walk law itself lives on the edge-end states `V ⊕ (E × Bool)`; it is carried by
  the induced relabelling of states, `LFMultigraph.map_walkLaw_stateRelabel`);
* `LFMultigraph.lemma311Holds_iff_of_edgeEquiv`: (3.35) holds for a cellular embedding iff it
  holds for the cellular embedding of the relabelled multigraph with the same cells;
* `MatedCRT.edgeMult` (the number of edges joining `x < y`), `MatedCRT.edgeEquivOfEdgeMult`, and
  the main result `MatedCRT.exists_lemma311Holds_iff_of_edgeMult`: for two paths with the same
  edge multiplicities and one curve `c`, the mesh-`ε` map of the first is locally finite with a
  cellular embedding by the cells `c([ε(x−1), εx])` satisfying (3.35) iff the same holds for the
  second.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

namespace MatedCRTHarmonic

/-! ### Images of Markov chains -/

namespace Markov

variable {S S' : Type*} [MeasurableSpace S] [MeasurableSpace S']

/-- The prefix of length `n + 1` of the chain law is the prefix of length `n` followed by one
transition. -/
theorem chainLaw_map_frestrictLe_succ (κ : Kernel S S) [IsMarkovKernel κ] (z : S) (n : ℕ) :
    (chainLaw κ z).map (frestrictLe (n + 1)) =
      ((chainLaw κ z).map (frestrictLe n) ⊗ₘ histKernel κ n).map (histAppend n) :=
  prefix_succ (histKernel κ) (Measure.dirac z) n

/-- **Image of a Markov chain.** If `f` carries the transition kernel `κ` to `κ'`, that is
`(κ s).map f = κ' (f s)` for every state `s`, then applying `f` to every coordinate carries the
chain law `P_z` of `κ` to the chain law `P'_{f z}` of `κ'`. -/
theorem chainLaw_map_of_kernel_map (κ : Kernel S S) [IsMarkovKernel κ] (κ' : Kernel S' S')
    [IsMarkovKernel κ'] {f : S → S'} (hf : Measurable f) (hmap : ∀ s, (κ s).map f = κ' (f s))
    (z : S) : (chainLaw κ z).map (fun ω n => f (ω n)) = chainLaw κ' (f z) := by
  have hF : Measurable fun (ω : ℕ → S) (n : ℕ) => f (ω n) :=
    Measurable.of_eval fun n => hf.comp (measurable_pi_apply n)
  have hFk : ∀ k : ℕ, Measurable fun (h : Finset.Iic k → S) (i : Finset.Iic k) => f (h i) :=
    fun k => Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)
  have hpre : ∀ n : ℕ, ((chainLaw κ z).map (frestrictLe n)).map
      (fun (h : Finset.Iic n → S) (i : Finset.Iic n) => f (h i)) =
      (chainLaw κ' (f z)).map (frestrictLe n) := by
    intro n
    induction n with
    | zero =>
      rw [chainLaw_initialHistory, chainLaw_initialHistory, Measure.map_dirac' (hFk 0)]
    | succ n ih =>
      have hcomm : (fun (h : Finset.Iic (n + 1) → S) (i : Finset.Iic (n + 1)) => f (h i)) ∘
            histAppend (S := S) n =
          histAppend (S := S') n ∘
            Prod.map (fun (h : Finset.Iic n → S) (i : Finset.Iic n) => f (h i)) f := by
        funext q i
        simp only [Function.comp_apply, histAppend, Prod.map_fst, Prod.map_snd]
        split_ifs <;> rfl
      have hker : ∀ h : Finset.Iic n → S,
          (histKernel κ n h).map f = histKernel κ' n (fun i => f (h i)) := by
        intro h
        rw [histKernel_apply, histKernel_apply]
        exact hmap _
      rw [chainLaw_map_frestrictLe_succ, chainLaw_map_frestrictLe_succ,
        Measure.map_map (hFk (n + 1)) (measurable_histAppend (S := S) n), hcomm,
        ← Measure.map_map (measurable_histAppend (S := S') n) ((hFk n).prodMap hf),
        compProd_map_prod_of_kernel_map _ _ _ _ _ (hFk n) hf hker, ih]
  refine measure_eq_of_prefix_eq _ _ fun n => ?_
  rw [Measure.map_map (measurable_frestrictLe n) hF, ← hpre n,
    Measure.map_map (hFk n) (measurable_frestrictLe n)]
  rfl

end Markov

/-! ### Relabelling the edges of a locally finite multigraph -/

namespace LFMultigraph

variable {V E E' : Type*}

/-- A bijection of the edges preserving both ends preserves the adjacency. -/
theorem adj_eq_of_edgeEquiv (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E')
    (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) :
    G'.adj = G.adj := by
  have hrel : (fun x y : V => ∃ e', G'.src e' = x ∧ G'.tgt e' = y) =
      (fun x y : V => ∃ e, G.src e = x ∧ G.tgt e = y) := by
    funext x y
    apply propext
    constructor
    · rintro ⟨e', h1, h2⟩
      exact ⟨σ.symm e', by rw [← hs, σ.apply_symm_apply, h1],
        by rw [← ht, σ.apply_symm_apply, h2]⟩
    · rintro ⟨e, h1, h2⟩
      exact ⟨σ e, by rw [hs, h1], by rw [ht, h2]⟩
  exact congrArg SimpleGraph.fromRel hrel

/-- A bijection of the edges preserving both ends preserves graph disconnection. -/
theorem disconnects_iff_of_edgeEquiv (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E')
    (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) (U S T : Set V) :
    G'.Disconnects U S T ↔ G.Disconnects U S T := by
  unfold LFMultigraph.Disconnects
  rw [adj_eq_of_edgeEquiv G G' σ hs ht]

/-- A bijection of the edges preserving both ends preserves the tail of every dart. -/
theorem dsrc_of_edgeEquiv (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E')
    (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) (e : E) (b : Bool) :
    G'.dsrc (σ e, b) = G.dsrc (e, b) := by
  cases b
  · exact hs e
  · exact ht e

/-- The darts out of `x` of the relabelled multigraph are the relabelled darts out of `x`. -/
theorem outDarts_eq_map_of_edgeEquiv (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E')
    (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) (x : V) :
    G'.outDarts x = (G.outDarts x).map (Equiv.prodCongr σ (Equiv.refl Bool)).toEmbedding := by
  ext ⟨e', b⟩
  rw [Harmonic.mem_outDarts, Finset.mem_map]
  constructor
  · intro h
    refine ⟨(σ.symm e', b), ?_, ?_⟩
    · rw [Harmonic.mem_outDarts, ← dsrc_of_edgeEquiv G G' σ hs ht, σ.apply_symm_apply]
      exact h
    · simp
  · rintro ⟨⟨e, b'⟩, hd, he⟩
    rw [← he]
    rw [Harmonic.mem_outDarts] at hd
    exact (dsrc_of_edgeEquiv G G' σ hs ht e b').trans hd

/-- A bijection of the edges preserving both ends preserves the degrees. -/
theorem deg_eq_of_edgeEquiv (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E')
    (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) (x : V) :
    G'.deg x = G.deg x := by
  unfold LFMultigraph.deg
  rw [outDarts_eq_map_of_edgeEquiv G G' σ hs ht, Finset.card_map]

/-- The relabelling of the edge-end states of simple random walk induced by a bijection of the
edges. -/
def stateRelabel (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E') :
    G.State ≃ᵐ G'.State where
  toEquiv := Equiv.sumCongr (Equiv.refl V) (Equiv.prodCongr σ (Equiv.refl Bool))
  measurable_toFun := measurable_from_top
  measurable_invFun := measurable_from_top

/-- The relabelling of states preserves the current vertex. -/
theorem stateVertex_stateRelabel (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E')
    (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) (s : G.State) :
    G'.stateVertex (stateRelabel G G' σ s) = G.stateVertex s := by
  rcases s with x | ⟨e, b⟩
  · rfl
  · cases b
    · exact ht e
    · exact hs e

/-- The relabelling of states carries the one-step law of simple random walk from `x` to that of
the relabelled multigraph. -/
theorem map_stepMeasure_stateRelabel (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E')
    (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) (x : V) :
    (G.stepMeasure x).map (stateRelabel G G' σ) = G'.stepMeasure x := by
  ext A hA
  have hA' : MeasurableSet (stateRelabel G G' σ ⁻¹' A) := (stateRelabel G G' σ).measurable hA
  rw [Measure.map_apply (stateRelabel G G' σ).measurable hA]
  unfold LFMultigraph.stepMeasure
  rw [deg_eq_of_edgeEquiv G G' σ hs ht, outDarts_eq_map_of_edgeEquiv G G' σ hs ht,
    Finset.sum_map]
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  exact (Measure.dirac_apply' (show G.State from Sum.inr d) hA').trans
    (Measure.dirac_apply' (show G'.State from Sum.inr (σ d.1, d.2)) hA).symm

/-- The relabelling of states intertwines the transition kernels of simple random walk. -/
theorem map_walkKernel_stateRelabel (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E')
    (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) (s : G.State) :
    (G.walkKernel s).map (stateRelabel G G' σ) = G'.walkKernel (stateRelabel G G' σ s) := by
  show (G.stepMeasure (G.stateVertex s)).map (stateRelabel G G' σ) =
    G'.stepMeasure (G'.stateVertex (stateRelabel G G' σ s))
  rw [stateVertex_stateRelabel G G' σ hs ht, map_stepMeasure_stateRelabel G G' σ hs ht]

/-- **The walk law of the relabelled multigraph** is the image of the walk law under the
relabelling of states. -/
theorem map_walkLaw_stateRelabel (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E')
    (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) (x : V) :
    (G.walkLaw x).map (fun ξ n => stateRelabel G G' σ (ξ n)) = G'.walkLaw x :=
  Markov.chainLaw_map_of_kernel_map G.walkKernel G'.walkKernel (stateRelabel G G' σ).measurable
    (map_walkKernel_stateRelabel G G' σ hs ht) (show G.State from Sum.inl x)

/-- **The vertex path of simple random walk has the same law** on two multigraphs related by a
bijection of the edges preserving both ends: for every property `P` of vertex paths (measurable or
not), the walk laws from `x` give `{P}` the same mass. -/
theorem walkLaw_vertexPath_of_edgeEquiv (G : LFMultigraph V E) (G' : LFMultigraph V E')
    (σ : E ≃ E') (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e)
    (P : (ℕ → V) → Prop) (x : V) :
    G'.walkLaw x {ξ | P (G'.vertexPath ξ)} = G.walkLaw x {ξ | P (G.vertexPath ξ)} := by
  rw [← map_walkLaw_stateRelabel G G' σ hs ht x]
  have hΦ : (fun (ξ : ℕ → G.State) (n : ℕ) => stateRelabel G G' σ (ξ n)) =
      ⇑(MeasurableEquiv.piCongrRight fun _ : ℕ => stateRelabel G G' σ) := rfl
  rw [hΦ, MeasurableEquiv.map_apply]
  congr 1
  ext ξ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have hv : G'.vertexPath ((MeasurableEquiv.piCongrRight fun _ : ℕ => stateRelabel G G' σ) ξ) =
      G.vertexPath ξ := funext fun n => stateVertex_stateRelabel G G' σ hs ht (ξ n)
  rw [hv]

end LFMultigraph

/-- A cellular embedding of `G` is a cellular embedding, with the same cells, of every multigraph
on the same vertices with the same adjacency. -/
def CellularEmbedding.ofAdjEq {V E E' : Type*} {G : LFMultigraph V E} {G' : LFMultigraph V E'}
    {o : V} (H : CellularEmbedding G o) (hadj : G'.adj = G.adj) : CellularEmbedding G' o where
  cell := H.cell
  isCompact_cell := H.isCompact_cell
  isConnected_cell := H.isConnected_cell
  interior_cell_nonempty := H.interior_cell_nonempty
  locallyFinite_cell := H.locallyFinite_cell
  iUnion_cell := H.iUnion_cell
  volume_inter_cell := H.volume_inter_cell
  inter_of_adj x y hxy := H.inter_of_adj x y (by rw [← hadj]; exact hxy)
  zero_mem_root := H.zero_mem_root

namespace LFMultigraph

variable {V E E' : Type*}

/-- **[18] (3.35) is invariant under relabelling the edges**: for multigraphs related by a
bijection of the edges preserving both ends and cellular embeddings with the same cells, (3.35)
holds for one iff it holds for the other. -/
theorem lemma311Holds_iff_of_edgeEquiv (G : LFMultigraph V E) (G' : LFMultigraph V E')
    (σ : E ≃ E') (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) {o : V}
    (H : CellularEmbedding G o) (H' : CellularEmbedding G' o) (hcell : H'.cell = H.cell)
    {ε ρ β p : ℝ} :
    GMSMain.T15A.Lemma311Holds H' ε ρ β p ↔ GMSMain.T15A.Lemma311Holds H ε ρ β p := by
  have hw : ∀ (z : ℂ) (r : ℝ) (x : V),
      G'.walkLaw x {ξ | GMSMain.T15A.Lemma311Event G' H.cell z r (G'.vertexPath ξ)} =
        G.walkLaw x {ξ | GMSMain.T15A.Lemma311Event G H.cell z r (G.vertexPath ξ)} := by
    intro z r x
    rw [walkLaw_vertexPath_of_edgeEquiv G G' σ hs ht
      (GMSMain.T15A.Lemma311Event G' H.cell z r) x]
    simp only [GMSMain.T15A.Lemma311Event, GMSMain.T15A.DisconnectsBeforeHit,
      disconnects_iff_of_edgeEquiv G G' σ hs ht]
  unfold GMSMain.T15A.Lemma311Holds
  rw [hcell]
  simp only [hw]

end LFMultigraph

/-! ### Edge multiplicities of the mated-CRT map -/

namespace MatedCRT

/-- **Edge multiplicity of the `ε`-mated-CRT map of `ω`**: the number of sides `b` (`false` for
`L`, `true` for `R`) for which `(x, y, b)` is an edge, that is, the number of edges joining
`x < y` ([18] (1.1)); it is `0` unless `x < y`. It does not presuppose local finiteness. -/
def edgeMult (ε : ℝ) (ω : Path2) (x y : ℤ) : ℕ :=
  Nat.card {b : Bool // IsEdge ε ω (x, y, b)}

/-- No edge `(x, y, b)` has `y ≤ x`. -/
theorem edgeMult_eq_zero_of_le {ε : ℝ} {ω : Path2} {x y : ℤ} (hyx : y ≤ x) :
    edgeMult ε ω x y = 0 := by
  have : IsEmpty {b : Bool // IsEdge ε ω (x, y, b)} :=
    ⟨fun b => absurd b.2.1 (not_lt.mpr hyx)⟩
  exact Nat.card_of_isEmpty

/-- **Darts of the `ε`-mated-CRT map.** For `x < y`, the darts from `x` to `y` are the edges
`(x, y, b)` traversed forwards, so their number is the edge multiplicity `edgeMult ε ω x y`. -/
theorem card_filter_outDarts_graph_of_lt {ε : ℝ} {ω : Path2} (h : IsLocallyFinite ε ω) {x y : ℤ}
    (hxy : x < y) :
    (((graph ε ω h).outDarts x).filter (fun d => (graph ε ω h).dtgt d = y)).card =
      edgeMult ε ω x y := by
  have hsF : ∀ e : Edge ε ω, (graph ε ω h).dsrc (e, false) = e.1.1 := fun _ => rfl
  have htF : ∀ e : Edge ε ω, (graph ε ω h).dtgt (e, false) = e.1.2.1 := fun _ => rfl
  have hsT : ∀ e : Edge ε ω, (graph ε ω h).dsrc (e, true) = e.1.2.1 := fun _ => rfl
  have htT : ∀ e : Edge ε ω, (graph ε ω h).dtgt (e, true) = e.1.1 := fun _ => rfl
  have hmem : ∀ d : (graph ε ω h).Dart,
      d ∈ ((graph ε ω h).outDarts x).filter (fun d => (graph ε ω h).dtgt d = y) ↔
        d.2 = false ∧ d.1.1.1 = x ∧ d.1.1.2.1 = y := by
    rintro ⟨⟨⟨a, c, t⟩, he⟩, b⟩
    have hac : a < c := he.1
    rw [Finset.mem_filter, Harmonic.mem_outDarts]
    cases b
    · rw [hsF, htF]
      exact ⟨fun hd => ⟨rfl, hd⟩, fun hd => hd.2⟩
    · rw [hsT, htT]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : c = x := h1
        have h2' : a = y := h2
        exfalso
        omega
      · rintro ⟨h1, -⟩
        simp at h1
  have hedge : ∀ d : (graph ε ω h).Dart,
      d ∈ ((graph ε ω h).outDarts x).filter (fun d => (graph ε ω h).dtgt d = y) →
        IsEdge ε ω (x, y, d.1.1.2.2) := by
    rintro ⟨⟨⟨a, c, t⟩, he⟩, b⟩ hd
    obtain ⟨-, h1, h2⟩ := (hmem _).1 hd
    have h1' : a = x := h1
    have h2' : c = y := h2
    subst h1' h2'
    exact he
  rw [edgeMult, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun d => ⟨d.1.1.1.2.2, hedge d.1 d.2⟩
      invFun := fun b => ⟨(⟨(x, y, b.1), b.2⟩, false), (hmem _).2 ⟨rfl, rfl, rfl⟩⟩
      left_inv := ?_
      right_inv := fun _ => rfl }
  rintro ⟨⟨⟨⟨a, c, t⟩, he⟩, b⟩, hd⟩
  obtain ⟨hb, h1, h2⟩ := (hmem _).1 hd
  have hb' : b = false := hb
  have h1' : a = x := h1
  have h2' : c = y := h2
  subst hb' h1' h2'
  rfl

/-- Equal numbers of darts between every two vertices of the `ε`-mated-CRT maps of `ω` and `ω'`
give equal edge multiplicities. -/
theorem edgeMult_eq_of_card_filter_outDarts {ε : ℝ} {ω ω' : Path2} (h : IsLocallyFinite ε ω)
    (h' : IsLocallyFinite ε ω')
    (hdarts : ∀ x y : ℤ,
      (((graph ε ω h).outDarts x).filter (fun d => (graph ε ω h).dtgt d = y)).card =
        (((graph ε ω' h').outDarts x).filter (fun d => (graph ε ω' h').dtgt d = y)).card)
    (x y : ℤ) : edgeMult ε ω x y = edgeMult ε ω' x y := by
  rcases lt_or_ge x y with hxy | hyx
  · rw [← card_filter_outDarts_graph_of_lt h hxy, ← card_filter_outDarts_graph_of_lt h' hxy,
      hdarts]
  · rw [edgeMult_eq_zero_of_le hyx, edgeMult_eq_zero_of_le hyx]

/-- The bijection of edges induced by bijections, for every pair of ends, of the sides carrying an
edge. -/
def edgeEquivOfSides {ε : ℝ} {ω ω' : Path2}
    (τ : ∀ x y : ℤ, {b : Bool // IsEdge ε ω (x, y, b)} ≃ {b : Bool // IsEdge ε ω' (x, y, b)}) :
    Edge ε ω ≃ Edge ε ω' where
  toFun e := ⟨(e.1.1, e.1.2.1, (τ e.1.1 e.1.2.1 ⟨e.1.2.2, e.2⟩).1),
    (τ e.1.1 e.1.2.1 ⟨e.1.2.2, e.2⟩).2⟩
  invFun e := ⟨(e.1.1, e.1.2.1, ((τ e.1.1 e.1.2.1).symm ⟨e.1.2.2, e.2⟩).1),
    ((τ e.1.1 e.1.2.1).symm ⟨e.1.2.2, e.2⟩).2⟩
  left_inv := by
    rintro ⟨⟨x, y, b⟩, he⟩
    apply Subtype.ext
    simp
  right_inv := by
    rintro ⟨⟨x, y, b⟩, he⟩
    apply Subtype.ext
    simp

/-- **Equal edge multiplicities give a relabelling of the edges**: a bijection between the edges
of the `ε`-mated-CRT maps of `ω` and `ω'` preserving both ends. -/
def edgeEquivOfEdgeMult {ε : ℝ} {ω ω' : Path2}
    (hmult : ∀ x y : ℤ, edgeMult ε ω x y = edgeMult ε ω' x y) : Edge ε ω ≃ Edge ε ω' :=
  edgeEquivOfSides fun x y => Classical.choice (Finite.card_eq.mp
    (hmult x y : Nat.card {b : Bool // IsEdge ε ω (x, y, b)} =
      Nat.card {b : Bool // IsEdge ε ω' (x, y, b)}))

/-- Local finiteness of the `ε`-mated-CRT map depends only on the edge multiplicities. -/
theorem isLocallyFinite_of_edgeMult {ε : ℝ} {ω ω' : Path2}
    (hmult : ∀ x y : ℤ, edgeMult ε ω x y = edgeMult ε ω' x y) (h : IsLocallyFinite ε ω) :
    IsLocallyFinite ε ω' := by
  intro x
  refine ((h x).image (edgeEquivOfEdgeMult hmult)).subset fun e' he' => ?_
  exact ⟨(edgeEquivOfEdgeMult hmult).symm e', he',
    (edgeEquivOfEdgeMult hmult).apply_symm_apply e'⟩

/-- Local finiteness of the `ε`-mated-CRT map depends only on the edge multiplicities. -/
theorem isLocallyFinite_iff_of_edgeMult {ε : ℝ} {ω ω' : Path2}
    (hmult : ∀ x y : ℤ, edgeMult ε ω x y = edgeMult ε ω' x y) :
    IsLocallyFinite ε ω ↔ IsLocallyFinite ε ω' :=
  ⟨isLocallyFinite_of_edgeMult hmult, isLocallyFinite_of_edgeMult fun x y => (hmult x y).symm⟩

/-- One direction of `exists_lemma311Holds_iff_of_edgeMult`. -/
theorem exists_lemma311Holds_of_edgeMult {ε ρ β p : ℝ} {ω ω' : Path2} (c : C(ℝ, ℂ))
    (hmult : ∀ x y : ℤ, edgeMult ε ω x y = edgeMult ε ω' x y)
    (hgood : ∃ h : IsLocallyFinite ε ω, ∃ H : CellularEmbedding (graph ε ω h) 0,
      (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
        GMSMain.T15A.Lemma311Holds H ε ρ β p) :
    ∃ h : IsLocallyFinite ε ω', ∃ H : CellularEmbedding (graph ε ω' h) 0,
      (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
        GMSMain.T15A.Lemma311Holds H ε ρ β p := by
  obtain ⟨h, H, hcell, h311⟩ := hgood
  have h' : IsLocallyFinite ε ω' := isLocallyFinite_of_edgeMult hmult h
  have hs : ∀ e, (graph ε ω' h').src (edgeEquivOfEdgeMult hmult e) = (graph ε ω h).src e :=
    fun _ => rfl
  have ht : ∀ e, (graph ε ω' h').tgt (edgeEquivOfEdgeMult hmult e) = (graph ε ω h).tgt e :=
    fun _ => rfl
  have hadj := LFMultigraph.adj_eq_of_edgeEquiv (graph ε ω h) (graph ε ω' h') _ hs ht
  refine ⟨h', H.ofAdjEq hadj, hcell, ?_⟩
  exact (LFMultigraph.lemma311Holds_iff_of_edgeEquiv (graph ε ω h) (graph ε ω' h') _ hs ht H
    (H.ofAdjEq hadj) rfl).2 h311

/-- **[18] Lemma 3.11's environment event depends on the boundary-length path only through the
edge multiplicities.** For two boundary-length paths `ω, ω'` whose `ε`-mated-CRT maps have the same
edge multiplicities and one curve `c`: the map of `ω` is locally finite, the cells `c([ε(x−1), εx])`
form a cellular embedding of it and (3.35) holds on it, iff the same holds for `ω'`. -/
theorem exists_lemma311Holds_iff_of_edgeMult {ε ρ β p : ℝ} {ω ω' : Path2} (c : C(ℝ, ℂ))
    (hmult : ∀ x y : ℤ, edgeMult ε ω x y = edgeMult ε ω' x y) :
    (∃ h : IsLocallyFinite ε ω, ∃ H : CellularEmbedding (graph ε ω h) 0,
      (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
        GMSMain.T15A.Lemma311Holds H ε ρ β p) ↔
    (∃ h : IsLocallyFinite ε ω', ∃ H : CellularEmbedding (graph ε ω' h) 0,
      (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
        GMSMain.T15A.Lemma311Holds H ε ρ β p) :=
  ⟨exists_lemma311Holds_of_edgeMult c hmult,
    exists_lemma311Holds_of_edgeMult c fun x y => (hmult x y).symm⟩

/-- `exists_lemma311Holds_iff_of_edgeMult` with the edge counts given as the numbers of darts
between every two vertices of the two locally finite maps. -/
theorem exists_lemma311Holds_iff_of_card_filter_outDarts {ε ρ β p : ℝ} {ω ω' : Path2}
    (c : C(ℝ, ℂ)) (h : IsLocallyFinite ε ω) (h' : IsLocallyFinite ε ω')
    (hdarts : ∀ x y : ℤ,
      (((graph ε ω h).outDarts x).filter (fun d => (graph ε ω h).dtgt d = y)).card =
        (((graph ε ω' h').outDarts x).filter (fun d => (graph ε ω' h').dtgt d = y)).card) :
    (∃ h : IsLocallyFinite ε ω, ∃ H : CellularEmbedding (graph ε ω h) 0,
      (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
        GMSMain.T15A.Lemma311Holds H ε ρ β p) ↔
    (∃ h : IsLocallyFinite ε ω', ∃ H : CellularEmbedding (graph ε ω' h) 0,
      (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
        GMSMain.T15A.Lemma311Holds H ε ρ β p) :=
  exists_lemma311Holds_iff_of_edgeMult c (edgeMult_eq_of_card_filter_outDarts h h' hdarts)

end MatedCRT

end MatedCRTHarmonic
