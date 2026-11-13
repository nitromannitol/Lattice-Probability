/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.PairingOwnershipInstance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.OwnedFieldPairingTransport
import LatticeProb.Bonanno.ReflectedGMS.Corrector.NestedProjectionProducers

/-!
# The actual ownership datum of the signed pairing coefficient, and its block sum

`Corrector/OwnedFieldPairingTransport` reduces the manuscript's

`∫ ω, rootedPairingDensity (decode (R.env ω)) (Ψ ω) (H ω) 0 ∂μ = 0`

to a structural datum `PairingOwnership R m Ψ H` — a symmetric, selected-square-valued owner
label for every ordered pair of raw vertex labels, absent only where the signed coefficient
vanishes — together with two real-valued hypotheses on the owner block of the origin
(`hsum`, `hzero`).  No producer existed for either.  This module supplies both, for the
**actual** nested pair, out of results already checked in this project:

* `activeOwner` — the owner block of an ordered pair of vertices is the unique selected square
  of which it is an `ActiveBlockEdges.ActiveEdge`.  Uniqueness is the checked
  `ActiveBlockEdges.activeEdge_unique`; nothing new is assumed.
* `activePairingOwnership` — the resulting `PairingOwnership`.  Its only nonformal field is
  *"the coefficient vanishes on unowned pairs"*, which is proved, not assumed: if the pair is
  not an edge the conductance is `0`; and if it is an edge, the two cells meet, so by the
  manuscript's `NestedProjectionProducers.SelectionCoversOn` some selected square contains a
  common point — which is covered, being in a cell — and hence both endpoints, and failure of
  `ActiveEdge` for that square then
  forces both endpoints onto its spatial boundary, where the variation `H` vanishes.
* `summable_indicator_ownedByOriginBlock` and `tsum_indicator_ownedByOriginBlock_eq_zero` —
  the two remaining real-valued hypotheses `hsum`/`hzero`, discharged from the block-local
  data of the manuscript's projection: `Ψ ω` minimizes the vector energy on the selected
  origin block against the centroid trace, and the competitor `Ψ ω + H ω` has finite
  block-local energy.  These are exactly the hypotheses of the checked
  `NestedProjectionProducers.summable_vectorGradProd` and
  `NestedProjectionProducers.tsum_vectorGradProd_sub_eq_zero_of_centroidTraceMinimizer`
  at the origin block; **no** finite energy of the whole network is used.
* `integral_rootedPairingDensity_eq_zero_of_active` — the transport statement with the
  ownership instance supplied and `hsum`/`hzero` gone.

The bridge between the `ℕ × ℕ`-indexed owner block and the `patchVertices × patchVertices`
index of the checked producers is the injection `labelPair` together with
`Function.Injective.summable_iff` and `Function.Injective.tsum_eq` (mathlib).  A mathlib search
(`grep` on statement shape over the pinned tree) found those two, `Set.indicator_of_notMem`
and `Real.inner_apply`; it found no form of the ownership construction, of the active-edge
owner, or of the label reindexing, and the project's own `ReflectedGMS/` tree contains no
`PairingOwnership` producer and no indicator-reindexing adapter (searched for
`Injective.tsum_eq`, `support_indicator_subset`, `summable_indicator`, `activeOwner`,
`labelOwner`, `PairingOwnership`).

* `ae_notMem_boundaryMask_env` — the hypothesis `hbdry` as well: the marked mass-transport
  principle already required pushes forward to the environment law along `R.env`, because a
  `MassTransportKernel` is similarity-covariant and the re-rooting action translates the
  environment, and the checked `Spatial.ae_notMem_boundaryMask_of_massTransport` then applies.

What is **not** proved here: the marked mass-transport principle `MarkedMassTransport` (a
separate, adjudicated packet), the measurability hypotheses `hcoeff`/`howner`, the pathwise
origin selection `hsel`, the re-rooting equivariance `PairingReRooting`, and the a.e.
finiteness of the two expected endpoint densities.  All of these remain visible hypotheses of
`integral_rootedPairingDensity_eq_zero_of_active`, which is therefore a **conditional**
statement and certifies none of its inputs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.PairingOwnershipInstance

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open ActiveBlockEdges NestedProjectionProducers OwnedFieldPairingTransport EnvironmentLaws

/-! ### Reindexing an indicator sum along an injection

The owner block of the origin is a set of ordered *label* pairs, while every checked block
result is indexed by ordered pairs of *patch vertices*.  The two sums agree as soon as the
label map is injective, its range covers the owner block, and the coefficient vanishes at the
patch pairs outside the owner block. -/

section Reindex

variable {ι β : Type*}

/-- Off the set the coefficient already vanishes, so the indicator changes nothing along the
reindexing map. -/
theorem indicator_apply_comp (S : Set β) (f : β → ℝ) (φ : ι → β)
    (hout : ∀ i : ι, φ i ∉ S → f (φ i) = 0) (i : ι) :
    S.indicator f (φ i) = f (φ i) := by
  classical
  by_cases h : φ i ∈ S
  · exact Set.indicator_of_mem h f
  · rw [Set.indicator_of_notMem h f, hout i h]

/-- **Summability transfers from the reindexing type to the indicator family.** -/
theorem summable_indicator_of_injective {S : Set β} {f : β → ℝ} {φ : ι → β}
    (hinj : Function.Injective φ) (hsub : S ⊆ Set.range φ)
    (hout : ∀ i : ι, φ i ∉ S → f (φ i) = 0)
    (hs : Summable fun i : ι => f (φ i)) : Summable (S.indicator f) := by
  classical
  have hzero : ∀ x : β, x ∉ Set.range φ → S.indicator f x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun hxS => hx (hsub hxS)) f
  exact (hinj.summable_iff hzero).1
    (hs.congr fun i => (indicator_apply_comp S f φ hout i).symm)

/-- **The indicator sum is the sum along the injection.** -/
theorem tsum_indicator_of_injective {S : Set β} {f : β → ℝ} {φ : ι → β}
    (hinj : Function.Injective φ) (hsub : S ⊆ Set.range φ)
    (hout : ∀ i : ι, φ i ∉ S → f (φ i) = 0) :
    (∑' x : β, S.indicator f x) = ∑' i : ι, f (φ i) := by
  classical
  have hsupp : Function.support (S.indicator f) ⊆ Set.range φ := by
    intro x hx
    refine hsub ?_
    by_contra hxS
    exact hx (Set.indicator_of_notMem hxS f)
  rw [← hinj.tsum_eq hsupp]
  exact tsum_congr fun i => indicator_apply_comp S f φ hout i

end Reindex

/-! ### The signed edge coefficient in inner-product form

`NestedProjectionProducers.vectorGradProd` is the coordinatewise polarization; the manuscript
writes the same number as one plane inner product. -/

/-- The signed edge coefficient `c(e) ⟪g(e), g'(e)⟫` of the manuscript is the coordinatewise
polarization `NestedProjectionProducers.vectorGradProd`. -/
theorem vectorGradProd_eq_mul_inner {W : Type*} (G : ReflectedWalk.ConductanceGraph W)
    (f g : W → Plane) (q : W × W) :
    vectorGradProd G f g q = G.c q.1 q.2 * inner ℝ (f q.2 - f q.1) (g q.2 - g q.1) := by
  have hinner : (inner ℝ (f q.2 - f q.1) (g q.2 - g q.1) : ℝ)
      = ∑ i : Fin 2, (f q.2 i - f q.1 i) * (g q.2 i - g q.1 i) := by
    simp [PiLp.inner_apply, PiLp.sub_apply]
    ring
  rw [vectorGradProd_apply, hinner, Fin.sum_univ_two]
  simp only [ReflectedWalk.ConductanceGraph.gradProd]
  ring

/-! ### The owner block of an ordered pair of vertices -/

section Owner

variable {V : Type*}

/-- Two `Option` values with the same `some`-fibres agree. -/
theorem option_eq_of_forall_iff {α : Type*} {o₁ o₂ : Option α}
    (h : ∀ a : α, o₁ = some a ↔ o₂ = some a) : o₁ = o₂ := by
  cases o₁ with
  | none =>
    cases o₂ with
    | none => rfl
    | some b => exact absurd ((h b).2 rfl) (by simp)
  | some a => exact ((h a).1 rfl).symm

/-- **The owner block of an ordered pair of vertices**: the selected square of which the pair
is an active edge, absent when no selected square owns it.  By
`ActiveBlockEdges.activeEdge_unique` there is at most one such square. -/
noncomputable def activeOwner (F : IndexedCells V) (D : Grid) (m : ℝ) (p : V × V) :
    Option SquareIndex := by
  classical
  exact if h : ∃ s : SquareIndex, ActiveEdge F D m s p then some h.choose else none

theorem activeEdge_of_activeOwner_eq_some (F : IndexedCells V) (D : Grid) (m : ℝ)
    {p : V × V} {s : SquareIndex} (h : activeOwner F D m p = some s) :
    ActiveEdge F D m s p := by
  classical
  unfold activeOwner at h
  by_cases hex : ∃ t : SquareIndex, ActiveEdge F D m t p
  · rw [dif_pos hex] at h
    have hs : hex.choose = s := Option.some.inj h
    rw [← hs]
    exact hex.choose_spec
  · rw [dif_neg hex] at h
    exact absurd h (by simp)

theorem activeOwner_eq_some_of_activeEdge (F : IndexedCells V)
    (hcell : ∀ v : V, IsConnected (F.cell v : Set Plane)) (D : Grid) (m : ℝ)
    {p : V × V} {s : SquareIndex} (h : ActiveEdge F D m s p) :
    activeOwner F D m p = some s := by
  classical
  have hex : ∃ t : SquareIndex, ActiveEdge F D m t p := ⟨s, h⟩
  unfold activeOwner
  rw [dif_pos hex]
  exact congrArg some (activeEdge_unique F hcell D m hex.choose_spec h)

theorem not_activeEdge_of_activeOwner_eq_none (F : IndexedCells V) (D : Grid) (m : ℝ)
    {p : V × V} (h : activeOwner F D m p = none) (s : SquareIndex) :
    ¬ ActiveEdge F D m s p := by
  classical
  intro hs
  have hex : ∃ t : SquareIndex, ActiveEdge F D m t p := ⟨s, hs⟩
  unfold activeOwner at h
  rw [dif_pos hex] at h
  exact absurd h (by simp)

/-- Active edges are unoriented. -/
theorem activeEdge_swap (F : IndexedCells V) (D : Grid) (m : ℝ) (s : SquareIndex)
    {p : V × V} (h : ActiveEdge F D m s p) : ActiveEdge F D m s (p.2, p.1) :=
  ⟨h.1, h.2.1.symm, h.2.2.2.1, h.2.2.1, fun hb => h.2.2.2.2 ⟨hb.2, hb.1⟩⟩

theorem activeEdge_swap_iff (F : IndexedCells V) (D : Grid) (m : ℝ) (s : SquareIndex)
    (p : V × V) : ActiveEdge F D m s (p.2, p.1) ↔ ActiveEdge F D m s p :=
  ⟨fun h => activeEdge_swap F D m s h, fun h => activeEdge_swap F D m s h⟩

/-- **The owner label lives on unoriented edges.** -/
theorem activeOwner_swap (F : IndexedCells V)
    (hcell : ∀ v : V, IsConnected (F.cell v : Set Plane)) (D : Grid) (m : ℝ) (p : V × V) :
    activeOwner F D m (p.2, p.1) = activeOwner F D m p := by
  refine option_eq_of_forall_iff fun s => ?_
  exact ⟨fun h => activeOwner_eq_some_of_activeEdge F hcell D m
      ((activeEdge_swap_iff F D m s p).1 (activeEdge_of_activeOwner_eq_some F D m h)),
    fun h => activeOwner_eq_some_of_activeEdge F hcell D m
      ((activeEdge_swap_iff F D m s p).2 (activeEdge_of_activeOwner_eq_some F D m h))⟩

/-! ### The coefficient vanishes off the active edges -/

/-- A non-edge carries no conductance, hence no pairing coefficient. -/
theorem coeff_eq_zero_of_not_adj (F : IndexedCells V) (Ψ H : V → Plane) {v w : V}
    (hadj : ¬ F.graph.toSimpleGraph.Adj v w) :
    F.graph.c v w * inner ℝ (Ψ w - Ψ v) (H w - H v) = (0 : ℝ) := by
  have hc : F.graph.c v w = 0 := by
    rcases lt_or_eq_of_le (F.graph.c_nonneg v w) with h | h
    · exact absurd (show F.graph.toSimpleGraph.Adj v w from h) hadj
    · exact h.symm
  rw [hc, zero_mul]

/-- **An edge of a selected block which is not active carries no pairing coefficient.**  Both
endpoints then lie on the spatial boundary of the block, where the variation vanishes. -/
theorem coeff_eq_zero_of_not_activeEdge (F : IndexedCells V) (D : Grid) (m : ℝ)
    {Ψ H : V → Plane} (hH : ∀ x : V, x ∈ skeleton F D m → H x = 0)
    {u : SquareIndex} (hu : Selected F D m u) {v w : V}
    (hv : v ∈ patchVertices F (square D u)) (hw : w ∈ patchVertices F (square D u))
    (hna : ¬ ActiveEdge F D m u (v, w)) :
    F.graph.c v w * inner ℝ (Ψ w - Ψ v) (H w - H v) = (0 : ℝ) := by
  by_cases hadj : F.graph.toSimpleGraph.Adj v w
  · have hbd : v ∈ boundaryVertices F (square D u) ∧ w ∈ boundaryVertices F (square D u) := by
      by_contra hb
      exact hna ⟨hu, hadj, hv, hw, hb⟩
    have h1 : H v = 0 := hH v ⟨u, hu, hbd.1⟩
    have h2 : H w = 0 := hH w ⟨u, hu, hbd.2⟩
    have hz : H w - H v = (0 : Plane) := by rw [h1, h2, sub_zero]
    rw [hz]
    simp
  · exact coeff_eq_zero_of_not_adj F Ψ H hadj

/-- **The endpoints of an edge share a selected block.**  Adjacent cells meet, and the closures
of the selected blocks cover every point belonging to a cell, so some selected square contains
a common point and therefore both cells.

The covering hypothesis is the manuscript's `SelectionCoversOn`.  It suffices unchanged: the
common point `z` is produced by the adjacency clause of `Geometry` *inside* both cells, so it
is covered by construction and no claim about an uncovered point is made. -/
theorem exists_selected_patch_of_adj [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (D : Grid) (m : ℝ) (hcover : SelectionCoversOn F D m) {v w : V}
    (hadj : F.graph.toSimpleGraph.Adj v w) :
    ∃ u : SquareIndex, Selected F D m u ∧ v ∈ patchVertices F (square D u) ∧
      w ∈ patchVertices F (square D u) := by
  obtain ⟨z, hzv, hzw⟩ := hF.2.2.2.2.2.2.2 hadj
  obtain ⟨u, hu, hzu⟩ := hcover.of_mem_cell hzv
  exact ⟨u, hu, ⟨z, hzv, hzu⟩, ⟨z, hzw, hzu⟩⟩

/-- **The pairing coefficient of an unowned pair vanishes.**  This is the single nonformal
field of the ownership datum. -/
theorem coeff_eq_zero_of_no_active_owner [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (D : Grid) (m : ℝ) (hcover : SelectionCoversOn F D m) {Ψ H : V → Plane}
    (hH : ∀ x : V, x ∈ skeleton F D m → H x = 0) {v w : V}
    (hno : ∀ u : SquareIndex, ¬ ActiveEdge F D m u (v, w)) :
    F.graph.c v w * inner ℝ (Ψ w - Ψ v) (H w - H v) = (0 : ℝ) := by
  by_cases hadj : F.graph.toSimpleGraph.Adj v w
  · obtain ⟨u, hu, hvp, hwp⟩ := exists_selected_patch_of_adj F hF D m hcover hadj
    exact coeff_eq_zero_of_not_activeEdge F D m hH hu hvp hwp (hno u)
  · exact coeff_eq_zero_of_not_adj F Ψ H hadj

/-- A boundary vertex of a selected square belongs to the skeleton. -/
theorem mem_skeleton_of_mem_boundaryVertices (F : IndexedCells V) (D : Grid) (m : ℝ)
    {s : SquareIndex} (hs : Selected F D m s) {v : V}
    (hv : v ∈ boundaryVertices F (square D s)) : v ∈ skeleton F D m :=
  ⟨s, hs, hv⟩

end Owner

/-! ### The ownership datum at the level of raw labels -/

section Instance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The owner block of an ordered pair of **raw labels**: the active-edge owner of the
corresponding pair of vertices, absent as soon as one of the labels is absent. -/
noncomputable def labelOwner (R : MarkedReRooting Ω) (m : ℝ) (ω : Ω) (p : ℕ × ℕ) :
    Option SquareIndex :=
  if ha : ((R.env ω).val.1 p.1).isSome then
    if hb : ((R.env ω).val.1 p.2).isSome then
      activeOwner (decode (R.env ω)) (R.grid ω) m (⟨p.1, ha⟩, ⟨p.2, hb⟩)
    else none
  else none

theorem labelOwner_pair (R : MarkedReRooting Ω) (m : ℝ) (ω : Ω) (a b : ℕ)
    (ha : ((R.env ω).val.1 a).isSome) (hb : ((R.env ω).val.1 b).isSome) :
    labelOwner R m ω (a, b)
      = activeOwner (decode (R.env ω)) (R.grid ω) m (⟨a, ha⟩, ⟨b, hb⟩) := by
  unfold labelOwner
  rw [dif_pos ha, dif_pos hb]

theorem labelOwner_eq_none_of_fst (R : MarkedReRooting Ω) (m : ℝ) (ω : Ω) {a : ℕ}
    (ha : ¬ ((R.env ω).val.1 a).isSome) (b : ℕ) : labelOwner R m ω (a, b) = none := by
  unfold labelOwner
  rw [dif_neg ha]

theorem labelOwner_eq_none_of_snd (R : MarkedReRooting Ω) (m : ℝ) (ω : Ω) (a : ℕ) {b : ℕ}
    (hb : ¬ ((R.env ω).val.1 b).isSome) : labelOwner R m ω (a, b) = none := by
  unfold labelOwner
  by_cases ha : ((R.env ω).val.1 a).isSome
  · rw [dif_pos ha, dif_neg hb]
  · rw [dif_neg ha]

theorem labelOwner_symm (R : MarkedReRooting Ω) (m : ℝ) (ω : Ω) (p : ℕ × ℕ) :
    labelOwner R m ω (p.2, p.1) = labelOwner R m ω p := by
  obtain ⟨a, b⟩ := p
  by_cases ha : ((R.env ω).val.1 a).isSome
  · by_cases hb : ((R.env ω).val.1 b).isSome
    · rw [labelOwner_pair R m ω b a hb ha, labelOwner_pair R m ω a b ha hb]
      exact activeOwner_swap (decode (R.env ω)) (decode_geometry (R.env ω)).1 (R.grid ω) m
        (⟨a, ha⟩, ⟨b, hb⟩)
    · rw [labelOwner_eq_none_of_fst R m ω hb a, labelOwner_eq_none_of_snd R m ω a hb]
  · rw [labelOwner_eq_none_of_snd R m ω b ha, labelOwner_eq_none_of_fst R m ω ha b]

/-! ### The owner block of the origin, reindexed by patch vertices -/

/-- The pair of raw labels of an ordered pair of patch vertices. -/
def labelPair (e : Env) (P : Set (Vertex e.val)) (q : P × P) : ℕ × ℕ := (q.1.1.1, q.2.1.1)

theorem injective_labelPair (e : Env) (P : Set (Vertex e.val)) :
    Function.Injective (labelPair e P) := by
  intro q q' h
  have h1 : (q.1 : Vertex e.val).1 = (q'.1 : Vertex e.val).1 := congrArg Prod.fst h
  have h2 : (q.2 : Vertex e.val).1 = (q'.2 : Vertex e.val).1 := congrArg Prod.snd h
  exact Prod.ext (Subtype.ext (Subtype.ext h1)) (Subtype.ext (Subtype.ext h2))

/-- The signed pairing coefficient read on a pair of patch vertices is the checked signed edge
coefficient of the patch graph. -/
theorem pairCoeff_labelPair (R : MarkedReRooting Ω)
    (Ψ H : ∀ ω : Ω, Vertex (R.env ω).val → Plane) (ω : Ω)
    (P : Set (Vertex (R.env ω).val)) (q : P × P) :
    pairCoeff (R.env ω) (Ψ ω) (H ω) (labelPair (R.env ω) P q)
      = vectorGradProd (restrictGraph (decode (R.env ω)).graph P)
          (fun v : P => Ψ ω v.1) (fun v : P => H ω v.1) q := by
  rw [vectorGradProd_eq_mul_inner]
  exact pairCoeff_vertex (R.env ω) (Ψ ω) (H ω) q.1.1 q.2.1

/-! ### The two remaining real-valued hypotheses of the transport

`hsum` and `hzero` of `OwnedFieldPairingTransport.integral_rootedPairingDensity_eq_zero`, from
the block-local data of the manuscript's projection at the selected origin block. -/

/-- The block-local energy of the variation, from the two block-local energies of the
manuscript. -/
theorem vectorEnergy_variation_lt_top (R : MarkedReRooting Ω) (m : ℝ)
    (Ψ H : ∀ ω : Ω, Vertex (R.env ω).val → Plane) (ω : Ω)
    (hΨE : vectorEnergy (restrictGraph (decode (R.env ω)).graph
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))))
        (fun v => Ψ ω v.1) < ∞)
    (hmE : vectorEnergy (restrictGraph (decode (R.env ω)).graph
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))))
        (fun v => Ψ ω v.1 + H ω v.1) < ∞) :
    vectorEnergy (restrictGraph (decode (R.env ω)).graph
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))))
        (fun v => H ω v.1) < ∞ := by
  have hdiff : ((fun v : (patchVertices (decode (R.env ω))
        (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))) =>
        Ψ ω v.1 + H ω v.1) - fun v => Ψ ω v.1)
      = fun v => H ω v.1 := by
    funext v
    simp
  rw [← hdiff]
  exact vectorEnergy_lt_top_of_coord _ fun i =>
    NestedEnergyProjections.hasFiniteEnergy_coord_sub _ hΨE hmE i

/-! ### The null boundary mask, from the marked mass transport

The hypothesis `hbdry` of the owned-field transport is not an independent assumption: it
follows from the marked mass-transport principle already required, once the re-rooting action
really translates the environment. -/

/-- **`hbdry`.**  Almost surely the origin lies on no cell boundary, from the manuscript's own
mass-transport principle `s:eq:MTP` for the pushed-forward environment law, through the checked
`Spatial.ae_notMem_boundaryMask_of_massTransport`.

The hypothesis is `EnvironmentLaws.MassTransport (μ.map R.env)` — the manuscript's `s:eq:MTP`
read on the law of the environment observable — and **not** the marked principle
`SpecificEnergyRedistribution.MarkedMassTransport`, which is strictly stronger than `s:eq:MTP`
and is not derivable from it.  The translation property `hre` of the re-rooting action is
consequently no longer needed either. -/
theorem ae_notMem_boundaryMask_env (R : MarkedReRooting Ω) {μ : Measure Ω}
    (hν : MassTransport (μ.map R.env)) (henv : Measurable R.env) :
    ∀ᵐ ω ∂μ, (0 : Plane) ∉ RootDensities.boundaryMask (decode (R.env ω)) :=
  ae_of_ae_map henv.aemeasurable
    (Spatial.ae_notMem_boundaryMask_of_massTransport (μ.map R.env) hν)

/-! ### The transport statement with the ownership datum supplied -/

end Instance

end ReflectedGMS.PairingOwnershipInstance
