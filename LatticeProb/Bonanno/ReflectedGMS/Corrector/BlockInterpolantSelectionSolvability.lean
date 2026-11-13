/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.BlockInterpolantSelectionSolvability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PatchLabelMeasurability
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MeasurableInfinitePatchMinimizer
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedLevelEnergySolvability

/-!
# The per-square solvability event is measurable

`Corrector/PatchSolvableEventMeasurability.lean` reduces the measurability input `hmeas` of
the harmonic-coordinate assembly, at every stage, to **one** measurability statement:

  `∀ s : SquareIndex, MeasurableSet (SquareSolvableEvent s)`,

where `SquareSolvable F D s` says that *some* plane-valued field on the patch of the dyadic
square `square D s` has finite vector energy and carries the centroid trace on that patch's
spatial boundary.  This module proves that statement.

## The obstruction and the route

The event is an existential over fields on `patchVertices (decode ω.1) (square ω.2 s)`, a
type that depends on the sample point, so no measurable-selection theorem applies to it
directly — and the pinned mathlib carries no measurable-selection theorem at all.  Three
checked ingredients remove the obstruction, and none of them is new here:

* `Corrector/VaryingVertexIndexing.lean` shows the varying vertex type is a **full subgraph**
  of one fixed `ℕ`-indexed graph, with energy transferring in both directions and with no
  finiteness hypothesis.  `maskGraph` turns the patch restriction — whose vertex type still
  varies — into a graph on the fixed type `ℕ` by zeroing every conductance touching the
  complement of the patch labels, and `isFullEmbedding_patchGraph` is the resulting full
  embedding.  Vertices outside the patch become isolated, which is why the anchor set on the
  fixed type must be `boundaryLabels ∪ patchLabelsᶜ`.
* `Corrector/PatchLabelMeasurability.lean` makes the patch and the spatial-boundary labels
  measurable events, so the masked graph, the anchor set and the centroid boundary data are
  all measurable in the marked environment.
* `Forms/BoundedLevelEnergySolvability.exists_finiteEnergy_trace_iff_exists_nat` converts the
  existential into a **countable** condition: a finite-energy field with the prescribed trace
  exists exactly when the energies of the anchored minimizers of a monotone exhausting family
  of finite levels are bounded by some natural number.  No finite energy of the reference
  field is assumed there, which is exactly what makes it usable: the centroid trace's own
  patch energy is infinite in general, and whether some finite-energy field carries it is the
  question being asked.

The exhausting levels are `Corrector/MeasurableInfinitePatchMinimizer.patchLevel`, whose
fibres are measurable, and the level minimizers are those of
`Corrector/MeasurableBlockMinimizer.exists_measurable_varying_block_minimizer_anchorSet`,
which are measurable in the environment.  `measurable_levelEnergy` then makes each level
energy a measurable real function — the level being a measurably varying `Finset ℕ`, the
energy is read off the countable partition of the space by its value — and

  `SquareSolvableEvent s = ⋂ i : Fin 2, ⋃ k : ℕ, ⋂ n : ℕ, {ω | levelEnergy … ≤ k}`

is measurable.  The coordinate intersection is the usual decoupling of the plane-valued
problem into its two scalar ones.

## What this closes and what remains

`measurableSet_squareSolvableEvent` discharges the hypothesis `hsq` of
`PatchSolvableEventMeasurability.measurable_gatedApproximant_of_squareSolvability`, so
`measurable_gatedApproximant_of_candidate` produces literally the `hmeas` hypothesis of the
harmonic-coordinate assembly from **one** remaining input: a measurable candidate family `Ψ`
which, on the good event and at a positive stage, is a block interpolant whenever one exists.
That single proposition is named `HasMeasurableBlockInterpolantCandidate` and is the whole
residual of `hmeas`; `hmeas_of_measurableBlockInterpolantCandidate` states the implication.

**This file proves no main theorem and does not certify `hmeas`.**  It removes the
existential-over-a-varying-vertex-type half of that input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal Classical

namespace ReflectedGMS.BlockInterpolantSelectionSolvability

open Code StatementIngredients DyadicApproximation HarmonicMainStatement
open EnvironmentLaws HarmonicLawIngredients
open HarmonicCoordinateAssembly GatedApproximantMeasurability
open BlockInterpolantSelectionGate BlockInterpolantGateReduction
open PatchSolvableEventMeasurability PatchLabelMeasurability
open VaryingVertexIndexing MeasurableInfinitePatchMinimizer
open AnchoredFiniteExhaustion FiniteDirichletEnergyLimit

/-- Coordinate evaluation on the plane is measurable. -/
theorem measurable_planeCoord (i : Fin 2) : Measurable fun y : Plane => y i := by
  first
    | exact (PiLp.continuous_apply _ _ i).measurable
    | fun_prop
    | measurability

/-! ### Masking a conductance graph outside a vertex set -/

/-- **The restriction of a conductance graph to a vertex set, carried on the original index
type.**  Every conductance touching the complement of `T` is set to zero, so the vertices
outside `T` become isolated and the index type does not change. -/
noncomputable def maskGraph {V : Type*} (G : ReflectedWalk.ConductanceGraph V) (T : Set V) :
    ReflectedWalk.ConductanceGraph V where
  c x y := if x ∈ T ∧ y ∈ T then G.c x y else 0
  c_symm x y := by
    by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp [hx, hy, G.c_symm x y]
  c_nonneg x y := by
    by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp [hx, hy, G.c_nonneg x y]
  c_self x := by
    by_cases hx : x ∈ T <;> simp [hx, G.c_self x]
  summable_c x := by
    refine Summable.of_nonneg_of_le (fun y => ?_) (fun y => ?_) (G.summable_c x)
    · by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp [hx, hy, G.c_nonneg x y]
    · by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp [hx, hy, G.c_nonneg x y]

theorem maskGraph_c_of_mem {V : Type*} (G : ReflectedWalk.ConductanceGraph V) {T : Set V}
    {x y : V} (hx : x ∈ T) (hy : y ∈ T) : (maskGraph G T).c x y = G.c x y :=
  if_pos ⟨hx, hy⟩

theorem maskGraph_c_of_notMem {V : Type*} (G : ReflectedWalk.ConductanceGraph V) {T : Set V}
    {x : V} (hx : x ∉ T) (y : V) : (maskGraph G T).c x y = 0 :=
  if_neg fun h => hx h.1

/-! ### Reachability transfers along a full embedding -/

/-- **A full embedding of conductance graphs preserves reachability.**  Only the conductance
clause is used: the image of an edge is an edge. -/
theorem reachable_map_of_isFullEmbedding {V W : Type*}
    {G : ReflectedWalk.ConductanceGraph V} {H : ReflectedWalk.ConductanceGraph W} {i : V → W}
    (hi : IsFullEmbedding G H i) {x y : V} (h : G.toSimpleGraph.Reachable x y) :
    H.toSimpleGraph.Reachable (i x) (i y) := by
  have hadj : ∀ a b : V, G.toSimpleGraph.Adj a b → H.toSimpleGraph.Adj (i a) (i b) := by
    intro a b hab
    have hc : H.c (i a) (i b) = G.c a b := hi.conductance a b
    show 0 < H.c (i a) (i b)
    rw [hc]
    exact hab
  exact SimpleGraph.Reachable.map
    (⟨i, fun hab => hadj _ _ hab⟩ :
      SimpleGraph.Hom G.toSimpleGraph H.toSimpleGraph) h

/-! ### The patch labels of a dyadic square -/

/-- The code labels belonging to the patch of the square `s`. -/
def patchLabels (s : SquareIndex) (ω : MarkedEnvironment) : Set ℕ :=
  {n : ℕ | ω ∈ patchLabelEvent s n}

/-- The code labels whose cell meets the spatial boundary of the square `s`. -/
def boundaryLabels (s : SquareIndex) (ω : MarkedEnvironment) : Set ℕ :=
  {n : ℕ | ω ∈ boundaryLabelEvent s n}

/-- **The anchor set on the fixed index type.**  Outside the patch every label is isolated in
the masked graph, so it has to be pinned; inside the patch the pinning is the spatial
boundary.  Nothing outside the patch influences any energy. -/
def anchorLabels (s : SquareIndex) (ω : MarkedEnvironment) : Set ℕ :=
  boundaryLabels s ω ∪ (patchLabels s ω)ᶜ

theorem isSome_of_mem_patchLabels {s : SquareIndex} {n : ℕ} {ω : MarkedEnvironment}
    (h : n ∈ patchLabels s ω) : (ω.1.val.1 n).isSome := h.1

theorem mem_patchLabels_iff (s : SquareIndex) (ω : MarkedEnvironment) (v : Vertex ω.1.val) :
    v ∈ patchVertices (decode ω.1) (square ω.2 s) ↔ v.val ∈ patchLabels s ω :=
  (mem_patchLabelEvent_iff (s := s) (n := v.val) (ω := ω) v.property).symm

theorem mem_boundaryLabels_iff (s : SquareIndex) (ω : MarkedEnvironment)
    (v : Vertex ω.1.val) :
    v ∈ boundaryVertices (decode ω.1) (square ω.2 s) ↔ v.val ∈ boundaryLabels s ω :=
  (mem_boundaryLabelEvent_iff (s := s) (n := v.val) (ω := ω) v.property).symm

theorem measurableSet_mem_patchLabels (s : SquareIndex) (n : ℕ) :
    MeasurableSet {ω : MarkedEnvironment | n ∈ patchLabels s ω} :=
  measurableSet_patchLabelEvent s n

theorem measurableSet_mem_anchorLabels (s : SquareIndex) (n : ℕ) :
    MeasurableSet {ω : MarkedEnvironment | n ∈ anchorLabels s ω} := by
  have hEq : {ω : MarkedEnvironment | n ∈ anchorLabels s ω}
      = boundaryLabelEvent s n ∪ (patchLabelEvent s n)ᶜ := rfl
  rw [hEq]
  exact (measurableSet_boundaryLabelEvent s n).union
    (measurableSet_patchLabelEvent s n).compl

/-! ### The masked patch graph on the fixed index type -/

/-- **The patch graph of one dyadic square, on the fixed index type `ℕ`.** -/
noncomputable def patchGraph (s : SquareIndex) (ω : MarkedEnvironment) :
    ReflectedWalk.ConductanceGraph ℕ :=
  maskGraph (envNatGraph ω.1) (patchLabels s ω)

/-- **The full embedding of the patch restriction into the masked graph.**  The vanishing
clause is where the patch labels being *present* slots is used. -/
theorem isFullEmbedding_maskGraph (e : Env) {S : Set (Vertex e.val)} {T : Set ℕ}
    (hST : ∀ v : Vertex e.val, v ∈ S ↔ v.val ∈ T)
    (hT : ∀ n ∈ T, (e.val.1 n).isSome) :
    IsFullEmbedding (restrictGraph (decode e).graph S) (maskGraph (envNatGraph e) T)
      (fun v : S => (v.1.val : ℕ)) where
  injective := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    exact Subtype.ext (Subtype.ext hab)
  conductance := fun v w => by
    rw [maskGraph_c_of_mem _ ((hST v.1).1 v.2) ((hST w.1).1 w.2)]
    exact (isFullEmbedding_envNatGraph e).conductance v.1 w.1
  vanishing := by
    intro a b hmem
    refine maskGraph_c_of_notMem _ (fun haT => hmem ?_) b
    exact ⟨⟨⟨a, hT a haT⟩, (hST ⟨a, hT a haT⟩).2 haT⟩, rfl⟩

theorem isFullEmbedding_patchGraph (s : SquareIndex) (ω : MarkedEnvironment) :
    IsFullEmbedding
      (restrictGraph (decode ω.1).graph (patchVertices (decode ω.1) (square ω.2 s)))
      (patchGraph s ω)
      (fun v : patchVertices (decode ω.1) (square ω.2 s) => (v.1.val : ℕ)) :=
  isFullEmbedding_maskGraph ω.1 (mem_patchLabels_iff s ω)
    (fun _ hn => isSome_of_mem_patchLabels hn)

theorem measurable_patchGraph_c (s : SquareIndex) (x y : ℕ) :
    Measurable fun ω : MarkedEnvironment => (patchGraph s ω).c x y := by
  have hEq : (fun ω : MarkedEnvironment => (patchGraph s ω).c x y)
      = fun ω : MarkedEnvironment =>
          if x ∈ patchLabels s ω ∧ y ∈ patchLabels s ω then (envNatGraph ω.1).c x y else 0 :=
    rfl
  rw [hEq]
  have hset : MeasurableSet
      {ω : MarkedEnvironment | x ∈ patchLabels s ω ∧ y ∈ patchLabels s ω} :=
    (measurableSet_mem_patchLabels s x).inter (measurableSet_mem_patchLabels s y)
  exact Measurable.ite hset (measurable_markedNatGraph_c x y) measurable_const

/-! ### The patch graph is anchored at every marked environment -/

/-- **Every label reaches the anchor set in the masked patch graph.**  Outside the patch a
label is isolated and lies in the anchor set; inside it, the geometric anchoring
`Geometry/BoundaryAnchoring.boundaryAnchored_restrictGraph_cells_hitting` transfers along the
full embedding. -/
theorem boundaryAnchored_patchGraph (s : SquareIndex) (ω : MarkedEnvironment) :
    BoundaryAnchored (patchGraph s ω) (anchorLabels s ω) := by
  intro n
  by_cases hn : n ∈ patchLabels s ω
  · have hsome : (ω.1.val.1 n).isSome := isSome_of_mem_patchLabels hn
    have hvS : (⟨n, hsome⟩ : Vertex ω.1.val)
        ∈ patchVertices (decode ω.1) (square ω.2 s) :=
      (mem_patchLabels_iff s ω ⟨n, hsome⟩).2 hn
    have hanch : BoundaryAnchored
        (restrictGraph (decode ω.1).graph (patchVertices (decode ω.1) (square ω.2 s)))
        {a : patchVertices (decode ω.1) (square ω.2 s) |
          a.1 ∈ boundaryVertices (decode ω.1) (square ω.2 s)} :=
      boundaryAnchored_restrictGraph_cells_hitting (decode ω.1) (decode_geometry ω.1)
        (square ω.2 s).carrier (BlockInterpolantExistence.isBounded_carrier (square ω.2 s))
    obtain ⟨a, haB, hreach⟩ := hanch ⟨⟨n, hsome⟩, hvS⟩
    refine ⟨a.1.val, Or.inl ((mem_boundaryLabels_iff s ω a.1).1 haB), ?_⟩
    exact reachable_map_of_isFullEmbedding (isFullEmbedding_patchGraph s ω) hreach
  · exact ⟨n, Or.inr hn, SimpleGraph.Reachable.refl n⟩

theorem exists_isAnchorChain_patchGraph (s : SquareIndex) (ω : MarkedEnvironment) (n : ℕ) :
    ∃ l : List ℕ, IsAnchorChain (patchGraph s ω) (anchorLabels s ω) n l :=
  exists_isAnchorChain (patchGraph s ω) (boundaryAnchored_patchGraph s ω) n

/-! ### The scalar problem on the fixed index type -/

/-- The centroid boundary datum of the square, read at a code slot and in one coordinate. -/
noncomputable def centroidDatum (i : Fin 2) (ω : MarkedEnvironment) (n : ℕ) : ℝ :=
  slotCentroid ω.1 n i

theorem measurable_centroidDatum (i : Fin 2) (n : ℕ) :
    Measurable fun ω : MarkedEnvironment => centroidDatum i ω n :=
  (measurable_planeCoord i).comp ((measurable_slotCentroid n).comp measurable_fst)

/-- The scalar trace problem of one square and one coordinate, on the fixed index type. -/
def NatSolvableEvent (s : SquareIndex) (i : Fin 2) : Set MarkedEnvironment :=
  {ω : MarkedEnvironment | ∃ g : ℕ → ℝ, (patchGraph s ω).HasFiniteEnergy g ∧
    ∀ a ∈ anchorLabels s ω, g a = centroidDatum i ω a}

/-- **The plane-valued per-square problem decouples into its two scalar coordinates.**  The
vector energy is by definition the sum of the coordinate energies and the centroid trace is
prescribed coordinatewise; this is the per-square form of
`BlockInterpolantGateReduction.patchSolvable_iff_coord`. -/
theorem squareSolvable_iff_coord {V : Type*} (F : IndexedCells V) (D : Grid)
    (s : SquareIndex) :
    SquareSolvable F D s ↔ ∀ i : Fin 2,
      ∃ u : patchVertices F (square D s) → ℝ,
        (restrictGraph F.graph (patchVertices F (square D s))).HasFiniteEnergy u ∧
        ∀ v : patchVertices F (square D s), v.1 ∈ boundaryVertices F (square D s) →
          u v = cellCentroid F v.1 i := by
  constructor
  · rintro ⟨u, hfin, htr⟩ i
    exact ⟨fun v => u v i, hasFiniteEnergy_coord _ hfin i,
      fun v hv => congrArg (fun z : Plane => z i) (htr v hv)⟩
  · intro h
    choose U hUfin hUtr using h
    refine ⟨fun v => (WithLp.toLp 2 (fun i => U i v) : Plane), ?_, ?_⟩
    · refine vectorEnergy_lt_top_of_coord _ fun i => ?_
      have hcoord : (fun v : patchVertices F (square D s) =>
          ((WithLp.toLp 2 (fun j => U j v) : Plane)) i) = U i := rfl
      rw [hcoord]
      exact hUfin i
    · intro v hv
      exact PiLp.ext fun i => hUtr i v hv

/-- **The scalar patch problem is the same on the varying and on the fixed index type.**
Forward, the field is extended off the patch by the centroid datum through `Function.extend`;
backward, it is restricted.  The anchor set on the fixed type contains the complement of the
patch, where the extension is the datum by construction. -/
theorem natSolvableEvent_iff (s : SquareIndex) (ω : MarkedEnvironment) (i : Fin 2) :
    (∃ u : patchVertices (decode ω.1) (square ω.2 s) → ℝ,
        (restrictGraph (decode ω.1).graph
          (patchVertices (decode ω.1) (square ω.2 s))).HasFiniteEnergy u ∧
        ∀ v : patchVertices (decode ω.1) (square ω.2 s),
          v.1 ∈ boundaryVertices (decode ω.1) (square ω.2 s) →
            u v = cellCentroid (decode ω.1) v.1 i)
      ↔ ω ∈ NatSolvableEvent s i := by
  have hi := isFullEmbedding_patchGraph s ω
  constructor
  · rintro ⟨u, hufin, hutr⟩
    refine ⟨Function.extend
      (fun v : patchVertices (decode ω.1) (square ω.2 s) => (v.1.val : ℕ)) u
      (fun n : ℕ => centroidDatum i ω n), ?_, ?_⟩
    · have hfun : (fun v : patchVertices (decode ω.1) (square ω.2 s) =>
          Function.extend
            (fun v : patchVertices (decode ω.1) (square ω.2 s) => (v.1.val : ℕ)) u
            (fun n : ℕ => centroidDatum i ω n) (v.1.val : ℕ)) = u :=
        funext fun v => hi.injective.extend_apply u _ v
      refine (hi.hasFiniteEnergy_comp_iff _).1 ?_
      show (restrictGraph (decode ω.1).graph
          (patchVertices (decode ω.1) (square ω.2 s))).HasFiniteEnergy
        (fun v : patchVertices (decode ω.1) (square ω.2 s) =>
          Function.extend
            (fun v : patchVertices (decode ω.1) (square ω.2 s) => (v.1.val : ℕ)) u
            (fun n : ℕ => centroidDatum i ω n) (v.1.val : ℕ))
      rw [hfun]
      exact hufin
    · intro a ha
      by_cases haP : a ∈ patchLabels s ω
      · have hsome : (ω.1.val.1 a).isSome := isSome_of_mem_patchLabels haP
        have hvS : (⟨a, hsome⟩ : Vertex ω.1.val)
            ∈ patchVertices (decode ω.1) (square ω.2 s) :=
          (mem_patchLabels_iff s ω ⟨a, hsome⟩).2 haP
        have hbL : a ∈ boundaryLabels s ω := by
          rcases ha with hb | hnp
          · exact hb
          · exact absurd haP hnp
        have hbv : (⟨a, hsome⟩ : Vertex ω.1.val)
            ∈ boundaryVertices (decode ω.1) (square ω.2 s) :=
          (mem_boundaryLabels_iff s ω ⟨a, hsome⟩).2 hbL
        have hval : Function.extend
            (fun v : patchVertices (decode ω.1) (square ω.2 s) => (v.1.val : ℕ)) u
            (fun n : ℕ => centroidDatum i ω n) a
            = u ⟨⟨a, hsome⟩, hvS⟩ :=
          hi.injective.extend_apply u (fun n : ℕ => centroidDatum i ω n)
            (⟨⟨a, hsome⟩, hvS⟩ : patchVertices (decode ω.1) (square ω.2 s))
        show Function.extend
            (fun v : patchVertices (decode ω.1) (square ω.2 s) => (v.1.val : ℕ)) u
            (fun n : ℕ => centroidDatum i ω n) a = centroidDatum i ω a
        rw [hval, hutr ⟨⟨a, hsome⟩, hvS⟩ hbv]
        exact (congrArg (fun z : Plane => z i)
          (slotCentroid_eq_cellCentroid ω.1 ⟨a, hsome⟩)).symm
      · refine Function.extend_apply' u (fun n : ℕ => centroidDatum i ω n) a ?_
        rintro ⟨v, hv⟩
        exact haP (hv ▸ (mem_patchLabels_iff s ω v.1).1 v.2)
  · rintro ⟨g, hgfin, hgtr⟩
    refine ⟨fun v : patchVertices (decode ω.1) (square ω.2 s) => g (v.1.val : ℕ),
      (hi.hasFiniteEnergy_comp_iff g).2 hgfin, ?_⟩
    intro v hv
    have hmem : (v.1.val : ℕ) ∈ anchorLabels s ω :=
      Or.inl ((mem_boundaryLabels_iff s ω v.1).1 hv)
    show g (v.1.val : ℕ) = cellCentroid (decode ω.1) v.1 i
    rw [hgtr _ hmem]
    exact congrArg (fun z : Plane => z i) (slotCentroid_eq_cellCentroid ω.1 v.1)

/-- **The per-square solvability event is the intersection of its two scalar events on the
fixed index type.** -/
theorem squareSolvableEvent_eq_iInter (s : SquareIndex) :
    SquareSolvableEvent s = ⋂ i : Fin 2, NatSolvableEvent s i := by
  refine Set.ext fun ω => ?_
  rw [Set.mem_iInter]
  constructor
  · intro hω i
    exact (natSolvableEvent_iff s ω i).1
      ((squareSolvable_iff_coord (decode ω.1) ω.2 s).1 hω i)
  · intro hω
    exact (squareSolvable_iff_coord (decode ω.1) ω.2 s).2 fun i =>
      (natSolvableEvent_iff s ω i).2 (hω i)

/-! ### The measurable level minimizers of one square and one coordinate -/

/-- **Measurable anchored minimizers on the canonical finite levels of the patch graph.**
This is the `hstep` of
`Corrector/MeasurableInfinitePatchMinimizer.exists_measurable_anchored_energy_minimizer`,
instantiated at the patch graph, the anchor labels and the centroid datum.  No finiteness of
the reference energy is involved. -/
theorem exists_measurable_levelMinimizers (s : SquareIndex) (i : Fin 2) :
    ∃ F : ℕ → MarkedEnvironment → ℕ → ℝ,
      (∀ (n : ℕ) (x : ℕ), Measurable fun ω : MarkedEnvironment => F n ω x) ∧
      ∀ (n : ℕ) (ω : MarkedEnvironment),
        (∀ a ∈ anchorLabels s ω,
            a ∈ patchLevel (patchGraph s ω) (anchorLabels s ω) n →
            F n ω a = centroidDatum i ω a) ∧
        (∀ w : ℕ → ℝ,
          (∀ a ∈ anchorLabels s ω,
              a ∈ patchLevel (patchGraph s ω) (anchorLabels s ω) n →
              w a = centroidDatum i ω a) →
          restrictedEnergy (patchGraph s ω)
              ((patchLevel (patchGraph s ω) (anchorLabels s ω) n : Finset ℕ) : Set ℕ)
              (F n ω)
            ≤ restrictedEnergy (patchGraph s ω)
              ((patchLevel (patchGraph s ω) (anchorLabels s ω) n : Finset ℕ) : Set ℕ) w) := by
  have hstep : ∀ n : ℕ, ∃ f : MarkedEnvironment → ℕ → ℝ,
      (∀ x : ℕ, Measurable fun ω : MarkedEnvironment => f ω x) ∧
      ∀ ω : MarkedEnvironment,
        (∀ a ∈ anchorLabels s ω,
            a ∈ patchLevel (patchGraph s ω) (anchorLabels s ω) n →
            f ω a = centroidDatum i ω a) ∧
        (∀ w : ℕ → ℝ,
          (∀ a ∈ anchorLabels s ω,
              a ∈ patchLevel (patchGraph s ω) (anchorLabels s ω) n →
              w a = centroidDatum i ω a) →
          restrictedEnergy (patchGraph s ω)
              ((patchLevel (patchGraph s ω) (anchorLabels s ω) n : Finset ℕ) : Set ℕ) (f ω)
            ≤ restrictedEnergy (patchGraph s ω)
              ((patchLevel (patchGraph s ω) (anchorLabels s ω) n : Finset ℕ) : Set ℕ) w) := by
    intro n
    obtain ⟨f, -, hfeval, hf⟩ :=
      MeasurableBlockMinimizer.exists_measurable_varying_block_minimizer_anchorSet
        (G := fun ω : MarkedEnvironment => patchGraph s ω)
        (fun x y => measurable_patchGraph_c s x y)
        (S := fun ω : MarkedEnvironment => patchLevel (patchGraph s ω) (anchorLabels s ω) n)
        (fun t => measurableSet_patchLevel_eq (fun x y => measurable_patchGraph_c s x y)
          (fun x => measurableSet_mem_anchorLabels s x)
          (fun ω x => exists_isAnchorChain_patchGraph s ω x) n t)
        (A := fun ω : MarkedEnvironment => anchorLabels s ω)
        (fun x => measurableSet_mem_anchorLabels s x)
        (fun ω => boundaryAnchored_patchLevel (patchGraph s ω)
          (fun x => exists_isAnchorChain_patchGraph s ω x) n)
        (u := fun ω : MarkedEnvironment => fun x : ℕ => centroidDatum i ω x)
        (fun x => measurable_centroidDatum i x)
    exact ⟨f, hfeval, fun ω => ⟨(hf ω).1, (hf ω).2.2.1⟩⟩
  choose F hFmeas hF using hstep
  exact ⟨F, hFmeas, hF⟩

/-! ### The level energies are measurable -/

/-- The restricted energy of a measurable field on a *fixed* finite level is a measurable
function of the marked environment: it is a finite sum. -/
theorem measurable_restrictedEnergy_finset (s : SquareIndex) (t : Finset ℕ)
    {f : MarkedEnvironment → ℕ → ℝ} (hf : ∀ x : ℕ, Measurable fun ω => f ω x) :
    Measurable fun ω : MarkedEnvironment =>
      restrictedEnergy (patchGraph s ω) ((t : Set ℕ)) (f ω) := by
  have hEq : (fun ω : MarkedEnvironment =>
      restrictedEnergy (patchGraph s ω) ((t : Set ℕ)) (f ω))
      = fun ω : MarkedEnvironment =>
        (∑ q : Set.Elem (↑t : Set ℕ) × Set.Elem (↑t : Set ℕ),
          (patchGraph s ω).c q.1.1 q.2.1 * (f ω q.2.1 - f ω q.1.1) ^ 2) / 2 := by
    funext ω
    simp only [restrictedEnergy, ReflectedWalk.ConductanceGraph.Energy, tsum_fintype,
      ReflectedWalk.ConductanceGraph.gradSq] <;> rfl
  rw [hEq]
  refine Measurable.div_const ?_ 2
  refine Finset.measurable_sum Finset.univ fun q _ => ?_
  exact (measurable_patchGraph_c s q.1.1 q.2.1).mul
    (((hf q.2.1).sub (hf q.1.1)).pow_const 2)

/-- The energy of the level minimizer at the canonical level `n`. -/
noncomputable def levelEnergy (s : SquareIndex) (F : ℕ → MarkedEnvironment → ℕ → ℝ) (n : ℕ)
    (ω : MarkedEnvironment) : ℝ :=
  restrictedEnergy (patchGraph s ω)
    ((patchLevel (patchGraph s ω) (anchorLabels s ω) n : Finset ℕ) : Set ℕ) (F n ω)

/-- **The level energies are measurable.**  The level itself varies with the environment, but
it takes countably many values with measurable fibres, and on each fibre the energy is the
fixed finite sum of `measurable_restrictedEnergy_finset`. -/
theorem measurable_levelEnergy (s : SquareIndex) {F : ℕ → MarkedEnvironment → ℕ → ℝ}
    (hF : ∀ (n : ℕ) (x : ℕ), Measurable fun ω : MarkedEnvironment => F n ω x) (n : ℕ) :
    Measurable (levelEnergy s F n) := by
  have hfib : ∀ t : Finset ℕ, MeasurableSet
      {ω : MarkedEnvironment | patchLevel (patchGraph s ω) (anchorLabels s ω) n = t} :=
    fun t => measurableSet_patchLevel_eq (fun x y => measurable_patchGraph_c s x y)
      (fun x => measurableSet_mem_anchorLabels s x)
      (fun ω x => exists_isAnchorChain_patchGraph s ω x) n t
  intro B hB
  have hEq : levelEnergy s F n ⁻¹' B = ⋃ t : Finset ℕ,
      ({ω : MarkedEnvironment |
          patchLevel (patchGraph s ω) (anchorLabels s ω) n = t} ∩
        (fun ω : MarkedEnvironment =>
          restrictedEnergy (patchGraph s ω) ((t : Set ℕ)) (F n ω)) ⁻¹' B) := by
    refine Set.ext fun ω => ?_
    constructor
    · intro hω
      exact Set.mem_iUnion.2
        ⟨patchLevel (patchGraph s ω) (anchorLabels s ω) n, rfl, hω⟩
    · intro hω
      obtain ⟨t, hmem⟩ := Set.mem_iUnion.1 hω
      have ht : patchLevel (patchGraph s ω) (anchorLabels s ω) n = t := hmem.1
      have hval : levelEnergy s F n ω
          = restrictedEnergy (patchGraph s ω) ((t : Set ℕ)) (F n ω) := by
        rw [levelEnergy, ht]
      show levelEnergy s F n ω ∈ B
      rw [hval]
      exact hmem.2
  rw [hEq]
  exact MeasurableSet.iUnion fun t =>
    (hfib t).inter (measurable_restrictedEnergy_finset s t (hF n) hB)

/-! ### The per-square solvability event is measurable -/

/-- **The scalar solvability event is a countable union of countable intersections of
sublevel sets of the level energies.**  This is
`Forms/BoundedLevelEnergySolvability.exists_finiteEnergy_trace_iff_exists_nat` at every
marked environment. -/
theorem natSolvableEvent_eq (s : SquareIndex) (i : Fin 2)
    {F : ℕ → MarkedEnvironment → ℕ → ℝ}
    (htrace : ∀ (n : ℕ) (ω : MarkedEnvironment), ∀ a ∈ anchorLabels s ω,
      a ∈ patchLevel (patchGraph s ω) (anchorLabels s ω) n →
        F n ω a = centroidDatum i ω a)
    (hmin : ∀ (n : ℕ) (ω : MarkedEnvironment) (w : ℕ → ℝ),
      (∀ a ∈ anchorLabels s ω, a ∈ patchLevel (patchGraph s ω) (anchorLabels s ω) n →
        w a = centroidDatum i ω a) →
      restrictedEnergy (patchGraph s ω)
          ((patchLevel (patchGraph s ω) (anchorLabels s ω) n : Finset ℕ) : Set ℕ) (F n ω)
        ≤ restrictedEnergy (patchGraph s ω)
          ((patchLevel (patchGraph s ω) (anchorLabels s ω) n : Finset ℕ) : Set ℕ) w) :
    NatSolvableEvent s i
      = ⋃ k : ℕ, ⋂ n : ℕ, {ω : MarkedEnvironment | levelEnergy s F n ω ≤ (k : ℝ)} := by
  refine Set.ext fun ω => ?_
  have hkey := BoundedLevelEnergySolvability.exists_finiteEnergy_trace_iff_exists_nat
    (patchGraph s ω) (A := anchorLabels s ω) (u := fun n : ℕ => centroidDatum i ω n)
    (L := fun n : ℕ => patchLevel (patchGraph s ω) (anchorLabels s ω) n)
    (F := fun n : ℕ => F n ω)
    (boundaryAnchored_patchGraph s ω)
    (patchLevel_mono (patchGraph s ω))
    (fun x => exists_mem_patchLevel (patchGraph s ω)
      (fun y => exists_isAnchorChain_patchGraph s ω y) x)
    (fun n a ha haL => htrace n ω a ha haL)
    (fun n w hw => hmin n ω w fun a ha haL => hw a ha haL)
  constructor
  · intro hω
    obtain ⟨k, hk⟩ := hkey.1 hω
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iInter.2 fun n => hk n⟩
  · intro hω
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hω
    exact hkey.2 ⟨k, fun n => Set.mem_iInter.1 hk n⟩

/-- **The per-square solvability event is measurable.**  This is the single measurability
statement left open by
`Corrector/PatchSolvableEventMeasurability.measurable_gatedApproximant_of_squareSolvability`.
-/
theorem measurableSet_squareSolvableEvent (s : SquareIndex) :
    MeasurableSet (SquareSolvableEvent s) := by
  rw [squareSolvableEvent_eq_iInter s]
  refine MeasurableSet.iInter fun i => ?_
  obtain ⟨F, hFmeas, hF⟩ := exists_measurable_levelMinimizers s i
  rw [natSolvableEvent_eq s i (fun n ω => (hF n ω).1) (fun n ω w hw => (hF n ω).2 w hw)]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iInter fun n =>
    measurableSet_le (measurable_levelEnergy s hFmeas n) measurable_const

/-! ### The residual of `hmeas` -/

/-- **The one remaining input of `hmeas`.**  A measurable field, stage by stage and label by
label, which at every marked environment of the good event and at every positive stage is a
block interpolant whenever one exists.  Nothing is asked off the good event, at stage `0`, at
inactive labels, or when no block interpolant exists. -/
def HasMeasurableBlockInterpolantCandidate : Prop :=
  ∃ Ψ : ℕ → MarkedEnvironment → ℕ → Plane,
    (∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => Ψ m ω n) ∧
    ∀ m : ℕ, m ≠ 0 → ∀ ω : MarkedEnvironment, ω.1 ∈ SublinearEvent →
      (∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f) →
        IsBlockInterpolation (decode ω.1) ω.2 m fun v : Vertex ω.1.val => Ψ m ω v.val

/-- **`hmeas` from a measurable candidate family alone.**  The conclusion is literally the
`hmeas` hypothesis of `HarmonicCoordinateAssembly.harmonicCoordinateConclusions_of_named_inputs`
and of `HarmonicCoordinateSevenInputs`; the measurability of the gate is now a theorem, not a
hypothesis.  This is an implication, not a proof of `hmeas`. -/
theorem measurable_gatedApproximant_of_candidate
    {Ψ : ℕ → MarkedEnvironment → ℕ → Plane}
    (hΨ : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => Ψ m ω n)
    (hex : ∀ m : ℕ, m ≠ 0 → ∀ ω : MarkedEnvironment, ω.1 ∈ SublinearEvent →
      (∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f) →
        IsBlockInterpolation (decode ω.1) ω.2 m fun v : Vertex ω.1.val => Ψ m ω v.val)
    (m n : ℕ) :
    Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n :=
  measurable_gatedApproximant_of_squareSolvability hΨ measurableSet_squareSolvableEvent hex m n

/-- **The measurability input `hmeas` of the harmonic-coordinate assembly is exactly
`HasMeasurableBlockInterpolantCandidate`.** -/
theorem hmeas_of_measurableBlockInterpolantCandidate
    (h : HasMeasurableBlockInterpolantCandidate) (m n : ℕ) :
    Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n := by
  obtain ⟨Ψ, hΨ, hex⟩ := h
  exact measurable_gatedApproximant_of_candidate hΨ hex m n

/-! ### Anti-vacuity -/

end ReflectedGMS.BlockInterpolantSelectionSolvability
