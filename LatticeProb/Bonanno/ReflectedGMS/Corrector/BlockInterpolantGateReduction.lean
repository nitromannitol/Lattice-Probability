/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.BlockInterpolantGateReduction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BlockInterpolantSelectionGate
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AlmostSureSpatialDiameterBounds

/-!
# The block-interpolant gate event is exactly per-square Dirichlet solvability

`Corrector/BlockInterpolantSelectionGate.lean` reduces the measurability input `hmeas` of the
harmonic-coordinate assembly, at every stage `m`, to two things: a measurable candidate field
`Ψ` that is a block interpolant wherever one exists on the good event, and measurability of
the **gate event** `{ω | Ψ ω is a block interpolant at stage m}`.  Stage `0` is closed there;
`m ≥ 1` is not.

This module does two independent things to that residual.

## (1) The gate event may be replaced by *any* measurable set agreeing with existence on the
good event

`isBlockInterpolantSelection_proxy` weakens the second hypothesis of
`BlockInterpolantSelectionGate.isBlockInterpolantSelection_gate` from

  `MeasurableSet (GateEvent m Ψ)` — a measurability statement about the *candidate* —

to

  a measurable `E` with `GoodMarked ∩ E = GoodMarked ∩ ExistenceEvent m`.

Nothing is asked of `E` off the good event, and the candidate `Ψ` no longer has to be
decidable in a measurable way anywhere.  `proxy_of_measurableSet_gateEvent` records that this
is a genuine weakening: the old hypothesis produces such an `E`, namely the gate event
itself, by `BlockInterpolantSelectionGate.gateEvent_inter_sublinearEvent`.

## (2) On `m ≥ 1` the existence event *is* the per-square solvability event

`exists_isBlockInterpolation_iff_patchSolvable` is an unconditional two-sided identity, valid
at every environment because `Code.decode_geometry` supplies `Geometry (decode e)` for free:
for `m ≠ 0`,

  `(∃ f, IsBlockInterpolation F D m f)  ↔  PatchSolvable F D m`,

where `PatchSolvable F D m` says only that **on every `κ`-selected dyadic square** some
plane-valued field on that square's patch has finite vector energy and the centroid trace on
the patch's spatial boundary.  The `⟸` half is
`BlockInterpolantExistence.exists_isBlockInterpolation_of_geometry` (gluing plus the
per-square Dirichlet problem, where `Geometry/BoundaryAnchoring` discharges the anchoring);
the `⟹` half is the observation that a block interpolant restricts on each selected patch to
an admissible competitor.

So the measurability residual of `hmeas` for `m ≥ 1` contains **no gluing, no skeleton
pinning and no minimality quantifier**: those three are exactly what the identity removes.
What is left is one per-square existential over plane-valued patch fields, and
`patchSolvable_iff_coord` splits even that into the two scalar Dirichlet problems that the
project's measurable-minimizer machinery (`Corrector/MeasurableBlockMinimizer`,
`Corrector/MeasurableInfinitePatchMinimizer`) is stated for.

`measurable_gatedApproximant_of_patchSolvableProxies` is the composite: it produces literally
the `hmeas` hypothesis of
`HarmonicCoordinateSevenInputs.harmonicCoordinateConclusions_of_seven_inputs` from a family
of measurable candidates and a family of measurable proxies for the *solvability* events,
with stage `0` discharged internally by
`BlockInterpolantSelectionGate.isBlockInterpolantSelection_zero`.

## Anti-vacuity

The trap for this packet is a gate event that is measurable because it is empty or null.  It
is neither.  `patchSolvable_of_spatialPiBounds` shows the solvability event contains the
manuscript `W`-bound event, and `ae_patchSolvable_of_ballBound` shows that under the
project's own spatial maximal bound the event is **conull at every stage and every grid**, so
the proxy `E` that a producer must supply is a.s. the whole space, not a null set.  The
reduction in (2) is an *equality* of events proved in both directions, so a producer cannot
discharge it by a one-sided inclusion, and the argument for satisfiability is not circular:
it runs through `SpatialDiameterCellBounds`, which
`Spatial/AlmostSureSpatialDiameterBounds` derives from the mass-transport and finite-energy
hypotheses of the law, never from the conclusion.

**This file proves no main theorem and does not certify `hmeas`.**  For `m ≥ 1` both the
candidate `Ψ` and the measurable proxy `E` remain open.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ENNReal Classical

namespace ReflectedGMS.BlockInterpolantGateReduction

open Code StatementIngredients DyadicApproximation HarmonicMainStatement
open HarmonicCoordinateAssembly GatedApproximantMeasurability
open BlockInterpolantSelectionGate PatchCentroidTraceFiniteEnergy

variable {V : Type*}

/-! ### Per-square solvability of the Dirichlet problem with the centroid trace -/

/-- **Per-square solvability.**  On every `κ`-selected dyadic square some plane-valued field
on that square's patch has finite vector energy and carries the centroid trace on the
patch's spatial boundary.  This is the hypothesis `hfin` of
`BlockInterpolantExistence.exists_isBlockInterpolation_of_geometry`, named. -/
def PatchSolvable (F : IndexedCells V) (D : Grid) (m : ℕ) : Prop :=
  ∀ s : SquareIndex, Selected F D (m : ℝ) s →
    ∃ u : patchVertices F (square D s) → Plane,
      vectorEnergy (restrictGraph F.graph (patchVertices F (square D s))) u < ∞ ∧
      ∀ v : patchVertices F (square D s), v.1 ∈ boundaryVertices F (square D s) →
        u v = cellCentroid F v.1

/-- **A block interpolant restricts to an admissible competitor on every selected patch.**
This is the half of the identity that the existence producer does not give: for `m ≠ 0` the
specification asserts a `CentroidTraceMinimizer` on every selected square, whose first two
clauses are exactly finite patch energy and the centroid boundary trace. -/
theorem patchSolvable_of_exists_isBlockInterpolation (F : IndexedCells V) (D : Grid) {m : ℕ}
    (hm : m ≠ 0) (h : ∃ f : V → Plane, IsBlockInterpolation F D m f) :
    PatchSolvable F D m := by
  obtain ⟨f, hf⟩ := h
  rw [IsBlockInterpolation, if_neg hm] at hf
  intro s hs
  obtain ⟨hfin, htr, -⟩ := hf.2 s hs
  exact ⟨fun v => f v.1, hfin, htr⟩

/-- **Existence of a block interpolant is exactly per-square solvability**, at every stage
`m ≠ 0` and at every environment satisfying `Geometry F`.

The `⟸` half is `BlockInterpolantExistence.exists_isBlockInterpolation_of_geometry`: the
per-square Dirichlet problems are solved by `Forms/VectorTraceMinimizer`, their anchoring is
free by `Geometry/BoundaryAnchoring`, and the solutions glue.  The `⟹` half is
`patchSolvable_of_exists_isBlockInterpolation`.  No probability, no measurability and no
sublinear diameter decay enter. -/
theorem exists_isBlockInterpolation_iff_patchSolvable [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (D : Grid) {m : ℕ} (hm : m ≠ 0) :
    (∃ f : V → Plane, IsBlockInterpolation F D m f) ↔ PatchSolvable F D m :=
  ⟨patchSolvable_of_exists_isBlockInterpolation F D hm,
    BlockInterpolantExistence.exists_isBlockInterpolation_of_geometry F hF D m⟩

/-! ### The plane-valued per-square problem splits into two scalar problems -/

/-! ### The events on the marked configuration space -/

/-- The good event of the harmonic-coordinate construction, read on marked configurations. -/
def GoodMarked : Set MarkedEnvironment := {ω : MarkedEnvironment | ω.1 ∈ SublinearEvent}

/-- Existence of a block interpolant at stage `m`, as an event. -/
def ExistenceEvent (m : ℕ) : Set MarkedEnvironment :=
  {ω : MarkedEnvironment |
    ∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f}

/-- Per-square solvability at stage `m`, as an event. -/
def PatchSolvableEvent (m : ℕ) : Set MarkedEnvironment :=
  {ω : MarkedEnvironment | PatchSolvable (decode ω.1) ω.2 m}

/-- **The existence event and the solvability event are the same set**, at every stage
`m ≠ 0`.  `Code.decode_geometry` supplies the geometry hypothesis at every environment, so
this is an unconditional identity of subsets of `Env × Grid`, not an almost-sure one. -/
theorem existenceEvent_eq_patchSolvableEvent {m : ℕ} (hm : m ≠ 0) :
    ExistenceEvent m = PatchSolvableEvent m :=
  Set.ext fun ω =>
    exists_isBlockInterpolation_iff_patchSolvable (decode ω.1) (decode_geometry ω.1) ω.2 hm

/-! ### The gate against an arbitrary measurable proxy for existence -/

/-- The candidate field on a proxy event, the centroid field off it. -/
noncomputable def proxySelection (E : Set MarkedEnvironment)
    (Ψ : MarkedEnvironment → ℕ → Plane) (ω : MarkedEnvironment) (n : ℕ) : Plane :=
  if ω ∈ E then Ψ ω n else centroidField ω n

/-- **The block-interpolant selection from a conditionally correct candidate and a measurable
proxy for the existence event.**

Compared with `BlockInterpolantSelectionGate.isBlockInterpolantSelection_gate` the
measurability obligation has moved off the candidate: `E` is an arbitrary measurable set that
decides existence correctly *on the good event only*, and is unconstrained elsewhere.  The
proof of the centroid clause is the same as there — off `E` no block interpolant exists, and
the fallback is the centroid field prescribed by the default branch of `phi`. -/
theorem isBlockInterpolantSelection_proxy (m : ℕ) {Ψ : MarkedEnvironment → ℕ → Plane}
    (hΨ : ∀ n : ℕ, Measurable fun ω : MarkedEnvironment => Ψ ω n)
    {E : Set MarkedEnvironment} (hE : MeasurableSet E)
    (hagree : GoodMarked ∩ E = GoodMarked ∩ ExistenceEvent m)
    (hex : ∀ ω : MarkedEnvironment, ω.1 ∈ SublinearEvent →
      (∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f) →
        IsBlockInterpolation (decode ω.1) ω.2 m fun v : Vertex ω.1.val => Ψ ω v.val) :
    IsBlockInterpolantSelection m (proxySelection E Ψ) where
  measurable n := by
    have hE' : MeasurableSet {ω : MarkedEnvironment | ω ∈ E} := hE
    show Measurable fun ω : MarkedEnvironment =>
      if ω ∈ E then Ψ ω n else centroidField ω n
    exact Measurable.ite hE' (hΨ n) (measurable_centroidField n)
  spec ω hG hexists := by
    have hmem : ω ∈ GoodMarked ∩ E := by
      rw [hagree]
      exact ⟨hG, hexists⟩
    have hfun : (fun v : Vertex ω.1.val => proxySelection E Ψ ω v.val)
        = fun v : Vertex ω.1.val => Ψ ω v.val := by
      funext v
      simp only [proxySelection, if_pos hmem.2]
    rw [hfun]
    exact hex ω hG hexists
  centroid ω hG hnex v := by
    have hnot : ω ∉ E := by
      intro hmemE
      have : ω ∈ GoodMarked ∩ ExistenceEvent m := by
        rw [← hagree]
        exact ⟨hG, hmemE⟩
      exact hnex this.2
    simp only [proxySelection, if_neg hnot]
    exact centroidField_eq ω v

/-- **The selection from a proxy for the per-square solvability event**, at a stage `m ≠ 0`.
This is `isBlockInterpolantSelection_proxy` with the existence event replaced by the
solvability event through `existenceEvent_eq_patchSolvableEvent`. -/
theorem isBlockInterpolantSelection_patchSolvableProxy {m : ℕ} (hm : m ≠ 0)
    {Ψ : MarkedEnvironment → ℕ → Plane}
    (hΨ : ∀ n : ℕ, Measurable fun ω : MarkedEnvironment => Ψ ω n)
    {E : Set MarkedEnvironment} (hE : MeasurableSet E)
    (hagree : GoodMarked ∩ E = GoodMarked ∩ PatchSolvableEvent m)
    (hex : ∀ ω : MarkedEnvironment, ω.1 ∈ SublinearEvent →
      (∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f) →
        IsBlockInterpolation (decode ω.1) ω.2 m fun v : Vertex ω.1.val => Ψ ω v.val) :
    IsBlockInterpolantSelection m (proxySelection E Ψ) :=
  isBlockInterpolantSelection_proxy m hΨ hE
    (by rw [hagree, existenceEvent_eq_patchSolvableEvent hm]) hex

/-! ### `hmeas` from stagewise candidates and proxies -/

/-- The selection used at every stage: the centroid field at stage `0`, where
`BlockInterpolantSelectionGate.isBlockInterpolantSelection_zero` already closes the problem,
and the gated candidate at every positive stage. -/
noncomputable def stagedSelection (Ψ : ℕ → MarkedEnvironment → ℕ → Plane)
    (E : ℕ → Set MarkedEnvironment) (m : ℕ) : MarkedEnvironment → ℕ → Plane :=
  if m = 0 then centroidField else proxySelection (E m) (Ψ m)

theorem isBlockInterpolantSelection_stagedSelection
    {Ψ : ℕ → MarkedEnvironment → ℕ → Plane} {E : ℕ → Set MarkedEnvironment}
    (hΨ : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => Ψ m ω n)
    (hE : ∀ m : ℕ, m ≠ 0 → MeasurableSet (E m))
    (hagree : ∀ m : ℕ, m ≠ 0 → GoodMarked ∩ E m = GoodMarked ∩ PatchSolvableEvent m)
    (hex : ∀ (m : ℕ), m ≠ 0 → ∀ ω : MarkedEnvironment, ω.1 ∈ SublinearEvent →
      (∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f) →
        IsBlockInterpolation (decode ω.1) ω.2 m fun v : Vertex ω.1.val => Ψ m ω v.val)
    (m : ℕ) : IsBlockInterpolantSelection m (stagedSelection Ψ E m) := by
  by_cases hm : m = 0
  · subst hm
    have h0 : stagedSelection Ψ E 0 = centroidField := by
      simp [stagedSelection]
    rw [h0]
    exact isBlockInterpolantSelection_zero
  · have hpos : stagedSelection Ψ E m = proxySelection (E m) (Ψ m) := by
      simp only [stagedSelection, if_neg hm]
    rw [hpos]
    exact isBlockInterpolantSelection_patchSolvableProxy hm (hΨ m) (hE m hm)
      (hagree m hm) (hex m hm)

/-- **The measurability input `hmeas` of the harmonic-coordinate assembly from stagewise
candidates and proxies for the per-square solvability events.**

The conclusion is literally the `hmeas` hypothesis of
`HarmonicCoordinateSevenInputs.harmonicCoordinateConclusions_of_seven_inputs`.  Stage `0` is
discharged inside; the three hypotheses are required only at the positive stages, and this is
an implication, not a proof of `hmeas`. -/
theorem measurable_gatedApproximant_of_patchSolvableProxies
    {Ψ : ℕ → MarkedEnvironment → ℕ → Plane} {E : ℕ → Set MarkedEnvironment}
    (hΨ : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => Ψ m ω n)
    (hE : ∀ m : ℕ, m ≠ 0 → MeasurableSet (E m))
    (hagree : ∀ m : ℕ, m ≠ 0 → GoodMarked ∩ E m = GoodMarked ∩ PatchSolvableEvent m)
    (hex : ∀ (m : ℕ), m ≠ 0 → ∀ ω : MarkedEnvironment, ω.1 ∈ SublinearEvent →
      (∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f) →
        IsBlockInterpolation (decode ω.1) ω.2 m fun v : Vertex ω.1.val => Ψ m ω v.val)
    (m n : ℕ) :
    Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n :=
  measurable_gatedApproximant_of_selection
    (isBlockInterpolantSelection_stagedSelection hΨ hE hagree hex) m n

/-! ### Anti-vacuity: the solvability event is conull, not null -/

end ReflectedGMS.BlockInterpolantGateReduction
