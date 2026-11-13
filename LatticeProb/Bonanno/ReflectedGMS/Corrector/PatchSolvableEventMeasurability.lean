/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.PatchSolvableEventMeasurability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BlockInterpolantGateReduction
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MeasurableSelectedAtIndex
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MeasurableEndpointTransport
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SpatialMaximalForFiniteEnergy

/-!
# `hmeas` for every stage from one per-square measurability statement

`Corrector/BlockInterpolantGateReduction.lean` identifies the block-interpolant existence
event with the per-square solvability event `PatchSolvableEvent m`, at every stage `m ≠ 0`,
and reduces the measurability input `hmeas` of the harmonic-coordinate assembly to a
measurable proxy for that event.  `Corrector/MeasurableSelectedAtIndex.lean` makes every
selection event `{(e, D) | Selected (decode e) D m s}` measurable, at an **arbitrary** square
index `s`.

This module composes the two.  `PatchSolvable F D m` is a conjunction over the countable
index type `SquareIndex` of implications "selected `⟹` solvable", so

  `PatchSolvableEvent m = ⋂ s, (SelectedEvent m s)ᶜ ∪ SquareSolvableEvent s`,

a countable intersection.  The first half of every term is now measurable, so the whole
residual of `hmeas` at the stages `m ≥ 1` is the measurability of the **single per-square
event**

  `SquareSolvableEvent s = {ω | some finite-vector-energy field on the patch of `square ω.2 s`
   carries the centroid trace on that patch's spatial boundary}`,

which does not mention the stage `m`, the skeleton, the gluing, the block index, or the
minimality of any field.  `measurable_gatedApproximant_of_squareSolvability` is the
composite: it produces literally the `hmeas` hypothesis of
`HarmonicCoordinateSevenInputs.harmonicCoordinateConclusions_of_seven_inputs` from a
measurable candidate family and that one measurability statement.

## Anti-vacuity

`spatialPiBounds_subset_squareSolvableEvent` shows `SquareSolvableEvent s` contains the
manuscript `W`-bound event at every `s`, and `ae_squareSolvable_of_ballBound` shows it is
conull under the project's own spatial maximal bound.  So the event whose measurability
remains open is a.s. the whole space, not a null or empty set, and the identification with
the existence event is a two-sided equality (`BlockInterpolantGateReduction`), not a
one-sided sufficient condition.  The satisfiability argument runs through
`Spatial/AlmostSureSpatialDiameterBounds`, i.e. through the mass-transport and finite-energy
hypotheses of the law, and never through the conclusion.

**This file proves no main theorem and does not certify `hmeas`.**
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ENNReal Classical

namespace ReflectedGMS.PatchSolvableEventMeasurability

open Code StatementIngredients DyadicApproximation HarmonicMainStatement
open HarmonicCoordinateAssembly GatedApproximantMeasurability
open BlockInterpolantSelectionGate BlockInterpolantGateReduction
open MeasurableSelectedAtIndex PatchCentroidTraceFiniteEnergy

variable {V : Type*}

/-! ### Solvability on a single square -/

/-- **The per-square Dirichlet problem.**  Some plane-valued field on the patch of one
dyadic square has finite vector energy and carries the centroid trace on the patch's spatial
boundary.  No stage, no block index and no minimality occur. -/
def SquareSolvable (F : IndexedCells V) (D : Grid) (s : SquareIndex) : Prop :=
  ∃ u : patchVertices F (square D s) → Plane,
    vectorEnergy (restrictGraph F.graph (patchVertices F (square D s))) u < ∞ ∧
    ∀ v : patchVertices F (square D s), v.1 ∈ boundaryVertices F (square D s) →
      u v = cellCentroid F v.1

/-! ### The events -/

/-- The selection event of one square at stage `m`, on marked configurations. -/
def SelectedEvent (m : ℕ) (s : SquareIndex) : Set MarkedEnvironment :=
  {ω : MarkedEnvironment | Selected (decode ω.1) ω.2 (m : ℝ) s}

/-- The per-square solvability event.  It does not depend on the stage. -/
def SquareSolvableEvent (s : SquareIndex) : Set MarkedEnvironment :=
  {ω : MarkedEnvironment | SquareSolvable (decode ω.1) ω.2 s}

/-- **Every selection event is measurable**, by
`MeasurableSelectedAtIndex.measurableSet_selected`. -/
theorem measurableSet_selectedEvent (m : ℕ) (s : SquareIndex) :
    MeasurableSet (SelectedEvent m s) :=
  measurableSet_selected_nat m s

/-- **The solvability event is a countable intersection over the dyadic squares.** -/
theorem patchSolvableEvent_eq_iInter (m : ℕ) :
    PatchSolvableEvent m
      = ⋂ s : SquareIndex, ((SelectedEvent m s)ᶜ ∪ SquareSolvableEvent s) := by
  refine Set.ext fun ω => ?_
  simp only [PatchSolvableEvent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union,
    Set.mem_compl_iff]
  constructor
  · intro h s
    by_cases hs : ω ∈ SelectedEvent m s
    · exact Or.inr (h s hs)
    · exact Or.inl hs
  · intro h s hs
    rcases h s with hns | hsol
    · exact absurd hs hns
    · exact hsol

/-- **The measurability of the solvability event reduces to the per-square event.** -/
theorem measurableSet_patchSolvableEvent (m : ℕ)
    (hsq : ∀ s : SquareIndex, MeasurableSet (SquareSolvableEvent s)) :
    MeasurableSet (PatchSolvableEvent m) := by
  rw [patchSolvableEvent_eq_iInter m]
  exact MeasurableSet.iInter fun s =>
    ((measurableSet_selectedEvent m s).compl).union (hsq s)

/-! ### `hmeas` from the per-square measurability -/

/-- **The measurability input `hmeas` of the harmonic-coordinate assembly from a measurable
candidate family and measurability of the per-square solvability event.**

The conclusion is literally the `hmeas` hypothesis of
`HarmonicCoordinateSevenInputs.harmonicCoordinateConclusions_of_seven_inputs`.  Stage `0` is
discharged inside by `BlockInterpolantSelectionGate.isBlockInterpolantSelection_zero`; at the
positive stages the proxy is the solvability event itself, so the agreement hypothesis of
`BlockInterpolantGateReduction.measurable_gatedApproximant_of_patchSolvableProxies` is an
identity.  This is an implication, not a proof of `hmeas`. -/
theorem measurable_gatedApproximant_of_squareSolvability
    {Ψ : ℕ → MarkedEnvironment → ℕ → Plane}
    (hΨ : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => Ψ m ω n)
    (hsq : ∀ s : SquareIndex, MeasurableSet (SquareSolvableEvent s))
    (hex : ∀ (m : ℕ), m ≠ 0 → ∀ ω : MarkedEnvironment, ω.1 ∈ SublinearEvent →
      (∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f) →
        IsBlockInterpolation (decode ω.1) ω.2 m fun v : Vertex ω.1.val => Ψ m ω v.val)
    (m n : ℕ) :
    Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n :=
  measurable_gatedApproximant_of_patchSolvableProxies (E := fun k => PatchSolvableEvent k)
    hΨ (fun k _ => measurableSet_patchSolvableEvent k hsq) (fun _ _ => rfl) hex m n

/-! ### Anti-vacuity -/

end ReflectedGMS.PatchSolvableEventMeasurability
