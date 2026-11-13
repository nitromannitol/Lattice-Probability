/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GatedApproximantMeasurability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.HarmonicCoordinateAssembly
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GoodEnvironmentSet

/-!
# Measurability of the gated block interpolants

This module attacks the input `hmeas` of
`HarmonicCoordinateAssembly.harmonicCoordinateConclusions_of_named_inputs`,

`∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n`,

which the assembly names as having two halves: measurability of the good event
`SublinearEvent`, and a measurable selection of block minimizers agreeing with the concrete
`DyadicApproximation.phi` on that event.

* **The first half is discharged outright.**  `measurableSet_sublinearEvent` proves
  `MeasurableSet SublinearEvent` from the checked reduction of sublinear diameter decay to
  rational slopes, natural thresholds and rational radii
  (`GoodEnvironmentSet.sublinearDiameterDecay_iff_rat`) together with measurability of the
  large-cell diameter `D_R` as a countable slot supremum
  (`GoodEnvironmentSet.measurable_maxDiamHittingBall`).  This is unconditional.

* **The second half is isolated as one named, specification-shaped hypothesis.**
  `IsBlockInterpolantSelection m Θ` asks for a label-indexed field `Θ`, measurable in the
  marked environment, which on the good event **is** a block interpolant whenever one exists
  and is the centroid field whenever none exists.  No reference to `phi`, to
  `Classical.choose` or to any measurability beyond `Measurable fun ω => Θ ω n` occurs in it,
  and nothing at all is required off the good event or at inactive labels.

`eq_phi_of_isBlockInterpolantSelection` then identifies such a `Θ` with `phi` on the good
event — through uniqueness of block interpolants under sublinear diameter decay,
`HarmonicCoordinateAssembly.isBlockInterpolation_unique`, in the existence branch, and
through the default clause of `phi` in the non-existence branch, which is exactly why the
selection must also prescribe the centroid field there.  Measurability of `hmeas` follows in
`measurable_gatedApproximant_of_eq_phi` — whose hypothesis is only that some measurably
varying field agrees with `phi` at the active labels of the good event, so a producer working
directly with `phi` can enter there — and in its corollary
`measurable_gatedApproximant_of_selection`, and
`harmonicCoordinateConclusions_of_blockInterpolantSelection` restates the assembly's
reduction with `hmeas` replaced by the selection.

**This file proves no main theorem and does not certify `hmeas`.**  It removes the good-event
half of that input and reduces the rest to a pointwise selection property; a conditional
reduction certifies neither its input nor `HarmonicCoordinateMainTheorem`.

## Why the remaining half is not a small addendum

The concrete `phi F D m` is a `Classical.choose` over `∃ f, IsBlockInterpolation F D m f`,
defaulting to `cellCentroid F`, and existence of a block interpolant is **not** implied by
the gate: `PatchCentroidTraceFiniteEnergy.exists_isBlockInterpolation_of_spatialCellBounds`
derives it from the manuscript `W`-bound `SpatialDiameterCellBounds`, strictly stronger than
`SublinearDiameterDecay`.  So the selection has to be built, not chosen: the pinned mathlib
carries no measurable-selection theorem at all, and the project's own measurable minimizers
(`Corrector/MeasurableBlockMinimizer`, `Corrector/MeasurableInfinitePatchMinimizer`) are
scalar, are stated for one fixed countable vertex type, and assume boundary anchoring and
finite reference energy at *every* parameter value — all three of which the block problem
violates as stated (its vertex type `Vertex ω.1.val` varies with the environment, its data
are `Plane`-valued, and the centroid trace has finite patch energy only under the `W`-bound).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Classical

namespace ReflectedGMS.GatedApproximantMeasurability

open Code StatementIngredients EnvironmentLaws HarmonicLawIngredients DyadicApproximation
open HarmonicMainStatement NonmacroscopicSelectedBlocks Spatial GoodEnvironmentSet
open HarmonicCoordinateAssembly

/-! ### The good event of the construction is measurable -/

/-- The good event as a countable Boolean combination of level sets of `D_R`: sublinear
diameter decay reduces to rational slopes, natural thresholds and rational radii. -/
theorem sublinearEvent_eq_iInter :
    SublinearEvent
      = ⋂ ε : {ε : ℚ // 0 < ε}, ⋃ N : ℕ, ⋂ q : {q : ℚ // (N : ℝ) ≤ q},
          {e : Env | maxDiamHittingBall (decode e) (q.1 : ℝ)
            ≤ ENNReal.ofReal ((ε.1 : ℝ) * (q.1 : ℝ))} := by
  refine Set.ext fun e => ?_
  rw [mem_sublinearEvent_iff, sublinearDiameterDecay_iff_rat (decode e)]
  simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]

/-- **The good event `SublinearEvent` of the harmonic-coordinate construction is
measurable.**  This is the first of the two halves of the input `hmeas`. -/
theorem measurableSet_sublinearEvent : MeasurableSet SublinearEvent := by
  rw [sublinearEvent_eq_iInter]
  exact MeasurableSet.iInter fun ε => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun q =>
      measurableSet_le (measurable_maxDiamHittingBall (q.1 : ℝ)) measurable_const

/-! ### Measurable selections of block interpolants -/

/-- **A measurable selection of block interpolants at stage `m`.**

`Θ` is a label-indexed field, measurable in the marked environment, which at every marked
environment of the good event is a block interpolant whenever one exists, and is the centroid
field whenever none exists.  The second clause is not cosmetic: the concrete `phi` is a
`Classical.choose` which defaults to the centroid field exactly when no block interpolant
exists, so a selection that says nothing there cannot identify it.

Nothing is required off the good event, and nothing is required at inactive labels. -/
structure IsBlockInterpolantSelection (m : ℕ) (Θ : MarkedEnvironment → ℕ → Plane) : Prop where
  /-- The selection is measurable at every label. -/
  measurable : ∀ n : ℕ, Measurable fun ω : MarkedEnvironment => Θ ω n
  /-- On the good event the selection satisfies the block-interpolation specification
  whenever it is satisfiable. -/
  spec : ∀ ω : MarkedEnvironment, ω.1 ∈ SublinearEvent →
    (∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f) →
      IsBlockInterpolation (decode ω.1) ω.2 m fun v : Vertex ω.1.val => Θ ω v.val
  /-- On the good event the selection is the centroid field when the specification is not
  satisfiable. -/
  centroid : ∀ ω : MarkedEnvironment, ω.1 ∈ SublinearEvent →
    (¬ ∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f) →
      ∀ v : Vertex ω.1.val, Θ ω v.val = cellCentroid (decode ω.1) v

/-- **On the good event a selection is the concrete interpolant `phi`.**  In the existence
branch this is uniqueness of block interpolants under sublinear diameter decay; in the
non-existence branch both sides are the centroid field. -/
theorem eq_phi_of_isBlockInterpolantSelection {m : ℕ} {Θ : MarkedEnvironment → ℕ → Plane}
    (hΘ : IsBlockInterpolantSelection m Θ) {ω : MarkedEnvironment}
    (hG : ω.1 ∈ SublinearEvent) (v : Vertex ω.1.val) :
    Θ ω v.val = phi (decode ω.1) ω.2 m v := by
  by_cases hex : ∃ f : Vertex ω.1.val → Plane, IsBlockInterpolation (decode ω.1) ω.2 m f
  · have hsel := hΘ.spec ω hG hex
    have hphi := phi_spec_of_exists (decode ω.1) ω.2 m hex
    have heq : (fun v : Vertex ω.1.val => Θ ω v.val) = phi (decode ω.1) ω.2 m :=
      isBlockInterpolation_unique (decode ω.1) (decode_geometry ω.1) ω.2
        ((mem_sublinearEvent_iff ω.1).1 hG) m hsel hphi
    exact congrFun heq v
  · have hphi : phi (decode ω.1) ω.2 m = cellCentroid (decode ω.1) := by
      unfold phi
      rw [dif_neg hex]
    rw [hΘ.centroid ω hG hex v, hphi]

/-- **The measurability input `hmeas` of the harmonic-coordinate assembly, from any
measurably varying field agreeing with the concrete interpolants at the active labels of the
good event.**  Off the good event the gated interpolant vanishes, at an inactive label it
vanishes, and elsewhere it is the given field; nothing is asked of that field off the good
event or at inactive labels. -/
theorem measurable_gatedApproximant_of_eq_phi {Θ : ℕ → MarkedEnvironment → ℕ → Plane}
    (hmeasΘ : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => Θ m ω n)
    (hΘ : ∀ (m : ℕ) (ω : MarkedEnvironment), ω.1 ∈ SublinearEvent →
      ∀ v : Vertex ω.1.val, Θ m ω v.val = phi (decode ω.1) ω.2 m v) (m n : ℕ) :
    Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n := by
  have hEq : (fun ω : MarkedEnvironment => gatedApproximant m ω n)
      = fun ω : MarkedEnvironment =>
          if ω.1 ∈ SublinearEvent ∧ (ω.1.val.1 n).isSome then Θ m ω n else 0 := by
    funext ω
    by_cases hG : ω.1 ∈ SublinearEvent
    · rw [gatedApproximant_of_mem m hG n]
      by_cases hn : (ω.1.val.1 n).isSome
      · have hv : approximationAtLabel m ω n = phi (decode ω.1) ω.2 m ⟨n, hn⟩ :=
          approximationAtLabel_vertex m ω ⟨n, hn⟩
        rw [if_pos ⟨hG, hn⟩, hv]
        exact (hΘ m ω hG ⟨n, hn⟩).symm
      · have h0 : approximationAtLabel m ω n = 0 := by
          unfold approximationAtLabel
          rw [dif_neg hn]
        rw [if_neg fun h => hn h.2, h0]
    · rw [gatedApproximant_of_notMem m hG n, if_neg fun h => hG h.1]
  rw [hEq]
  refine Measurable.ite ?_ (hmeasΘ m n) measurable_const
  exact (measurable_fst measurableSet_sublinearEvent).inter
    (measurable_markedSlot n Spatial.measurableSet_slotIsSome)

/-- **The measurability input `hmeas` of the harmonic-coordinate assembly, from a measurable
selection of block interpolants.** -/
theorem measurable_gatedApproximant_of_selection {Θ : ℕ → MarkedEnvironment → ℕ → Plane}
    (hΘ : ∀ m : ℕ, IsBlockInterpolantSelection m (Θ m)) (m n : ℕ) :
    Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n :=
  measurable_gatedApproximant_of_eq_phi (fun m n => (hΘ m).measurable n)
    (fun m _ hG v => eq_phi_of_isBlockInterpolantSelection (hΘ m) hG v) m n

/-! ### The assembly's reduction with `hmeas` replaced by the selection -/

end ReflectedGMS.GatedApproximantMeasurability
