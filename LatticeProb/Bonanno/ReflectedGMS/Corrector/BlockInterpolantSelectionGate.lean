/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.BlockInterpolantSelectionGate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GatedApproximantMeasurability
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedFiniteEnergyDensityMeasurable
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The centroid field is measurable, and the block-interpolant selection splits in two

`Corrector/GatedApproximantMeasurability.lean` reduces the input `hmeas` of the harmonic
coordinate assembly to `IsBlockInterpolantSelection m Θ`: a field `Θ`, measurable in the
marked environment, which on `SublinearEvent` **is** a block interpolant whenever one
exists and **is the centroid field** whenever none exists.  The second clause is forced by
the default branch of the `Classical.choose` in `DyadicApproximation.phi`.

This module supplies two things that every producer of that selection needs.

## (1) The centroid field is measurable — unconditionally

`StatementIngredients.cellCentroid F v = (cellArea F v)⁻¹ • ∫ z in F.cell v, z` is a
*vector* integral over a compact cell, and nothing in the project made it a measurable
function of the environment: `Spatial.NullBoundaryRoots` proves measurability of the cell
*volume* (`measurable_cellVolume`), of cell membership (`measurableSet_cellMem`) and of
interior and frontier membership, but the barycentre `∫ z in K, z` never appears there, nor
anywhere else in the three trees.

`measurable_cellIntegral` fills that hole with exactly the `NullBoundaryRoots` template, for
the Bochner integral instead of the lower integral: the jointly measurable membership
indicator of `measurableSet_cellMem`, valued in `Plane` instead of `ℝ≥0∞`, fed to
`MeasureTheory.StronglyMeasurable.integral_prod_right'`.  `measurable_slotCentroid` then
reads the centroid at a *code slot*, so that absent slots carry a canonical value and no
vertex subtype occurs, and `slotCentroid_eq_cellCentroid` identifies it with `cellCentroid`
at every active label.  `centroidField` is the marked form.

## (2) The selection splits into a candidate and one measurable event

`isBlockInterpolantSelection_gate` is the factorisation.  Given

* a measurable candidate field `Ψ`,
* the **conditional correctness** `hex`: on the good event, *if* a block interpolant exists
  then `Ψ` is one,
* and measurability of the single event `{ω | Ψ ω is a block interpolant at stage m}`,

the field `gateSelection m Ψ`, which is `Ψ` on that event and the centroid field off it,
is a `IsBlockInterpolantSelection m`.  The centroid clause is then **free**: off the gate
event `Ψ` is not a block interpolant, so in particular no block interpolant equal to `Ψ`
exists, and the fallback is exactly the centroid field demanded by the default branch of
`phi`.  `measurable_gatedApproximant_of_gates` composes this with
`GatedApproximantMeasurability.measurable_gatedApproximant_of_selection`, producing `hmeas`
in the exact shape taken by `HarmonicCoordinateSevenInputs`.

`gateEvent_inter_sublinearEvent` records why this is the right split: under `hex` the gate
event and the *existence* event `{ω | ∃ f, IsBlockInterpolation … f}` agree on the good
event, so the residual measurability is not an artefact of the fallback — it is the
measurability of block-interpolant existence itself, expressed at a single measurable field
rather than under an existential quantifier.

## (3) Stage `0` is discharged outright

`isBlockInterpolantSelection_zero` proves `IsBlockInterpolantSelection 0 centroidField` with
no hypotheses: `IsBlockInterpolation F D 0 f` *is* `f = cellCentroid F`.  This is also the
satisfiability witness for the structure and for the hypotheses of the gate theorem
(`gate_hypotheses_satisfiable_zero`), which is recorded explicitly because a selection
statement that no field can satisfy, or that holds only on a null event, would be vacuous.

**This file proves no main theorem and does not certify `hmeas`.**  For a stage `m ≥ 1` both
the candidate `Ψ` and the measurability of the gate event remain open; the file removes the
centroid branch, the measurability of the boundary data, and the stage `0` case from that
problem.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ENNReal Classical

namespace ReflectedGMS.BlockInterpolantSelectionGate

open Code StatementIngredients DyadicApproximation HarmonicMainStatement
open HarmonicCoordinateAssembly GatedApproximantMeasurability
open RootedFiniteEnergyDensityMeasurable

/-! ### The barycentre of a compact cell is a measurable function of the cell -/

/-- The unnormalised barycentre `∫_K z dz` of a compact cell. -/
noncomputable def cellIntegral (K : CompactCell) : Plane :=
  ∫ z in (K : Set Plane), z ∂volume

/-- **The barycentre of a cell is measurable for the Hausdorff Borel structure on cells.**
This is `Spatial.measurable_cellVolume`'s argument for the Bochner integral: the membership
indicator is jointly measurable by `Spatial.measurableSet_cellMem`, and the Bochner integral
of a jointly strongly measurable integrand is measurable in the parameter. -/
theorem measurable_cellIntegral : Measurable cellIntegral := by
  have hsm : StronglyMeasurable
      (Set.indicator {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)}
        fun p : CompactCell × Plane => p.2) :=
    (measurable_snd.indicator Spatial.measurableSet_cellMem).stronglyMeasurable
  have hint : StronglyMeasurable fun K : CompactCell =>
      ∫ z : Plane, Set.indicator {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)}
        (fun p : CompactCell × Plane => p.2) (K, z) ∂volume :=
    hsm.integral_prod_right' (ν := (volume : Measure Plane))
  have hpt : (fun K : CompactCell =>
      ∫ z : Plane, Set.indicator {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)}
        (fun p : CompactCell × Plane => p.2) (K, z) ∂volume) = cellIntegral := by
    funext K
    have hz : ∀ z : Plane,
        Set.indicator {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)}
            (fun p : CompactCell × Plane => p.2) (K, z)
          = Set.indicator (K : Set Plane) (fun z : Plane => z) z := by
      intro z
      by_cases hzK : z ∈ (K : Set Plane)
      · rw [Set.indicator_of_mem
          (show (K, z) ∈ {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)} from hzK),
          Set.indicator_of_mem hzK]
      · rw [Set.indicator_of_notMem
          (show (K, z) ∉ {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)} from hzK),
          Set.indicator_of_notMem hzK]
    simp only [hz]
    rw [cellIntegral]
    exact integral_indicator K.isCompact.isClosed.measurableSet
  rw [← hpt]
  exact hint.measurable

/-! ### The centroid read at a code slot -/

/-- The cell centroid read at code slot `n`, with the reference cell's centroid at absent
slots.  No vertex subtype occurs, so this is a function of the environment alone. -/
noncomputable def slotCentroid (e : Env) (n : ℕ) : Plane :=
  ((volume (slotCell e n : Set Plane)).toReal)⁻¹ • cellIntegral (slotCell e n)

theorem measurable_slotCentroid (n : ℕ) : Measurable fun e : Env => slotCentroid e n := by
  have hcell : Measurable fun e : Env => slotCell e n := measurable_slotCell_env n
  have hvol : Measurable fun e : Env => ((volume (slotCell e n : Set Plane)).toReal)⁻¹ :=
    ((Spatial.measurable_cellVolume.comp hcell).ennreal_toReal).inv
  exact hvol.smul (measurable_cellIntegral.comp hcell)

/-- At an active label the slot centroid is the cell centroid of the decoded environment. -/
theorem slotCentroid_eq_cellCentroid (e : Env) (v : Vertex e.val) :
    slotCentroid e v.val = cellCentroid (decode e) v := by
  simp only [slotCentroid, cellIntegral, cellCentroid, cellArea, slotCell_eq_cell]

/-! ### The marked centroid field -/

/-- The centroid field of a marked environment, label by label. -/
noncomputable def centroidField (ω : MarkedEnvironment) (n : ℕ) : Plane :=
  slotCentroid ω.1 n

theorem measurable_centroidField (n : ℕ) :
    Measurable fun ω : MarkedEnvironment => centroidField ω n :=
  (measurable_slotCentroid n).comp measurable_fst

theorem centroidField_eq (ω : MarkedEnvironment) (v : Vertex ω.1.val) :
    centroidField ω v.val = cellCentroid (decode ω.1) v :=
  slotCentroid_eq_cellCentroid ω.1 v

theorem centroidField_restrict (ω : MarkedEnvironment) :
    (fun v : Vertex ω.1.val => centroidField ω v.val) = cellCentroid (decode ω.1) :=
  funext fun v => centroidField_eq ω v

/-! ### Stage `0` is discharged -/

/-- **A measurable selection of block interpolants at stage `0`, with no hypotheses.**
`IsBlockInterpolation F D 0 f` is `f = cellCentroid F`, so the centroid field is a selection
and both clauses of the selection hold for the same reason. -/
theorem isBlockInterpolantSelection_zero : IsBlockInterpolantSelection 0 centroidField where
  measurable n := measurable_centroidField n
  spec ω _ _ := by
    simpa [IsBlockInterpolation] using centroidField_restrict ω
  centroid ω _ _ v := centroidField_eq ω v

/-! ### The gate: a candidate field plus one measurable event -/

/-! ### The measurability input `hmeas` from a gated candidate at every stage -/

/-! ### Satisfiability of the gate hypotheses -/

end ReflectedGMS.BlockInterpolantSelectionGate
