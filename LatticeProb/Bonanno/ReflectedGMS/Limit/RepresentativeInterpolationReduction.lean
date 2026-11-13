/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.RepresentativeInterpolationReduction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.InterpolatedTwoClockReduction
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# The construction half of `hlimit`, split and reduced

`InterpolatedTwoClockReduction.RepresentativeInterpolationData` — the construction half of
the `hlimit` slot — had **zero producers**.  It is *not* the FCLT: it asks only that the two
spatial extensions of the representative rule and the two continuous interpolations exist,
satisfy the pathwise clauses almost surely, and that the interpolations are measurable into
`BouRabeeGwynne.BrownianPath 2`.

This file does three things to it, none of which is the construction itself.

## 1. The two clocks separate

`OneClockInterpolationData` is the same statement for **one** lifted path.  The two clocks
are staffed by different lanes (the exponential clock by the area-clock construction, the
exact clock by the clock-collapse lane), and
`representativeInterpolationData_of_clocks` recombines them.  Nothing is lost: the four
pathwise clauses of `PathwiseInterpolationClauses` are two clauses about `Xexp, Zexp, Iexp`
and two about `Xexact, Zexact, Iexact`, with no clause coupling the clocks.

## 2. The objects are canonical, so this is a measurability obligation and not a selection
problem

`isContinuousInterpolation_unique` — proved here, and new — says that for a fixed vertex
path `X`, representative field `z` and spatial extension `Z`, the continuous interpolation
is **unique**: on every vertex time it is pinned by the linear formula over the complete
preceding holding interval (which exists by `HasCompleteHoldingIntervals`), and on every
end time it is pinned to `Z`.  Together with the uniqueness clause already carried by
`RegularSpatialExtension`, this gives `ae_eq_of_oneClockInterpolationData`: any two witnesses
of `OneClockInterpolationData` agree almost surely, in both components.

Consequently the open content of the construction half is exactly: *does the canonical
interpolation exist pathwise, and is it measurable* — there is no choice to make and no
measurable-selection theorem to invoke.

## 3. Measurability reduces to the evaluations

`oneClockInterpolationData_of_eval_measurable` replaces `Measurable I`, a statement about the
compact-open Borel structure of the path space, by measurability of `ω ↦ I ω r` at each fixed
time `r`, through mathlib's `ContinuousMap.measurable_iff_eval`.

**Nothing here certifies `RepresentativeInterpolationData` at the reflected walk.**  The
smallest honest input left by this file is: a pathwise-defined `Z` and `I` for one clock,
with the two pathwise clauses holding almost surely and with `ω ↦ I ω r` measurable at each
`r`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.RepresentativeInterpolationReduction

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.InterpolatedTwoClockReduction

/-! ## Uniqueness of the continuous interpolation -/

/-! ## The one-clock construction datum -/

/-- **The construction half of `hlimit` for one lifted path.**

`RepresentativeInterpolationData` is exactly the conjunction of this statement at `Xexp` and
at `Xexact` (`representativeInterpolationData_of_clocks`). -/
def OneClockInterpolationData (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (start : Vertex e.val)
    (X : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e)) : Prop :=
  ∃ (Z : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (I : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
    Measurable I ∧
      ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
        RegularSpatialExtension (decode e) (z.at e) (fun t => X t ω) (fun t => Z t ω) ∧
        IsContinuousInterpolation (decode e) (z.at e) (fun t => X t ω)
          (fun t => Z t ω) (I ω)

/-- **`RepresentativeInterpolationData` from the two one-clock data.**  No clause of
`PathwiseInterpolationClauses` couples the two clocks, so the split is lossless. -/
theorem representativeInterpolationData_of_clocks (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (hexp : OneClockInterpolationData e D hG z start Xexp)
    (hexact : OneClockInterpolationData e D hG z start Xexact) :
    RepresentativeInterpolationData e D hG z start Xexp Xexact := by
  obtain ⟨Zexp, Iexp, hmexp, hpexp⟩ := hexp
  obtain ⟨Zexact, Iexact, hmexact, hpexact⟩ := hexact
  refine ⟨Zexp, Zexact, Iexp, Iexact, hmexp, hmexact, ?_⟩
  filter_upwards [hpexp, hpexact] with ω h1 h2
  exact ⟨h1.1, h2.1, h1.2, h2.2⟩

/-- **Measurability of the interpolation reduces to its evaluations.**

`ContinuousMap.measurable_iff_eval` identifies the Borel structure of the compact-open
topology on `C(ℝ≥0, Plane)` with the one generated by the time evaluations, so the path-space
measurability asked by `RepresentativeInterpolationData` is exactly measurability of
`ω ↦ I ω r` at each fixed `r`. -/
theorem oneClockInterpolationData_of_eval_measurable (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (start : Vertex e.val)
    (X : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (Z : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (I : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (hI : ∀ r : ℝ≥0, Measurable fun ω => I ω r)
    (hpath : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      RegularSpatialExtension (decode e) (z.at e) (fun t => X t ω) (fun t => Z t ω) ∧
      IsContinuousInterpolation (decode e) (z.at e) (fun t => X t ω)
        (fun t => Z t ω) (I ω)) :
    OneClockInterpolationData e D hG z start X :=
  ⟨Z, I, ContinuousMap.measurable_iff_eval.2 hI, hpath⟩

/-- **`RepresentativeInterpolationData` from four pathwise objects with measurable
evaluations.**  The smallest honest input this file leaves: two extensions, two
interpolations, the pathwise clauses almost surely, and time-evaluation measurability. -/
theorem representativeInterpolationData_of_eval_measurable (e : Env)
    [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2)
    (hIexp : ∀ r : ℝ≥0, Measurable fun ω => Iexp ω r)
    (hIexact : ∀ r : ℝ≥0, Measurable fun ω => Iexact ω r)
    (hexp : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      RegularSpatialExtension (decode e) (z.at e) (fun t => Xexp t ω)
        (fun t => Zexp t ω) ∧
      IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexp t ω)
        (fun t => Zexp t ω) (Iexp ω))
    (hexact : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      RegularSpatialExtension (decode e) (z.at e) (fun t => Xexact t ω)
        (fun t => Zexact t ω) ∧
      IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexact t ω)
        (fun t => Zexact t ω) (Iexact ω)) :
    RepresentativeInterpolationData e D hG z start Xexp Xexact :=
  representativeInterpolationData_of_clocks e D hG z start Xexp Xexact
    (oneClockInterpolationData_of_eval_measurable e D hG z start Xexp Zexp Iexp hIexp hexp)
    (oneClockInterpolationData_of_eval_measurable e D hG z start Xexact Zexact Iexact
      hIexact hexact)

/-! ## The datum is canonical -/

end ReflectedGMS.RepresentativeInterpolationReduction
