/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.HlimitAssemblyAtoms at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssemblyFourInputs
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizedBracketRegularity
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialCutoffEnvironment
import LatticeProb.Bonanno.ReflectedGMS.Corrector.HarmonicCoordinateFiveInputs
import LatticeProb.Bonanno.ReflectedGMS.Corrector.HarmonicCoordinateThreeInputs
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BlockInterpolantSelectionCandidate
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketClausesScalarReduction
import LatticeProb.Bonanno.ReflectedGMS.Limit.CanonicalOccupationDischarge
import LatticeProb.Bonanno.ReflectedGMS.Forms.NonvertexContinuityEnvironment
import LatticeProb.Bonanno.ReflectedGMS.Limit.TwoClockLiftEnvironment
import LatticeProb.Bonanno.ReflectedGMS.Limit.ExactClockModulus

/-!
# `hlimit` as an exact list of open atoms

`Limit/HlimitAssembly` puts `LocalBracketMainTheoremsWeld.UniformAreaClockLimit` at two
inputs: the construction half and the analytic half.  `Limit/TwoClockLiftEnvironment` reduces
the analytic half to four per-environment atoms, and `Limit/ExactClockModulus` fills the two
window-modulus atoms from the localized martingale arrays plus the clock-equivalence input.

This file composes all of that, and discharges the three remaining *geometric* side
conditions of the modulus route from hypotheses the invariance assembly already has:

* `SubmacroscopicDiameters (decode e)` — `InvarianceAssembly.ae_submacroscopicDiameters`
  from `hmt`, `hFE`;
* `SublinearDiameterDecay (decode e)` — `Spatial.ae_maxDiamHittingBall_finite_and_sublinear`
  from `hmt`, `hFE`;
* `UniformlySublinearError (decode e) (Φ.at e) (z.at e)` —
  `HarmonicCoordinateAssembly.uniformlySublinearError_of_representatives` from the previous
  one, the geometry of `decode e`, the `SublinearCorrector` clause of `IsHarmonicCoordinate`,
  and the representative clause.  So the *representative-dependent* sublinearity is free, and
  in particular the packet below does not have to be asked uniformly in `z` by hand.

## The resulting cost of `hlimit`, exactly

`UniformAreaClockLimit ν` follows from precisely two things:

1. `HlimitAssembly.UniformRepresentativeInterpolationData ν` — the construction half
   (`Limit/RepresentativeInterpolationReduction` splits it by clock, shows its witnesses are
   canonical, and reduces the path-space measurability to the time evaluations);
2. `UniformAnalyticPacket ν` — per environment, per admissible datum, four things:
   * the localized martingale arrays for the rescaled harmonic extension (`harray`, the
     bracket-LLN lane);
   * `ExactClockModulus.ClockCrossClosenessSlot` (the clock equivalence `p:eq:clockequiv`);
   * `TwoClockLiftEnvironment.GaussSlotExp` and `GaussSlotExact` (the two identification
     atoms, which `Limit/RescaledFddCharFunReduction` reduces to the conditional increment
     CLT).

**Nothing here certifies any of those.**  Every theorem is an implication.
-/

-- Merged from `ReflectedGMS/Limit/HlimitAssembly.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_HlimitAssembly

/-!
# `UniformAreaClockLimit` reduced to the two halves of `hlimit`

`LocalBracketMainTheoremsWeld.UniformAreaClockLimit ν` is the `hlimit` binder of the two
frontier welds (`ScalarBracketMainTheoremsWeld` and its `validLaw` variant).  It had **zero
producers**: nothing in the tree concluded it, and it had not been reduced one step.

Unfolded, `UniformAreaClockLimit ν` asks for `hlimit` *uniformly in the harmonic
coordinate*.  Everything beyond the per-environment analytic statement
`InterpolatedTwoClockReduction.TwoClockScalingLimit` is therefore exactly three things:

1. the **construction half** `RepresentativeInterpolationData` — the two spatial extensions
   and the two continuous interpolations exist, satisfy the pathwise clauses a.s., and are
   measurable into the path space;
2. the **almost-every-environment gating**, supplied by
   `Limit/TwoClockLiftEnvironment`;
3. the **`∀ Φ, IsHarmonicCoordinate ν Φ →` prefix**, which is free: the harmonic coordinate
   is an output of the harmonic main theorem, not an input of the weld, so both halves must
   be asked at every harmonic field.  That prefix is the only thing this file adds.

So `UniformAreaClockLimit` costs nothing beyond `UniformRepresentativeInterpolationData` and
`UniformTwoClockScalingLimit`, and the latter is discharged by the four analytic atoms of
`TwoClockLiftEnvironment.AeGaussianClockLimitAtoms` at any fixed scale set that is a
neighbourhood of `0` within the positive scales.

The last two theorems restate the two frontier heads with `hlimit` replaced by these halves;
they are pure applications and discharge nothing.
-/

-- Merged from `ReflectedGMS/ScalarBracketMainTheoremsWeld.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ScalarBracketMainTheoremsWeld

/-!
# The cross-theorem weld at the current frontier

`LocalBracketMainTheoremsWeld.reflectedInvarianceConclusions_of_harmonic_inputs_and_local_atoms`
is the project's only two-theorem composition, and it is **three discharges behind** the corpus:

1. it consumes the *five*-input harmonic head, although `hmax`, `hsub` and `hcopies` have since
   been produced (`Corrector/HarmonicCoordinateThreeInputs`) and `hmeas` outright discharged
   (`Corrector/HarmonicCoordinateTwoInputs`);
2. it consumes the *pre-scalar* `hlocal`, although bracket clauses one and five have since been
   reduced to the scalar diagonal atoms of `Limit/BracketClausesScalarReduction`;
3. its `hlocal` still carries `CanonicalOccupationLocallyFinite`, although
   `Limit/CanonicalOccupationDischarge.ae_canonicalOccupationLocallyFinite` **discharges** that
   atom from `hmt`, `hFE` and `hΦ` — i.e. at no cost at all inside this weld, because the
   harmonic coordinate `Φ` produced here comes with its `hΦ`.

This file redoes the weld against all three, so that one checked statement carries the frontier.

⚠ The *statement* of the previous weld is not merely superseded in count: its `hmaxd`, `hcopies`
and `hsubl` binders are now theorems, and its `hlocal` binder is strictly stronger than what is
asked here.  Nothing below weakens any conclusion.

## DISCHARGED vs REDUCED, stated exactly

* **DISCHARGED here, relative to the previous weld**: `CanonicalOccupationLocallyFinite`.  It was
  the first conjunct of the previous weld's bracket binder and it is gone, paid for by `hΦ`
  through `CanonicalOccupationDischarge.ae_canonicalOccupationLocallyFinite` — a genuine
  discharge, not a reduction: no new hypothesis replaces it.  Likewise `hcut` (the spatial-cutoff
  half of `hreg`) and, inside the harmonic lane, `hmax`, `hsub` and the marked-space producer of
  `hcopies`.
* **REDUCED, not discharged**: bracket clauses one and five, which are now asked in their scalar
  diagonal form (`CoordinateLocallySquareIntegrable`, `DiagonalCompensatedSquares`) rather than
  the plane-valued/cross form — the same mathematical content in the vocabulary every `Forms/`
  square-compensation producer speaks; and `hcopies`, reduced to `hzero`.
* **Unchanged**: `hlimit` is the previous weld's binder *verbatim* — it is literally
  `LocalBracketMainTheoremsWeld.UniformAreaClockLimit`, imported rather than restated, so it
  cannot have drifted.

⚠ The `hcont` discharged here is the project's nonvertex-continuity atom (the nonvertex half of
`p:prop:purejump`).  It is **not** the `hcont` of `Limit/CompactContainmentProducer`, which is
compact containment; the two are unrelated, and the latter is untouched by any of this.

## Honest count: **four** named open inputs

| input | lane | content |
|---|---|---|
| `hproj`   | harmonic | `SpecificEnergyConvergence.MarkedNestedProjectionBound ν` |
| `hzero`   | harmonic | cross orthogonality, `ℝ≥0∞` form — the irreducible content of `hcopies` |
| `hscalar` | process  | the two scalar bracket atoms |
| `hlimit`  | process  | the area-clock FCLT `p:thm:areaclt` and its construction half |

Against the previous weld's eight (`hmeas, hproj, hmaxd, hcopies, hsubl, hcont, hlocal, hlimit`).

Two of the four that disappeared are **DISCHARGED outright**, not reduced:

* `hmeas`, with no hypotheses at all, by
  `Corrector/BlockInterpolantSelectionCandidate.measurable_gatedApproximant`, applied inside
  `Corrector/HarmonicCoordinateTwoInputs`;
* `hcont` — the nonvertex half of `p:prop:purejump` — by
  `Forms/NonvertexContinuityEnvironment.ae_hcont_of_cutoffs` from the *same* `hcut` that
  `Process/SpatialCutoffEnvironment.ae_hasSpatialCutoffs_of_isHarmonicCoordinate` already derives
  from `hΦ`.  So the whole `hreg` binder — both halves — now costs nothing beyond the harmonic
  coordinate this weld produces for itself.

## The standing caveat is inherited, not introduced

`HarmonicCoordinateConclusions ν` is an existential, so the coordinate the harmonic lane produces
is not available to the statement, and the three process-lane atoms must be asked **uniformly in
`Φ`**.  That is a genuine strengthening relative to asking them at a single `Φ` fixed in advance,
exactly as in the previous weld; the total here is therefore better organised and strictly fewer
inputs, but it is not a claim that the two lanes together are cheaper than the lanes apart.

**This file proves no main theorem.**  All six named inputs are open; every statement is an
implication and certifies none of them.
-/

-- Merged from `ReflectedGMS/LocalBracketMainTheoremsWeld.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_LocalBracketMainTheoremsWeld

/-!
# The cross-theorem weld, rebuilt against the localized bracket head

`MainTheoremsWeld.reflectedInvarianceConclusions_of_harmonic_inputs_and_three_atoms` welded the
two main theorems together against the *old* bracket head: it asked for the full canonical
bracket identification `hbracket` as one of its three process-lane atoms.  Since then
`Limit/LocalBracketInvarianceWeld.reflectedInvarianceConclusions_of_local_bracket_inputs` replaced
that binder by the strictly weaker `hlocal`, because
`Limit/LocalizedBracketRegularity.hbracket_of_ae_local_inputs` discharges the càdlàg clause, the
interval-integrability clause, the occupation identification and the pathwise regularity of the
bracket from `LocalizedBracketOccupation.CanonicalOccupationLocallyFinite` alone.

This file redoes the weld against **that** head, so the project's single top-level statement
carries the current frontier rather than a superseded one.

## What is composed

* `hΦ` — eliminated by `Exists.elim` on
  `Corrector/HarmonicCoordinateFiveInputs.harmonicCoordinateConclusions_of_five_inputs`, at the
  price of importing that theorem's five open inputs;
* `hcut` — the spatial-cutoff half of the `hreg` binder, supplied by
  `Process/SpatialCutoffEnvironment.ae_hasSpatialCutoffs_of_isHarmonicCoordinate` from the very
  same `IsHarmonicCoordinate ν Φ` that the harmonic theorem produced, and combined with the
  nonvertex-continuity atom by `SpatialExtensionConstruction.ae_hreg_of_cutoffs_and_continuity`;
* the bracket slot — not asked for at all: it is `hlocal`'s job inside
  `LocalBracketInvarianceWeld.reflectedInvarianceConclusions_of_local_bracket_inputs`.

## Honest count: eight named open inputs (five plus three), no new discharge

Besides the environment hypotheses `hmt : MassTransport ν` and `hFE : FiniteEnergyMoment ν`, the
theorem takes

| input | lane | manuscript |
|---|---|---|
| `hmeas`  | harmonic | measurability of the gated approximants |
| `hproj`  | harmonic | `SpecificEnergyConvergence.MarkedNestedProjectionBound` |
| `hmaxd`  | harmonic | `StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal` |
| `hcopies`| harmonic | `DifferenceFieldGridIndependent`, uniform in the subsequence |
| `hsubl`  | harmonic | `MarkedCentroidSublinearity`, uniform in the subsequence |
| `hcont`  | process  | nonvertex half of `p:prop:purejump` |
| `hlocal` | process  | local occupation finiteness + local square integrability of `M` + the
                       compensated products being local martingales |
| `hlimit` | process  | the area-clock FCLT `p:thm:areaclt` and its construction half |

**This composition discharges nothing that was not already discharged.**  The count is the same
eight as in `MainTheoremsWeld`; what changed is the *strength* of the third process atom, and that
change was made upstream, in `LocalizedBracketRegularity`/`LocalBracketInvarianceWeld`, not here.
Relative to `MainTheoremsWeld` this file is weaker in its hypotheses (`hlocal` implies the old
`hbracket`, by `hbracket_of_ae_local_inputs`; the converse is not available) and identical in its
conclusion — the cross-check `example` below proves exactly that by re-deriving the same
conclusion through the old weld.  Relative to `LocalBracketInvarianceWeld` it trades that
theorem's `hΦ` and the cutoff half of its `hreg` for the harmonic theorem's five inputs.  No new
mathematics: this is a restatement of the frontier in one place, which is the point, and it must
not be read as a discharge.

## The standing caveat: `Φ` is an output, so the atoms are asked for every harmonic `Φ`

`HarmonicCoordinateConclusions ν` is an existential, so the coordinate that the harmonic lane
produces is not available to the statement.  The three process-lane atoms must therefore be asked
**uniformly in `Φ`**, for every field satisfying `IsHarmonicCoordinate ν Φ` — see
`UniformNonvertexContinuity`, `UniformLocalBracketClauses`, `UniformAreaClockLimit` below.  That
is a genuine strengthening relative to asking them at a single `Φ` fixed in advance, as the
two-lane bookkeeping does.  **So the total here is not strictly better than keeping the two lanes
separate**; it is better organized, and it is honest about the overlap the separate bookkeeping
hides.  (The same phenomenon occurs one level down, with `hcopies`/`hsubl` asked uniformly in the
subsequence `ms` inside the five-input harmonic theorem.)

**This file proves no main theorem.**  All eight named inputs are open.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

namespace ReflectedGMS.LocalBracketMainTheoremsWeld

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.SpatialExtensionConstruction
open ReflectedGMS.LocalizedBracketOccupation ReflectedGMS.LocalizedBracketRegularity

/-- The area-clock FCLT `p:thm:areaclt` together with its construction half, asked uniformly in
the harmonic coordinate.  Verbatim the `hlimit` binder of both existing welds. -/
def UniformAreaClockLimit (ν : Measure Env) : Prop :=
  ∀ Φ : CellField, IsHarmonicCoordinate ν Φ →
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M →
            ∀ target : AnisotropicBrownianTarget,
              target.covariance = meanCovariance ν Φ →
              ∀ z : CellField, IsCellRepresentative z →
                RepresentativePathConclusions e z
                  (areaSampleLaw (decode e) D hG ⟨n, hn⟩) target Xexp Xexact

end ReflectedGMS.LocalBracketMainTheoremsWeld

end Merged_LocalBracketMainTheoremsWeld

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

namespace ReflectedGMS.ScalarBracketMainTheoremsWeld

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.SpatialExtensionConstruction
open ReflectedGMS.LocalizedBracketOccupation ReflectedGMS.LocalizedBracketRegularity
open ReflectedGMS.BracketClausesScalarReduction
open ReflectedGMS.LocalBracketMainTheoremsWeld

/-- The remaining bracket debt in its **scalar diagonal** form — each real coordinate of the
harmonic path is a locally square-integrable martingale, and the diagonal compensated squares of
the coordinates and their sums are local martingales — asked uniformly in the harmonic
coordinate.

This is verbatim the `hlocal` binder of
`Limit/BracketClausesScalarReduction.reflectedInvarianceConclusions_of_scalar_bracket_inputs`
with its `CanonicalOccupationLocallyFinite` conjunct **deleted** and a
`∀ Φ, IsHarmonicCoordinate ν Φ →` prefix in place of that theorem's fixed `Φ`.  The deleted
conjunct is paid for by `hΦ` inside the weld below. -/
def UniformScalarBracketClauses (ν : Measure Env) : Prop :=
  ∀ Φ : CellField, IsHarmonicCoordinate ν Φ →
    ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∀ (start : Vertex e.val)
          (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
          (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
          PathwiseClockClauses e D hG Φ start Xexp Xexact M →
          CoordinateLocallySquareIntegrable e D hG start M ∧
          DiagonalCompensatedSquares e D hG Φ start M

end ReflectedGMS.ScalarBracketMainTheoremsWeld

end Merged_ScalarBracketMainTheoremsWeld

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.HlimitAssembly

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.InterpolatedTwoClockReduction
open ReflectedGMS.TwoClockLiftEnvironment
open ReflectedGMS.LocalBracketMainTheoremsWeld
open ReflectedGMS.ScalarBracketMainTheoremsWeld

/-! ## The two halves, asked uniformly in the harmonic coordinate -/

/-- The construction half of `hlimit`, asked at every harmonic coordinate.  This is the
`∀ Φ, IsHarmonicCoordinate ν Φ →` closure of
`TwoClockLiftEnvironment.AeRepresentativeInterpolationData`. -/
def UniformRepresentativeInterpolationData (ν : Measure Env) : Prop :=
  ∀ Φ : CellField, IsHarmonicCoordinate ν Φ → AeRepresentativeInterpolationData ν Φ

/-- The analytic half of `hlimit` (`p:thm:areaclt`), asked at every harmonic coordinate. -/
def UniformTwoClockScalingLimit (ν : Measure Env) : Prop :=
  ∀ Φ : CellField, IsHarmonicCoordinate ν Φ → AeTwoClockScalingLimit ν Φ

/-- The four analytic atoms in their Gaussian form, asked at every harmonic coordinate and
at a fixed scale set. -/
def UniformGaussianClockLimitAtoms (ν : Measure Env) (T : Set ℝ≥0) : Prop :=
  ∀ Φ : CellField, IsHarmonicCoordinate ν Φ → AeGaussianClockLimitAtoms ν Φ T

/-! ## `UniformAreaClockLimit`, produced -/

/-- **The first producer of `LocalBracketMainTheoremsWeld.UniformAreaClockLimit`.**

CONDITIONAL on the two halves; this certifies neither of them, nor `p:thm:areaclt`, nor
either main theorem.  It is a pure application of
`InterpolatedTwoClockReduction.hlimit_of_ae_interpolation_data_of_scaling_limit` under the
`∀ Φ, IsHarmonicCoordinate ν Φ →` prefix, so it establishes that the prefix is the *only*
thing `UniformAreaClockLimit` asks beyond the two halves. -/
theorem uniformAreaClockLimit_of_halves (ν : Measure Env)
    (hdata : UniformRepresentativeInterpolationData ν)
    (hlaw : UniformTwoClockScalingLimit ν) :
    UniformAreaClockLimit ν :=
  fun Φ hΦ => hlimit_of_ae_halves ν Φ (hdata Φ hΦ) (hlaw Φ hΦ)

/-- `UniformTwoClockScalingLimit` from the four analytic atoms in their Gaussian form. -/
theorem uniformTwoClockScalingLimit_of_uniformGaussianAtoms (ν : Measure Env)
    (T : Set ℝ≥0) (hT : T ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
    (h : UniformGaussianClockLimitAtoms ν T) :
    UniformTwoClockScalingLimit ν :=
  fun Φ hΦ => aeTwoClockScalingLimit_of_aeGaussianClockLimitAtoms ν Φ T hT (h Φ hΦ)

/-- **`UniformAreaClockLimit` from the construction half and the four Gaussian atoms.**
The fully reduced form: `hlimit` costs exactly the construction of the interpolations plus
the two window-modulus tails and the two Gaussian identifications. -/
theorem uniformAreaClockLimit_of_data_and_gaussian_atoms (ν : Measure Env)
    (T : Set ℝ≥0) (hT : T ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
    (hdata : UniformRepresentativeInterpolationData ν)
    (hatoms : UniformGaussianClockLimitAtoms ν T) :
    UniformAreaClockLimit ν :=
  uniformAreaClockLimit_of_halves ν hdata
    (uniformTwoClockScalingLimit_of_uniformGaussianAtoms ν T hT hatoms)

/-! ## The frontier welds with `hlimit` replaced by its two halves -/

end ReflectedGMS.HlimitAssembly

end Merged_HlimitAssembly

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.HlimitAssemblyAtoms

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.DirectionalNondegeneracy
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.InterpolatedTwoClockReduction
open ReflectedGMS.MartingaleLimit
open ReflectedGMS.WindowModulusGridTransfer
open ReflectedGMS.TwoClockScalingLimitReduction
open ReflectedGMS.WindowModulusUniformScales
open ReflectedGMS.TwoClockLiftEnvironment
open ReflectedGMS.ExactClockModulus
open ReflectedGMS.HlimitAssembly
open ReflectedGMS.LocalBracketMainTheoremsWeld
open ReflectedGMS.ScalarBracketMainTheoremsWeld

/-! ## The analytic packet -/

/-- **The four open analytic atoms of the `hlimit` lane, gated to almost every
environment.**

Per environment, per exhaustion, per start, per admissible pair of lifts and harmonic
extension, per target and per representative rule: the localized martingale arrays for the
rescaled harmonic extension, the clock-equivalence closeness of the two interpolations, and
the Gaussian identification at every sequential limit point of each rescaled interpolation
law. -/
def AeAnalyticPacket (ν : Measure Env) (Φ : CellField) : Prop :=
  ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
    letI := hnt
    ∀ (D : (decode e).graph.Exhaustion)
      (hG : (decode e).graph.toSimpleGraph.Connected),
      EnvironmentWalkData e D hG →
      ∀ (start : Vertex e.val)
        (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
        (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
        PathwiseClockClauses e D hG Φ start Xexp Xexact M →
        ∀ target : AnisotropicBrownianTarget,
          target.covariance = meanCovariance ν Φ →
          ∀ z : CellField, IsCellRepresentative z →
            (∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
              ∀ (k : Fin 2) (H : ℝ≥0),
                Nonempty (LocalizedMartingaleArray (areaSampleLaw (decode e) D hG start)
                  (fun n u ω => (ε n : ℝ) * M ((ε n)⁻¹ ^ 2 * u) ω k) H)) ∧
            ClockCrossClosenessSlot e D hG z start Xexp Xexact ∧
            GaussSlotExp e D hG z target start Xexp Xexact ∧
            GaussSlotExact e D hG z target start Xexp Xexact

/-- The analytic packet asked at every harmonic coordinate. -/
def UniformAnalyticPacket (ν : Measure Env) : Prop :=
  ∀ Φ : CellField, IsHarmonicCoordinate ν Φ → AeAnalyticPacket ν Φ

/-! ## The geometric side conditions are free -/

/-- **`AeGaussianClockLimitAtoms` from the analytic packet.**

The three geometric side conditions of the modulus route — submacroscopic diameters,
sublinear diameter decay, and representative-dependent sublinearity of the corrector error —
are supplied here from `hmt`, `hFE` and the `SublinearCorrector` clause of
`IsHarmonicCoordinate`, so they cost nothing beyond what the invariance assembly already
has.  CONDITIONAL on the packet; certifies none of its four atoms. -/
theorem aeGaussianClockLimitAtoms_of_packet (ν : Measure Env)
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hΦ : IsHarmonicCoordinate ν Φ) (h : AeAnalyticPacket ν Φ) :
    AeGaussianClockLimitAtoms ν Φ (Set.Ioc 0 1) := by
  filter_upwards [h, ae_submacroscopicDiameters ν hmt hFE,
    Spatial.ae_maxDiamHittingBall_finite_and_sublinear ν hmt hFE.ne, hΦ.2.2.2.2.1]
    with e hp hdiam hdec hcorr
  intro hnt D hG hdat start Xexp Xexact M hclock target hcov z hz
  have : Nontrivial (Vertex e.val) := hnt
  obtain ⟨harray, hcross, hg1, hg2⟩ :=
    hp hnt D hG hdat start Xexp Xexact M hclock target hcov z hz
  have hsubErr : UniformlySublinearError (decode e) (Φ.at e) (z.at e) :=
    HarmonicCoordinateAssembly.uniformlySublinearError_of_representatives (decode e)
      (decode_geometry e) hdec.2.1 hcorr.2.2.2.2.1 (fun v => hz e v)
  exact gaussianClockLimitAtoms_of_arrays_and_crossCloseness e D hG z Φ target start Xexp
    Xexact M hdat hclock hz hsubErr hdiam hcross harray hg1 hg2

/-! ## `UniformAreaClockLimit` at two inputs -/

/-- **`LocalBracketMainTheoremsWeld.UniformAreaClockLimit` from exactly two inputs**: the
construction half, and the four-atom analytic packet.

This is the exact statement of what `hlimit` costs.  CONDITIONAL on both; nothing here
certifies either, nor `p:thm:areaclt`, nor either main theorem. -/
theorem uniformAreaClockLimit_of_data_and_packet (ν : Measure Env)
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hdata : UniformRepresentativeInterpolationData ν)
    (hpacket : UniformAnalyticPacket ν) :
    UniformAreaClockLimit ν :=
  uniformAreaClockLimit_of_data_and_gaussian_atoms ν (Set.Ioc 0 1)
    Ioc_zero_one_mem_nhdsWithin hdata
    (fun Φ hΦ => aeGaussianClockLimitAtoms_of_packet ν hmt hFE Φ hΦ (hpacket Φ hΦ))

/-! ## The frontier welds, with `hlimit` fully opened -/

end ReflectedGMS.HlimitAssemblyAtoms
