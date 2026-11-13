/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.InvarianceMainStatement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.HarmonicMainStatement
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClocks
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialEnds
import LatticeProb.Bonanno.ReflectedGMS.Process.MartingaleIngredients
import LatticeProb.Bonanno.ReflectedGMS.Process.QuenchedLimit
import LatticeProb.Bonanno.ReflectedGMS.Process.NaturalFiltration
import Mathlib.Util.AssertNoSorry

/-!
The reflected invariance-principle target, manuscript Theorem `p:thm:whole`.
This file defines the proposition; it does not prove the theorem. It uses the
actual constructed ReflectedWalk sample and process for both clocks. All
harmonic coordinates, exhaustions, process regularity, bracket and Brownian
limit assertions occur in the conclusion, with only the manuscript's random
environment assumptions on the input side.

The canonical version is identified by its existing explicit construction.
Its full reflected-form/Hunt identification remains a proof obligation; no
free realization predicate is assumed or asserted to have been proved here.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.InvarianceMainStatement
open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration

/-- Full physical covariance of a chosen measurable representative rule. -/
def RepresentativeCovariant (z : CellField) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (relabel : Vertex e.val ≃ Vertex e'.val),
    IsSimilarityRelabel s u hs e e' relabel → ∀ v,
      z.at e' (relabel v) = positiveSimilarity s u (z.at e v)

/-- Reuse the existing encoding of an optional active vertex. Its injectivity
retains exactly the information of the collapsed path in a discrete codomain. -/
def observedState (e : Env) : Option (Vertex e.val) → ℕ := Encodable.encode

theorem observedState_injective (e : Env) : Function.Injective (observedState e) :=
  Encodable.encode_injective

/-- The natural completed filtration of the actual exponential area-clock path. -/
noncomputable def areaFiltration (e : Env) (D : (decode e).graph.Exhaustion)
    (P : Measure (Existence.Sample (Vertex e.val))) :=
  completedNaturalFiltration P
    (fun t ω => observedState e (exponentialAreaPath (decode e) D t ω))
    (fun t => (measurable_of_countable (observedState e)).comp
      (measurable_exponentialAreaPath (decode e) D t))

/-- The complete bracket assertion in the completed natural filtration. The
same harmonic coordinate is evaluated at every vertex and extended at all
reflection times; the density at those times is zero by the shared definition. -/
def CanonicalBracket (e : Env) (D : (decode e).graph.Exhaustion)
    (Φ : CellField) (P : Measure (Existence.Sample (Vertex e.val)))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane) : Prop :=
  HasOrdinaryEdgeBracket (Ω := NullMeasurableSpace (Existence.Sample (Vertex e.val)) P)
    (decode e) (Φ.at e) P.completion (areaFiltration e D P)
    (exponentialAreaPath (decode e) D) M

/-- Unique pathwise spatial extension, with all-time local boundedness and
only ordinary-edge jumps. This uses actual end labels, without asserting any
fixed deterministic spatial image for an abstract graph end. -/
def RegularSpatialExtension {V : Type*} (F : IndexedCells V) (z : V → Plane)
    (X : ℝ≥0 → State F) (Z : ℝ≥0 → Plane) : Prop :=
  IsSpatialExtension F z X Z ∧
  (∀ W : ℝ≥0 → Plane, IsSpatialExtension F z X W → W = Z) ∧
  LocallySpatiallyBounded Z ∧ HasOnlyOrdinaryJumps F z X Z

/-- Both laws are actual pushforwards of the same canonical sample law through
measurable continuous interpolations. The environment and starting vertex are
fixed before the positive-side scale limit. -/
def InterpolatedTwoClockLimit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (target : AnisotropicBrownianTarget)
    (Zexp Zexact : Ω → BouRabeeGwynne.BrownianPath 2) : Prop :=
  Measurable Zexp ∧ Measurable Zexact ∧
  TwoClockQuenchedWeakLimitAtFixedStart
    (fun (_ : Unit) (_ : Unit) => P.toProbabilityMeasure.map Zexp)
    (fun (_ : Unit) (_ : Unit) => P.toProbabilityMeasure.map Zexact)
    target () ()

/-- Clauses (b), (d), and (e) for one representative rule, from one fixed start.
The interpolations are constrained over the actual complete preceding holding
intervals and at reflection times, then their actual laws have the same target. -/
def RepresentativePathConclusions (e : Env) (z : CellField)
    (P : Measure (Existence.Sample (Vertex e.val))) [IsProbabilityMeasure P]
    (target : AnisotropicBrownianTarget)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e)) : Prop :=
  ∃ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
    (∀ᵐ ω ∂P,
      RegularSpatialExtension (decode e) (z.at e) (fun t => Xexp t ω)
        (fun t => Zexp t ω) ∧
      RegularSpatialExtension (decode e) (z.at e) (fun t => Xexact t ω)
        (fun t => Zexact t ω) ∧
      IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexp t ω)
        (fun t => Zexp t ω) (Iexp ω) ∧
      IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexact t ω)
        (fun t => Zexact t ω) (Iexact ω)) ∧
    InterpolatedTwoClockLimit P target Iexp Iexact

/-- All pathwise and martingale conclusions under the actual canonical law
from one fixed starting vertex. The exact and exponential paths retain the
same coupled chains by definition. Their time-change homeomorphisms act on
the entire half-line, so neither clock has a finite terminal lifetime. -/
def FixedStartConclusions (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (target : AnisotropicBrownianTarget) (start : Vertex e.val) : Prop :=
  let P := areaSampleLaw (decode e) D hG start
  ∃ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
    (∀ᵐ ω ∂P,
      (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
      (∀ t, collapse (Xexact t ω) = exactAreaPath (decode e) D t ω) ∧
      IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
      IsEndLabeling (decode e) (fun t => Xexact t ω) ∧
      AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω) ∧
      AvoidsSpatialInfinity (decode e) (fun t => Xexact t ω) ∧
      IsHomeomorphicTimeChange (fun t => exponentialAreaPath (decode e) D t ω)
        (fun t => canonicalFastPath (decode e) D hG t ω) ∧
      IsHomeomorphicTimeChange (fun t => exactAreaPath (decode e) D t ω)
        (fun t => exponentialAreaPath (decode e) D t ω) ∧
      (∀ v w s t, IsHoldingInterval (decode e) (fun t => Xexact t ω) v w s t →
        (t : ℝ) - s = areaHoldingLength (decode e) v) ∧
      RegularSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω)
        (fun t => M t ω)) ∧
    ReturnsToEveryVertex P (exponentialAreaPath (decode e) D) ∧
    ReturnsToEveryVertex P (exactAreaPath (decode e) D) ∧
    CanonicalBracket e D Φ P M ∧
    ∀ z : CellField, IsCellRepresentative z →
      RepresentativePathConclusions e z P target Xexp Xexact

/-- The canonical construction has both the area-clock and admissible
fast-clock reflected-walk properties, with the actual full finite-energy
finite-target minimizer data. These are conclusions, not environmental inputs.
The exhaustion `D` is existential, matching the manuscript's "an admissible fast clock"; the
law-level conclusions do not depend on it, since `IsReflectedWalk` determines the law at every
positive rate (Gwynne–Sung Theorem 1.6 uniqueness in the sibling `ReflectedWalk` tree; fidelity
audit 2026-09-18, I2). -/
def EnvironmentProcessConclusions (e : Env) (Φ : CellField)
    (target : AnisotropicBrownianTarget) : Prop :=
  ∃ hnt : Nontrivial (Vertex e.val),
    letI := hnt
    ∃ (D : (decode e).graph.Exhaustion)
      (hG : (decode e).graph.toSimpleGraph.Connected)
      (hmin : (decode e).graph.EnergyMinimizer),
      (∀ v, 0 < areaRate (decode e) v) ∧
      IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
        (Existence.processFamily D hG (areaRate (decode e))) ∧
      IsReflectedWalk (decode e).graph (D.rateFunction hG) hmin
        (Existence.processFamily D hG (D.rateFunction hG)) ∧
      ∀ start : Vertex e.val, FixedStartConclusions e D hG Φ target start

/-- One measurable unmarked harmonic coordinate and one deterministic genuine
Brownian target serve almost every environment, every fixed start, both clocks
and every measurable cell representative rule. Entrywise integrability prevents
the mean covariance integral from silently taking a default zero value. -/
def ReflectedInvarianceConclusions (ν : Measure Env) : Prop :=
  ∃ (Φ : CellField) (target : AnisotropicBrownianTarget),
    IsHarmonicCoordinate ν Φ ∧
    IntegrableBracket ν Φ ∧
    target.covariance = meanCovariance ν Φ ∧
    (∃ z : CellField, IsCellRepresentative z ∧ RepresentativeCovariant z) ∧
    ∀ᵐ e : Env ∂ν, EnvironmentProcessConclusions e Φ target

/-- The complete main process target: validity, full trace-measurable mass
transport, FE and environment-only similarity ergodicity imply (a)--(e).
No corrector, martingale, bracket law of large numbers or invariance principle
is present as an additional input assumption. This declaration states a
proposition and does not assert that it has been proved. -/
def ReflectedInvarianceMainTheorem : Prop :=
  ∀ (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValid P),
    AmbientMassTransport P hP →
    FiniteEnergyMoment (validLaw P hP) →
    AmbientEnvironmentErgodic P hP →
    ReflectedInvarianceConclusions (validLaw P hP)

end ReflectedGMS.InvarianceMainStatement

assert_no_sorry ReflectedGMS.InvarianceMainStatement.observedState_injective
assert_no_sorry ReflectedGMS.InvarianceMainStatement.ReflectedInvarianceMainTheorem
#print axioms ReflectedGMS.InvarianceMainStatement.observedState_injective
#print axioms ReflectedGMS.InvarianceMainStatement.ReflectedInvarianceMainTheorem
