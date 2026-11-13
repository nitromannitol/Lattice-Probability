/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.InterpolatedTwoClockReduction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssembly

/-!
# The `hlimit` input of the invariance assembly, split into its two halves

`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs` (and its
recurrence-free form `InvarianceAssemblyNoReturn`) carries an input `hlimit`
whose conclusion is
`InvarianceMainStatement.RepresentativePathConclusions e z P target Xexp Xexact`,
i.e. clauses (b), (d) and (e) of manuscript Theorem `p:thm:whole` for one
measurable cell-representative rule from one fixed start.

That conclusion is an existential over four objects — the two pathwise spatial
extensions `Zexp`, `Zexact` of the representative rule and the two continuous
interpolations `Iexp`, `Iexact` — followed by *two* logically independent
assertions about them: an almost-sure **pathwise** assertion (the extensions are
regular and the interpolations are the linear interpolations over the complete
holding intervals) and an **analytic** assertion (the two rescaled path laws
converge weakly to the same anisotropic Brownian target).  Carrying them as a
single input hides the fact that they belong to two different lanes of the
project.

This file splits them:

* `RepresentativeInterpolationData` — the construction half.  It is the
  existence of `Zexp`, `Zexact`, `Iexp`, `Iexact` with the almost-sure pathwise
  clauses and with `Iexp`, `Iexact` measurable as maps into
  `BouRabeeGwynne.BrownianPath 2`.  This is a pathwise/measurability obligation,
  of the kind `Forms/SpatialInfinityAvoidance` addresses; no scaling limit
  occurs in it.
* `TwoClockScalingLimit` — the analytic half.  For *any* measurable
  interpolations satisfying those same pathwise clauses, the two diffusively
  rescaled path laws converge to `target.pathLaw`.  This is manuscript
  `p:thm:areaclt`, the quenched invariance principle, and it is the clause the
  martingale-CLT lane (`Limit/ActualArrayBracketLimit`,
  `Limit/UnstoppedContinuousLindeberg`,
  `Limit/MultivariateBrownianIdentification`) has to produce.

Nothing here proves `hlimit`, `p:thm:areaclt` or either main theorem: the
statements below are implications whose hypotheses are open, and none of them
certifies any hypothesis.  Both halves keep every hypothesis that `hlimit` gives
its producer — the walk data, the pathwise clock clauses of the two lifts, the
covariance normalisation of the target and admissibility of the representative
rule — so their conjunction is exactly as weak as `hlimit` itself.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.InterpolatedTwoClockReduction

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly

/-! ## The two halves -/

/-- **The pathwise clauses of `RepresentativePathConclusions`**, for one fixed
choice of the two spatial extensions and the two continuous interpolations.
Copied verbatim from `InvarianceMainStatement.RepresentativePathConclusions`. -/
def PathwiseInterpolationClauses (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) →
      BouRabeeGwynne.BrownianPath 2) : Prop :=
  ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
    RegularSpatialExtension (decode e) (z.at e) (fun t => Xexp t ω)
      (fun t => Zexp t ω) ∧
    RegularSpatialExtension (decode e) (z.at e) (fun t => Xexact t ω)
      (fun t => Zexact t ω) ∧
    IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexp t ω)
      (fun t => Zexp t ω) (Iexp ω) ∧
    IsContinuousInterpolation (decode e) (z.at e) (fun t => Xexact t ω)
      (fun t => Zexact t ω) (Iexact ω)

/-- **The construction half of `hlimit`.**  The two spatial extensions of the
representative rule and the two continuous interpolations exist, satisfy the
pathwise clauses almost surely, and the interpolations are measurable as maps
into the path space `BouRabeeGwynne.BrownianPath 2`.

No scaling limit and no Brownian target occur here. -/
def RepresentativeInterpolationData (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e)) :
    Prop :=
  ∃ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) →
      BouRabeeGwynne.BrownianPath 2),
    Measurable Iexp ∧ Measurable Iexact ∧
      PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact
        Iexp Iexact

/-- **The analytic half of `hlimit`**, manuscript `p:thm:areaclt`.  For any
measurable interpolations satisfying the pathwise clauses, the two diffusively
rescaled path laws converge weakly, as the scale tends to `0` from the right, to
the path law of the prescribed anisotropic Brownian target.

The hypothesis quantifies over all admissible interpolations rather than over a
constructed one, so this half does not presuppose the construction half. -/
def TwoClockScalingLimit (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e)) :
    Prop :=
  ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) →
      BouRabeeGwynne.BrownianPath 2),
    Measurable Iexp → Measurable Iexact →
    PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact
      Iexp Iexact →
    InterpolatedTwoClockLimit (areaSampleLaw (decode e) D hG start) target
      Iexp Iexact

/-! ## Recombination -/

/-- **`RepresentativePathConclusions` from the two halves.**

CONDITIONAL on `hdata` and `hlaw`; nothing here certifies either of them, nor
`p:thm:areaclt`, nor either main theorem. -/
theorem representativePathConclusions_of_parts (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (hdata : RepresentativeInterpolationData e D hG z start Xexp Xexact)
    (hlaw : TwoClockScalingLimit e D hG z target start Xexp Xexact) :
    RepresentativePathConclusions e z (areaSampleLaw (decode e) D hG start)
      target Xexp Xexact := by
  obtain ⟨Zexp, Zexact, Iexp, Iexact, hmexp, hmexact, hpath⟩ := hdata
  exact ⟨Zexp, Zexact, Iexp, Iexact, hpath,
    hlaw Zexp Zexact Iexp Iexact hmexp hmexact hpath⟩

/-! ## The `hlimit` input -/

/-- **The `hlimit` input of the invariance assembly, split.**

CONDITIONAL on `hdata` and `hlaw`; this certifies neither of them, nor
`hlimit`, nor either main theorem.

The conclusion is, verbatim, the `hlimit` hypothesis of
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs` and of
`InvarianceAssemblyNoReturn.reflectedInvarianceConclusions_of_named_inputs_no_return`.

Both inputs keep every hypothesis that `hlimit` supplies its producer: the walk
data, the pathwise clock clauses of the two lifts (which pin `Xexp`, `Xexact` to
the two area clocks), the covariance normalisation
`target.covariance = meanCovariance ν Φ`, and admissibility of the cell
representative rule.  What the split removes is the packaging: the per-label
quantifier `∀ n, ∀ hn : (e.val.1 n).isSome` becomes a quantifier over actual
starting cells, and the single existential conclusion becomes one construction
obligation plus one weak-convergence obligation, each of which can be staffed
and checked on its own. -/
theorem hlimit_of_ae_interpolation_data_of_scaling_limit (ν : Measure Env)
    (Φ : CellField)
    (hdata : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∀ (start : Vertex e.val)
          (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
          (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
          PathwiseClockClauses e D hG Φ start Xexp Xexact M →
          ∀ z : CellField, IsCellRepresentative z →
            RepresentativeInterpolationData e D hG z start Xexp Xexact)
    (hlaw : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
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
              TwoClockScalingLimit e D hG z target start Xexp Xexact) :
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
                  (areaSampleLaw (decode e) D hG ⟨n, hn⟩) target Xexp Xexact := by
  intro n
  filter_upwards [hdata, hlaw] with e hd hl
  intro hn hnt D hG hdat Xexp Xexact M hpcc target hcov zrep hz
  have : Nontrivial (Vertex e.val) := hnt
  exact representativePathConclusions_of_parts e D hG zrep target ⟨n, hn⟩
    Xexp Xexact
    (hd hnt D hG hdat ⟨n, hn⟩ Xexp Xexact M hpcc zrep hz)
    (hl hnt D hG hdat ⟨n, hn⟩ Xexp Xexact M hpcc target hcov zrep hz)

end ReflectedGMS.InterpolatedTwoClockReduction
