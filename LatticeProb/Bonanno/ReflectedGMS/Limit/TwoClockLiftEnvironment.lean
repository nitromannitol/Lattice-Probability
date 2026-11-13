/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.TwoClockLiftEnvironment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.GaussianLimitIdentification

/-!
# Lifting the per-environment two-clock scaling limit to almost every environment

`InterpolatedTwoClockReduction.hlimit_of_ae_interpolation_data_of_scaling_limit` consumes
its two halves in an **almost-every-environment** form: a `∀ᵐ e ∂ν` statement whose body
quantifies over the exhaustion, the connectivity witness, the walk data, the start, the two
lifts, the harmonic extension, the target and the representative rule.

Every producer of `InterpolatedTwoClockReduction.TwoClockScalingLimit` in the tree is
**per environment** — one fixed `e`, one fixed `D`, one fixed start:

* `TwoClockScalingLimitReduction.twoClockScalingLimit_of_window_modulus_of_finiteDimensional`;
* `FddClusterReduction.twoClockScalingLimit_of_window_modulus_of_limit_identification`;
* `GaussianLimitIdentification.twoClockScalingLimit_of_window_modulus_of_gaussian_limits`;
* `FddBrownianWeld.twoClockScalingLimit_of_window_modulus_of_levy_limits`.

Nothing in the tree turns those into the `∀ᵐ e` shape the assembly demands.  This file is
that lift, and nothing else.

## What is here

* `AeRepresentativeInterpolationData` and `AeTwoClockScalingLimit` — names for the two
  binders of `hlimit_of_ae_interpolation_data_of_scaling_limit`, so that downstream welds
  can be written by application instead of by restating them.
* `ModulusSlotExp`, `ModulusSlotExact`, `FddSlotExp`, `FddSlotExact`, `GaussSlotExp`,
  `GaussSlotExact` — names for the six universally-quantified slots that the per-environment
  producers take, copied verbatim from those producers' binders.
* `ClockLimitAtoms` / `GaussianClockLimitAtoms` — the per-environment four-atom packages,
  and `twoClockScalingLimit_of_clockLimitAtoms` / `_of_gaussianClockLimitAtoms`, which are
  the producers repackaged.
* `AeClockLimitAtoms` / `AeGaussianClockLimitAtoms` and the two lifts
  `aeTwoClockScalingLimit_of_aeClockLimitAtoms`,
  `aeTwoClockScalingLimit_of_aeGaussianClockLimitAtoms`.

**Nothing here certifies any atom.**  Every theorem below is an implication whose hypotheses
are the four open analytic atoms, gated to almost every environment; the only content added
is the gating itself, which is exactly what was missing.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.TwoClockLiftEnvironment

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.InterpolatedTwoClockReduction
open ReflectedGMS.MartingaleLimit
open ReflectedGMS.TwoClockScalingLimitReduction
open ReflectedGMS.FddClusterReduction
open ReflectedGMS.GaussianLimitIdentification

/-! ## The two almost-every-environment halves of `hlimit` -/

/-- **The construction half of `hlimit`, gated to almost every environment.**

Copied verbatim from the `hdata` binder of
`InterpolatedTwoClockReduction.hlimit_of_ae_interpolation_data_of_scaling_limit`. -/
def AeRepresentativeInterpolationData (ν : Measure Env) (Φ : CellField) : Prop :=
  ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
    letI := hnt
    ∀ (D : (decode e).graph.Exhaustion)
      (hG : (decode e).graph.toSimpleGraph.Connected),
      EnvironmentWalkData e D hG →
      ∀ (start : Vertex e.val)
        (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
        (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
        PathwiseClockClauses e D hG Φ start Xexp Xexact M →
        ∀ z : CellField, IsCellRepresentative z →
          RepresentativeInterpolationData e D hG z start Xexp Xexact

/-- **The analytic half of `hlimit`, gated to almost every environment.**

Copied verbatim from the `hlaw` binder of
`InterpolatedTwoClockReduction.hlimit_of_ae_interpolation_data_of_scaling_limit`. -/
def AeTwoClockScalingLimit (ν : Measure Env) (Φ : CellField) : Prop :=
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
            TwoClockScalingLimit e D hG z target start Xexp Xexact

/-! ## The six per-environment slots, named -/

/-- The `hmodExp` slot of every per-environment producer, verbatim. -/
def ModulusSlotExp (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (T : Set ℝ≥0) : Prop :=
  ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
    Measurable Iexp → Measurable Iexact →
    PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
    RescaledWindowModulusTail
      ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp) T

/-- The `hmodExact` slot of every per-environment producer, verbatim. -/
def ModulusSlotExact (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (T : Set ℝ≥0) : Prop :=
  ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
    Measurable Iexp → Measurable Iexact →
    PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
    RescaledWindowModulusTail
      ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexact) T

/-- The `hgaussExp` slot of
`GaussianLimitIdentification.twoClockScalingLimit_of_window_modulus_of_gaussian_limits`,
verbatim. -/
def GaussSlotExp (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e)) : Prop :=
  ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
    Measurable Iexp → Measurable Iexact →
    PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
    ∀ (ε : ℕ → ℝ≥0) (ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)),
      Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) →
      Tendsto (fun n => diffusivelyRescaledPathLaw
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexp) (ε n))
        atTop (𝓝 ρ) →
      GaussianLimitInput target ρ

/-- The `hgaussExact` slot, verbatim. -/
def GaussSlotExact (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e)) : Prop :=
  ∀ (Zexp Zexact : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (Iexp Iexact : Existence.Sample (Vertex e.val) → BouRabeeGwynne.BrownianPath 2),
    Measurable Iexp → Measurable Iexact →
    PathwiseInterpolationClauses e D hG z start Xexp Xexact Zexp Zexact Iexp Iexact →
    ∀ (ε : ℕ → ℝ≥0) (ρ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)),
      Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) →
      Tendsto (fun n => diffusivelyRescaledPathLaw
        ((areaSampleLaw (decode e) D hG start).toProbabilityMeasure.map Iexact) (ε n))
        atTop (𝓝 ρ) →
      GaussianLimitInput target ρ

/-! ## The per-environment packages -/

/-- The four analytic atoms of
`twoClockScalingLimit_of_window_modulus_of_gaussian_limits`, packaged. -/
def GaussianClockLimitAtoms (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (T : Set ℝ≥0) : Prop :=
  ModulusSlotExp e D hG z start Xexp Xexact T ∧
    ModulusSlotExact e D hG z start Xexp Xexact T ∧
    GaussSlotExp e D hG z target start Xexp Xexact ∧
    GaussSlotExact e D hG z target start Xexp Xexact

/-- `TwoClockScalingLimit` from the packaged Gaussian atoms — the most reduced
per-environment producer, repackaged. -/
theorem twoClockScalingLimit_of_gaussianClockLimitAtoms (e : Env)
    [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (z Φ : CellField)
    (target : AnisotropicBrownianTarget) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hclock : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (T : Set ℝ≥0) (hT : T ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
    (h : GaussianClockLimitAtoms e D hG z target start Xexp Xexact T) :
    TwoClockScalingLimit e D hG z target start Xexp Xexact :=
  twoClockScalingLimit_of_window_modulus_of_gaussian_limits e D hG z Φ target start
    Xexp Xexact M hclock T hT h.1 h.2.1 h.2.2.1 h.2.2.2

/-! ## The almost-every-environment atoms, and the lift -/

/-- The four Gaussian atoms, gated to almost every environment. -/
def AeGaussianClockLimitAtoms (ν : Measure Env) (Φ : CellField) (T : Set ℝ≥0) : Prop :=
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
            GaussianClockLimitAtoms e D hG z target start Xexp Xexact T

/-- **THE LIFT, at the Gaussian atoms.**  Same statement with the two finite-dimensional
atoms replaced by the Gaussian input at every sequential limit point — the form the
martingale-CLT lane produces.

CONDITIONAL on `h`; certifies nothing. -/
theorem aeTwoClockScalingLimit_of_aeGaussianClockLimitAtoms (ν : Measure Env)
    (Φ : CellField) (T : Set ℝ≥0) (hT : T ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
    (h : AeGaussianClockLimitAtoms ν Φ T) :
    AeTwoClockScalingLimit ν Φ := by
  filter_upwards [h] with e he
  intro hnt D hG hdat start Xexp Xexact M hclock target hcov z hz
  have : Nontrivial (Vertex e.val) := hnt
  exact twoClockScalingLimit_of_gaussianClockLimitAtoms e D hG z Φ target start Xexp Xexact
    M hclock T hT (he hnt D hG hdat start Xexp Xexact M hclock target hcov z hz)

/-! ## The two halves recombine into the `hlimit` binder -/

/-- **`hlimit` from the two almost-every-environment halves**, by application of
`InterpolatedTwoClockReduction.hlimit_of_ae_interpolation_data_of_scaling_limit`.

The conclusion is, verbatim, the `hlimit` binder of
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`.  CONDITIONAL on both
halves; certifies neither. -/
theorem hlimit_of_ae_halves (ν : Measure Env) (Φ : CellField)
    (hdata : AeRepresentativeInterpolationData ν Φ)
    (hlaw : AeTwoClockScalingLimit ν Φ) :
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
                  (areaSampleLaw (decode e) D hG ⟨n, hn⟩) target Xexp Xexact :=
  hlimit_of_ae_interpolation_data_of_scaling_limit ν Φ hdata hlaw

end ReflectedGMS.TwoClockLiftEnvironment
