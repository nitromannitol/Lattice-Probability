/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.DFGPSInputsDG at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (DDDF). -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Blueprint
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Measure.Prod
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import LatticeProb.Bonanno.LQGMetric.Statement.Field
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Function.L2Space
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower3
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Restrict
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
Source: DG = Ding–Gwynne, *The fractal dimension of Liouville quantum gravity: universality,
monotonicity, and bounds*, arXiv:1807.01072, `literature/src/1807.01072/metric-comparison-final.tex`
(cited `DG:`). Consumer: DFGPS (arXiv:1905.00380, cited `T:`) Lemma 3.6 (T:1628–1650): "by
[DG, Theorem 1.5] … [DG, Lemma 3.7] … the same argument as in [DG, Proposition 3.16]".

* DG Thm 1.5 (DG:336–347): (1.5a) and the first half of (1.5b) are `LQGMetric.DG.DGThm1_5`
  (reused); the second half of (1.5b), `D^δ(K, ∂U) = δ^{λ+o(1)}`, which DFGPS's lower bound needs
  (left–right crossing ≥ distance from the left side to the boundary of its neighbourhood, node
  DFGPS.S11), is `DGThm1_5KU` here.
* DG (3.1) (DG:907): `ĥ_t(z) = √π ∫_{t²}^1 ∫ p(s/2; z,w) W(dw,ds)` is DDDF's `φ_{t,1}`; its
  continuous modification is `DDDF.phiVer W P t 1` (no new definition).
* `DGLem3_7` — DG Lemma 3.7 (`lem-circle-avg-approx`, DG:1096–1102).
* `DGProp3_16` — DG Proposition 3.16 (`prop-lfpp-approx`, DG:1432–1437), lower bound corrected
  (D126), with the approximate δ-LFPP distance (3.32) (DG:1425–1430) `dgApproxLFPP`.

Readings (proposed DEVIATIONS entries BP-DF-8…10, see the P2-BP-DF report):
* `h^{𝕊(1)}`, a zero-boundary GFF on `𝕊(1) = [−1,2]²`, is a random distribution on `ℂ` whose
  restriction to `(−1,2)²` is a zero-boundary GFF and which vanishes off `[−1,2]²` (as in
  `LMLem2_1`); its circle averages `h^{𝕊(1)}_δ(z)` (`z ∈ 𝕊(1/2) = [−1/2,3/2]²`, `δ ∈ (0,1/2)`, D118) are taken in a
  version continuous on `𝕊` (DS Prop 3.1); since the coupling is asserted to exist, the version is
  part of it.
* "superpolynomially / polynomially high probability as δ → 0" as in `DFGPSEstimates`
  (`P[failure] ≤ K δ^p` for `δ < δ₀`, every / some `p > 0`); events over uncountably many points
  use the outer measure.
* (1.5b)'s second half is stated for bounded open `U` and nonempty compact `K ⊂ U` (otherwise
  `∂U` or `K` may be empty and the distance is `∞`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

open WhiteNoise DG

/-- `D^δ_{LFPP}(K, ∂U) = inf_{z∈K, w∈∂U} D^δ_{LFPP}(z, w)` (DG (1.5b), second half) -/
def dgSetDist (ξ : ℝ) (φ : ℂ → ℝ) (K U : Set ℂ) : ℝ≥0∞ :=
  ⨅ z ∈ K, ⨅ w ∈ frontier U, ENNReal.ofReal (dgLFPP ξ φ univ z w)

/-- **DG Theorem 1.5, second half of (1.5b)** (`thm-lfpp-compare`, DG:343–346): "for each open
set `U ⊂ ℂ` and each compact set `K ⊂ U`, it holds with probability tending to 1 as `δ → 0` that
… `D^δ_{h,LFPP}(K, ∂U) = δ^{1 − 2/d_γ − γ²/(2d_γ) + o_δ(1)}`" (`h` whole-plane GFF with
`h_1(0) = 0`, circle-average LFPP, `ξ = γ/d_γ`; field model as in `DG.DGThm1_5`). -/
def DGThm1_5KU : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hc : ℝ → ℂ → Ω → ℝ),
      LQGDimension.IsGFFCircleAverage hc P →
      ∀ U K : Set ℂ, IsOpen U → Bornology.IsBounded U → IsCompact K → K.Nonempty → K ⊆ U →
        ∀ η : ℝ, 0 < η →
        Tendsto (fun δ : ℝ => P {ω | ¬ (ENNReal.ofReal (δ ^ (dgLambda γ + η)) ≤
            dgSetDist (xiGamma γ) (fun x => hc δ x ω) K U ∧
          dgSetDist (xiGamma γ) (fun x => hc δ x ω) K U ≤ ENNReal.ofReal (δ ^ (dgLambda γ - η)))})
          (𝓝[>] 0) (𝓝 0)

/-! ## DG's approximate δ-LFPP distance (3.32) -/

end LQGMetric.Blueprint
