/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.DFGPSInputsDG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Blueprint
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputs
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundary
import Mathlib.Analysis.SpecialFunctions.Log.Base
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

/-!
# Blueprint: the DG results DFGPS Lemma 3.6 cites (task P2-BP-DF)

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

open WhiteNoise DDDF DG

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

/-- the open square `(−1,2)²`, interior of DG's `𝕊(1) = [−1,2]²` (DG:1098) -/
def sqOne : TopologicalSpace.Opens ℂ :=
  ⟨Complex.re ⁻¹' Ioo (-1) 2 ∩ Complex.im ⁻¹' Ioo (-1) 2,
    (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)⟩

/-- DG's `𝕊(1/2) = [−1/2, 3/2]²`, the expanded square of `𝕊 = [0,1]²` (DG:1165); it lies at
distance `1/2` from `∂𝕊(1)`, so `𝕊(1/2) ⊆ 𝒰_{1/4}` in the notation of DGW Prop 3.2 -/
def sqHalf : Set ℂ := {z | -1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2 ∧ -1 / 2 ≤ z.im ∧ z.im ≤ 3 / 2}

/-- `hz` is a zero-boundary GFF on `U` extended by zero: its restriction to `U` is a zero-boundary
GFF and it vanishes off `cl U` (as in `LMLem2_1`) -/
def IsZBGFFExtDist {Ω : Type} [MeasurableSpace Ω] (U : TopologicalSpace.Opens ℂ)
    (hz : Ω → DistC) (P : Measure Ω) : Prop :=
  IsZeroBoundaryGFF U (fun ω => restrictTo U (hz ω)) P ∧
    ∀ ω, restrictTo (toOpens (closure (U : Set ℂ))ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0

/-- `hc` is a version of the circle averages `h_δ(x)` of `hz`, continuous in `x ∈ 𝕊(1/2)`, for
`δ ∈ (0, 1/2)` (then `B̄_δ(x) ⊆ (−1,2)²`; DS Prop 3.1 as read at DGW:190–192: a version jointly
Hölder on compact subsets of `{(v,δ) : 0 < δ < d(v, ∂𝕊(1))}`; D118) -/
def IsCircleAvgVersionSq {Ω : Type} [MeasurableSpace Ω] (hz : Ω → DistC)
    (hc : ℝ → ℂ → Ω → ℝ) (P : Measure Ω) : Prop :=
  (∀ δ ∈ Ioo (0 : ℝ) (1 / 2), ∀ ω, ContinuousOn (fun x => hc δ x ω) sqHalf) ∧
    ∀ δ ∈ Ioo (0 : ℝ) (1 / 2), ∀ x ∈ sqHalf, hc δ x =ᵐ[P] fun ω => circleAvg (hz ω) δ x

/-- a coupling of a white noise `W` (hence `ĥ_t = φ_{t,1}`) and a zero-boundary GFF `hz` on
`𝕊(1)` with continuous circle averages `hc` -/
def IsDGCoupling {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (hz : Ω → DistC) (hc : ℝ → ℂ → Ω → ℝ) : Prop :=
  IsProbabilityMeasure P ∧ IsWhiteNoise P W ∧ IsZBGFFExtDist sqOne hz P ∧
    IsCircleAvgVersionSq hz hc P

/-- **DG Lemma 3.7** (`lem-circle-avg-approx`, DG:1096–1102): "Let `h^{𝕊(1)}` be a zero-boundary
GFF on the square `𝕊(1)`. There is a coupling of `ĥ` and `h^{𝕊(1)}` such that for each `C > 0`
and each `ζ ∈ (0,1)`, it holds with superpolynomially high probability as `δ → 0` that
`max_{z,w∈𝕊: |z−w| ≤ Cδ} |h^{𝕊(1)}_δ(z) − ĥ_δ(w)| ≤ ζ log δ⁻¹`." Stated on `𝕊(1/2) = [−1/2,3/2]²`
in place of `𝕊` (D118): this is the form DG use in the proof of Prop 3.22 (DG:1729–1731, LFPP
paths in `𝕊(1/2)`), and it is what DG's proof gives — DGW Prop 3.2 (arXiv Prop 3.3, DGW:549–554)
holds for every `V ⊆ 𝒰_ε`, `δ < ε/4`, here `𝒰 = (−1,2)²`, `ε = 1/4`, and DG L3.4 holds on every
bounded domain. -/
def DGLem3_7 : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hz : Ω → DistC)
    (hc : ℝ → ℂ → Ω → ℝ), IsDGCoupling P W hz hc ∧
    ∀ C : ℝ, 0 < C → ∀ ζ ∈ Ioo (0 : ℝ) 1, ∀ p : ℝ, 0 < p → ∃ K δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        P {ω | ¬ ∀ z ∈ sqHalf, ∀ w ∈ sqHalf, ‖z - w‖ ≤ C * δ →
          |hc δ z ω - phiVer W P δ 1 w ω| ≤ ζ * Real.log δ⁻¹} ≤ ENNReal.ofReal (K * δ ^ p)

/-! ## DG's approximate δ-LFPP distance (3.32) -/

/-- `m_δ = ⌈log₂ δ⁻¹⌉` (DG:1425) -/
def dgM (δ : ℝ) : ℕ := ⌈Real.logb 2 δ⁻¹⌉₊

/-- indices of the dyadic squares of side `2^{-m}` contained in `𝕊 = [0,1]²` -/
def dgIdx (m : ℕ) : Set (ℤ × ℤ) := {k | 0 ≤ k.1 ∧ k.1 < 2 ^ m ∧ 0 ≤ k.2 ∧ k.2 < 2 ^ m}

/-- the centre `v_S` of the square `gridSquare (2^{-m}) k` -/
def dgCenter (m : ℕ) (k : ℤ × ℤ) : ℂ :=
  ⟨(k.1 + 1 / 2) * (2 : ℝ)⁻¹ ^ m, (k.2 + 1 / 2) * (2 : ℝ)⁻¹ ^ m⟩

/-- two squares of the grid share a side -/
def dgAdj (k k' : ℤ × ℤ) : Prop := |k.1 - k'.1| + |k.2 - k'.2| = 1

/-- `S_0, …, S_k` distinct squares of `𝒮_{2^{-m}}`, `z ∈ S_0`, `w ∈ S_k`, consecutive ones
sharing a side (DG:1428–1429) -/
def IsDGSqChain (m : ℕ) (z w : ℂ) (L : List (ℤ × ℤ)) : Prop :=
  L.Nodup ∧ (∀ k ∈ L, k ∈ dgIdx m) ∧ L.IsChain dgAdj ∧
    (∃ k ∈ L.head?, z ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k) ∧
    (∃ k ∈ L.getLast?, w ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k)

/-- **DG (3.32)** (DG:1425–1430): `D̂^δ_{ĥ,LFPP}(z,w;𝕊) = min_{S_0,…,S_k} Σ_j δ e^{ξ ĥ_δ(v_{S_j})}`
(field `φ = ĥ_δ`) -/
def dgApproxLFPP (ξ δ : ℝ) (φ : ℂ → ℝ) (z w : ℂ) : ℝ :=
  ⨅ L : {L : List (ℤ × ℤ) // IsDGSqChain (dgM δ) z w L},
    (L.1.map fun k => δ * Real.exp (ξ * φ (dgCenter (dgM δ) k))).sum

/-- `ĥ_δ(v_{S_z})`: the maximum of `φ` over the centres of the squares of `𝒮_{2^{-m_δ}}` that
contain `z` (DG:1437) -/
def dgMaxSq (δ : ℝ) (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  ⨆ k : {k : ℤ × ℤ // k ∈ dgIdx (dgM δ) ∧ z ∈ gridSquare ((2 : ℝ)⁻¹ ^ dgM δ) k},
    φ (dgCenter (dgM δ) k.1)

/-- **DG Proposition 3.16, corrected** (D126; `prop-lfpp-approx`, DG:1432–1437): "There is a
coupling of `ĥ` and `h^{𝕊(1)}` such that the following is true. For each `ζ ∈ (0,1)` and each
`ξ > 0`, it holds with polynomially high probability as `δ → 0` that for each `z, w ∈ 𝕊`,
`δ^ζ (D̂^δ_{ĥ,LFPP}(z,w;𝕊) − δ^{1−ζ} e^{ξ ĥ_δ(v_{S_z})}) ≤ D^δ_{h^{𝕊(1)},LFPP}(z,w;𝕊) ≤
δ^{−ζ} D̂^δ_{ĥ,LFPP}(z,w;𝕊)`", i.e. `δ^ζ D̂ ≤ D + δ e^{ξ ĥ_δ(v_{S_z})}`. DG print the error term
as `δ e^{ξ ĥ_δ(v_{S_z})}` (DG:1436); that statement is false (`DG.not_dgProp3_16Printed`,
Papers/DG/S3P16A.lean: `z`, `w` at distance `2ε → 0` on either side of a side shared by two grid
squares, where `D^δ(z,w) → 0` while every chain contains both squares) and DG's proof has a gap
at DG:1500–1512 (the squares crossed in time `< δ^{1+ζ/2}` before the first long crossing have
no `J_j`). DG's argument at DG:1505–1508 shows that these squares are at most 4, with centres
within `3δ` of `v_{S_z}`, so on (3.34) their total weight is `≤ 4 δ^{1−ζ/2} e^{ξ ĥ_δ(v_{S_z})}`;
this is the corrected statement (DEC-126 §1). (`D^δ(z,w;𝕊)`: circle-average LFPP of `h^{𝕊(1)}`
along piecewise `C¹` paths in `𝕊`, DG:326, `DG.dgLFPP`.) -/
def DGProp3_16 : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hz : Ω → DistC)
    (hc : ℝ → ℂ → Ω → ℝ), IsDGCoupling P W hz hc ∧
    ∀ ζ ∈ Ioo (0 : ℝ) 1, ∀ ξ : ℝ, 0 < ξ → ∃ p K δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧
      ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        P {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
          δ ^ ζ * (dgApproxLFPP ξ δ (fun x => phiVer W P δ 1 x ω) z w -
              δ ^ (1 - ζ) * Real.exp (ξ * dgMaxSq δ (fun x => phiVer W P δ 1 x ω) z)) ≤
            dgLFPP ξ (fun x => hc δ x ω) closedUnitSquare z w ∧
          dgLFPP ξ (fun x => hc δ x ω) closedUnitSquare z w ≤
            δ ^ (-ζ) * dgApproxLFPP ξ δ (fun x => phiVer W P δ 1 x ω) z w} ≤
          ENNReal.ofReal (K * δ ^ p)

end LQGMetric.Blueprint
