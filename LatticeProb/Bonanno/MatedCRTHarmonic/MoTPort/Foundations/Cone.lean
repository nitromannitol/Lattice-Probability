/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.Cone at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.Params
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import Mathlib.Analysis.SpecialFunctions.Log.Base
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundary
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFDefs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Statement.Metric
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.EReal.Lemmas
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes
import LatticeProb.Bonanno.LQGMetric.Metric.LengthSpace
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.MeasureTheory.Measure.Tight
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Dilate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Field.MarkovExt
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MapComap
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryExt
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
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
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Basic
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyVar
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegKolm
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN
import LatticeProb.Bonanno.LQGMetric.Metric.WeylBasic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import LatticeProb.Bonanno.LQGMetric.LFPP.PathPiece
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.ConditionalProbability
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen6
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import Mathlib.Probability.Moments.Covariance
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.LQGMetric.Field.GreenSquare2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P29Second
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareTheta
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBound
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L2Space
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1RadialMain
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import Mathlib.MeasureTheory.Integral.Indicator
import LatticeProb.Bonanno.QuantumZipper.Proofs.NonVacuity
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2H

/-!
# Quantum cones (DMS Def 4.10)

DMS (arXiv:1409.7055v4) Def `def::quantum_cone` (L2198–2201): for `α < Q`, the
`α`-quantum cone is the field `h` on `ℂ` whose average on `∂B(0,e^{-s})` is `A_s`, with `A_s` as
in Def 4.5 (L2071) "except with `B_{2s}` and `B̂_{2s}` replaced by `B_s` and `B̂_s`", and whose
lateral part (projection onto `H₂(ℂ)`, Lemma `lem::c_spaces_orthogonal` L2187) is that of a
whole-plane GFF. Weight `W = 2γ(Q − α)` (Table 1.2, DMS (1.?) `eqn::quantum_cone_weight`; our
`coneAlpha γ W = Q − W/(2γ)`, Params.lean).

* `conePath α Q b b'` is a thin layer over QuantumZipper's `wedgePath` (QZ/LQG/WedgeProcess.lean)
  by Brownian scaling: `wedgePath (Q + 2(α−Q)) Q (b(2·)/√2) (b'(2·)/√2) (t/2)`. In QZ's convention
  (`t = −log|z|`, circle average at radius `e^{-t}` equal to `Q t + A_t`) it is `b_t + (α−Q)t` for
  `t ≥ 0` (`conePath_of_nonneg`; so `Q t + A_t = b_t + α t`, DMS's `B_s + αs`) and the
  last-zero-normalized path `b'_s + (Q−α)s` for `t < 0` (`conePath_of_neg`).
* `IsConeProcess` copies the shape of QZ's `IsWedgeProcess`; `isWedgeProcess_of_isConeProcess`:
  a cone process run at twice the speed is a QZ wedge process with `α' = Q + 2(α−Q)` (mathlib
  `IsBrownianReal.smul`).
* `coneField y A Q = y + (Q(−log|·|) + A_{−log|·|})` (the `Field` analogue of QZ `wedgeField`).
* `IsQuantumCone γ W Y P`: the law of `Y` up to dilation and rotation (`surfLawC`, ConeArea.lean)
  is that of `coneField (lateralPartC X) A Q` with `X` a whole-plane GFF (LM `IsWholePlaneGFF`)
  and `A` an independent cone process. The same canonicalization makes DMS's choice of embedding
  (circle-average embedding) irrelevant, exactly as for QZ's `IsQuantumWedge`.
* `exists_isQuantumCone`: for every `W > 0` there is a quantum cone, given the open node C.meas
  (`ConeRefMeas`, needed for the measurability guards of `IsQuantumCone`) (construction as in
  WedgeExist.lean / QZ `NonVacuity`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Pointwise

namespace MatedCRTHarmonic.MoTPort

open QuantumZipper LQGMetric

/-- the cone radial path (DMS Def 4.10: Def 4.5 with `B_{2s}` replaced by `B_s`), QZ convention:
`QZ.wedgePath` of the Brownian-rescaled paths, run at half speed -/
def conePath (α Q : ℝ) (b b' : ℝ≥0 → ℝ) : ℝ → ℝ :=
  fun t => wedgePath (Q + 2 * (α - Q)) Q (fun s => (√2)⁻¹ * b (2 * s))
    (fun s => (√2)⁻¹ * b' (2 * s)) (t / 2)

/-- the `∞`-side path `b'_s − (α−Q)s` of the cone, before the last-zero shift -/
def coneTail (α Q : ℝ) (b' : ℝ≥0 → ℝ) : ℝ → ℝ := fun s => b' s.toNNReal - (α - Q) * s

/-- `A` is the radial process of an `α`-quantum cone: `conePath` of two independent standard
Brownian motions (shape of QZ `IsWedgeProcess`) -/
def IsConeProcess {Ω : Type*} [MeasurableSpace Ω] (α Q : ℝ) (A : ℝ → Ω → ℝ) (P : Measure Ω) :
    Prop :=
  ∃ B B' : ℝ≥0 → Ω → ℝ, IsBrownianReal B P ∧ IsBrownianReal B' P ∧
    IndepFun (pathOf B) (pathOf B') P ∧
    ∀ ω t, A t ω = conePath α Q (fun s => B s ω) (fun s => B' s ω) t

/-- the cone field on `ℂ`: `y + Q(−log|·|) + A_{−log|·|}` (the `Field` analogue of QZ `wedgeField`) -/
def coneField (y : Field) (A : ℝ → ℝ) (Q : ℝ) : Field :=
  y + ofFunC fun z => Q * (-Real.log ‖z‖) + A (-Real.log ‖z‖)

namespace Cone

lemma two_mul_toNNReal (s : ℝ) : (2 : ℝ≥0) * s.toNNReal = (2 * s).toNNReal := by
  rw [Real.toNNReal_mul zero_le_two]; simp

lemma two_mul_toNNReal_half (t : ℝ) : (2 : ℝ≥0) * (t / 2).toNNReal = t.toNNReal := by
  rw [two_mul_toNNReal]; congr 1; ring

/-- for `t ≥ 0` (inside the unit disc): `A_t = b_t + (α − Q) t` -/
theorem conePath_of_nonneg (α Q : ℝ) (b b' : ℝ≥0 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    conePath α Q b b' t = b t.toNNReal + (α - Q) * t := by
  have ht2 : 0 ≤ t / 2 := by positivity
  simp only [conePath, wedgePath, if_pos ht2, two_mul_toNNReal_half]
  have : Real.sqrt 2 * (√2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [← mul_assoc, this, one_mul]; ring

/-- the rescaled tail used by `wedgePath` is `coneTail` at twice the time -/
lemma wedgeTail_eq (α Q : ℝ) (b' : ℝ≥0 → ℝ) :
    (fun s : ℝ => Real.sqrt 2 * ((√2)⁻¹ * b' (2 * s.toNNReal)) - (Q + 2 * (α - Q) - Q) * s) =
      fun s => coneTail α Q b' (2 * s) := by
  funext s
  have : Real.sqrt 2 * (√2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [← mul_assoc, this, one_mul, two_mul_toNNReal, coneTail]; ring

lemma lastZero_comp_two_mul (C : ℝ → ℝ) :
    lastZero (fun s => C (2 * s)) = lastZero C / 2 := by
  unfold lastZero
  have e : {s : ℝ | 0 ≤ s ∧ C (2 * s) = 0} = (2⁻¹ : ℝ) • {u : ℝ | 0 ≤ u ∧ C u = 0} := by
    ext s
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by norm_num)]
    simp only [Set.mem_setOf_eq, inv_inv, smul_eq_mul]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by positivity, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  rw [e, Real.sSup_smul_of_nonneg (by norm_num), smul_eq_mul]; ring

/-- for `t < 0` (outside the unit disc): `A_t = C(−t + s₀)` with `C_s = b'_s + (Q − α)s` and `s₀`
the last zero of `C` (DMS Def 4.10 with Def 4.5: the conditioned side, realized after the last
zero as in QZ `wedgePath`) -/
theorem conePath_of_neg (α Q : ℝ) (b b' : ℝ≥0 → ℝ) {t : ℝ} (ht : t < 0) :
    conePath α Q b b' t =
      coneTail α Q b' (-t + lastZero (coneTail α Q b')) := by
  have ht2 : ¬ 0 ≤ t / 2 := by intro h; linarith
  simp only [conePath, wedgePath, if_neg ht2]
  rw [wedgeTail_eq, lastZero_comp_two_mul]
  have key := congrFun (wedgeTail_eq α Q b') (-(t / 2) + lastZero (coneTail α Q b') / 2)
  rw [key]
  congr 1; ring

/-! ## Cone processes are wedge processes at twice the speed (Brownian scaling) -/

lemma measurable_scaleTwo :
    Measurable fun (p : ℝ≥0 → ℝ) (s : ℝ≥0) => (√2)⁻¹ * p (2 * s) :=
  measurable_pi_iff.mpr fun s => (measurable_pi_apply (2 * s)).const_mul _

lemma isBrownianReal_scaleTwo {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    IsBrownianReal (fun s ω => (√2)⁻¹ * B (2 * s) ω) P := by
  have := hB.smul (c := 2) two_ne_zero
  simpa using this

/-- **Brownian scaling**: `t ↦ A_{2t}` of a cone process is QZ's wedge process with
`α' = Q + 2(α − Q)` (so all a.s. path facts of `QZ.IsWedgeProcess` transfer to cones) -/
theorem isWedgeProcess_of_isConeProcess {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {α Q : ℝ} {A : ℝ → Ω → ℝ} (hA : IsConeProcess α Q A P) :
    IsWedgeProcess (Q + 2 * (α - Q)) Q (fun t ω => A (2 * t) ω) P := by
  obtain ⟨B, B', hB, hB', hI, hA⟩ := hA
  refine ⟨fun s ω => (√2)⁻¹ * B (2 * s) ω, fun s ω => (√2)⁻¹ * B' (2 * s) ω,
    isBrownianReal_scaleTwo hB, isBrownianReal_scaleTwo hB', ?_, fun ω t => ?_⟩
  · exact hI.comp measurable_scaleTwo measurable_scaleTwo
  · show A (2 * t) ω = _
    rw [hA, conePath, mul_div_cancel_left₀ t two_ne_zero]

/-! ## Existence -/

end Cone

end MatedCRTHarmonic.MoTPort
