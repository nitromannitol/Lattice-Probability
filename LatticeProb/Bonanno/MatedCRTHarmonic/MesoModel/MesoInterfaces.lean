/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MesoModel.MesoInterfaces at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces
import LatticeProb.Bonanno.LQGMetric.Statement.Field
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Process.Stopping
import Mathlib.Data.ENat.Lattice
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersCellCoupling
import Mathlib.Topology.Connected.LocallyPathConnected
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Tietze
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.Positivity.Finset
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep3
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.HoloLog
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Compactification.OnePoint.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCoord
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTSideCond
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeBasic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.UnzipInvariance
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Order.Floor
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Increments
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Oscillation
import Mathlib.Analysis.Complex.ExponentialBounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.PathLaw
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Process.FiniteDimensionalLaws
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoJaniszewski
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMapCurve
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeDistortion
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.FrozenLocalDynkin
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Dynkin

/-!
# Inputs for mesoscopic cell-model estimates

The probabilistic inputs are stated at the unit-cell coupling and dyadic-mesh level.
The event form of joint scaling below is the scale-transfer consequence of the equality in law of `(h_b, η^b)` with
`(h, η)` and the resulting cell-configuration identity.

The mesh families carry the **multigraph** identification
(`CellFamily.MultigraphCoupledRandomFamily`), the scaled-grid estimate inputs are bad-event (outer-measure)
bounds with no measurability fields, and the unit-mesh output is `UnitMesoscopicOutput`
(no Borel premise).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel

/-- A cell-model sample space, together with its unit-mesh cell embedding and the mesh-indexed
embeddings used in the scaled-grid estimate. The sample space may be restricted to the full-measure event
on which all these geometric objects are defined. Its unit coupling is still the frozen
`IsCellCoupling` definition. The mesh family is a
`CellFamily.MultigraphCoupledRandomFamily`: almost surely each mesh graph *is* the mated-CRT multigraph
(`coupled.meshGraph_eq`), so its walk laws, degrees
and looplessness are those of `MatedCRT.graph`. -/
structure MatedCRTUnitMesoModel (γ : ℝ) where
  coupled : CellFamily.MultigraphCoupledRandomFamily γ
  standardBorel : StandardBorelSpace coupled.family.Ω
  unitLocallyFinite : ∀ ω, MatedCRT.IsLocallyFinite 1 (coupled.bm ω)
  unitEmbedding : ∀ ω,
    CellularEmbedding (MatedCRT.graph 1 (coupled.bm ω) (unitLocallyFinite ω)) 0
  unitEmbedding_cell : ∀ ω, (unitEmbedding ω).cell = coupled.cell ω
  radius : coupled.family.Ω → ℕ → ℝ
  radius_pos : ∀ ω k, 0 < radius ω k
  ρ : ℝ
  hρ : ρ ∈ Set.Ioo 0 1
  q : ℝ
  hq : 0 < q ∧ q < 2 / (2 + γ) ^ 2
  hγ : γ ∈ Set.Ioo 0 2

end MatedCRTHarmonic.MesoModel
