/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.Defs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsDG
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsDG2
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import LatticeProb.Bonanno.LQGMetric.Statement.Metric
import Mathlib.MeasureTheory.Function.FactorsThrough
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.MetricSpace.Polish
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSScaling
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Basic
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS: definitions shared by the work packages (DF-A0)

Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage percolation*
(arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"). Code from `blueprint/DF.md` §5 (type-checked by P2-BP-DF, 2026-10-01): `setDistIn` (D(A,B;V)),
`SuperPolyHighProbA` (T:607), `rS` (𝕣𝕊), the 8-neighbour graph LFPP `graphLFPP` (T:1606–1612) and
the left/right vertices (T:1626).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

/-! ## Definitions (WP-DF0, file `LQGMetric/Papers/DFGPS/Defs.lean`) -/

/-- `D(A, B; V) = inf_{u∈A, v∈B} D(u, v; V)` -/
def setDistIn (D : ContMetric) (A B V : Set ℂ) : ℝ≥0∞ := ⨅ u ∈ A, ⨅ v ∈ B, D.internal V u v

/-- "`E^A_𝕣` holds with superpolynomially high probability as `A → ∞`, uniformly in `𝕣`" (T:607) -/
def SuperPolyHighProbA {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → ℝ → Set Ω) :
    Prop :=
  ∀ p : ℝ, 0 < p → ∃ C A₀ : ℝ, ∀ A, A₀ < A → ∀ 𝕣 : ℝ, 0 < 𝕣 →
    P (E A 𝕣)ᶜ ≤ ENNReal.ofReal (C * A ^ (-p))

/-- the open unit square `𝕊 = (0,1)²` scaled: `𝕣𝕊` -/
def rS (𝕣 : ℝ) : Set ℂ := scaleSet 𝕣 0 {z | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < 1}

/-- the graph `U ∩ εℤ²` with diagonal edges (T:1606): a path `π` as a list of vertices -/
def IsGraphPath (ε : ℝ) (U : Set ℂ) (L : List ℂ) : Prop :=
  L ≠ [] ∧ (∀ x ∈ L, x ∈ U ∧ x ∈ gridPts ε) ∧
    L.IsChain fun x y => ‖x - y‖ = ε ∨ ‖x - y‖ = Real.sqrt 2 * ε

/-- discretized LFPP `D̃^ε_h(A, B; U) = min_π Σ_{j=0}^{|π|} e^{ξ h_ε(π(j))}` (T:1612) over graph
paths from `A` to `B` (field `φ = h_ε`) -/
def graphLFPP (ξ ε : ℝ) (φ : ℂ → ℝ) (A B U : Set ℂ) : ℝ :=
  ⨅ L : {L : List ℂ // IsGraphPath ε U L ∧ (∃ x ∈ L.head?, x ∈ A) ∧ ∃ y ∈ L.getLast?, y ∈ B},
    (L.1.map fun x => Real.exp (ξ * φ x)).sum

/-- leftmost / rightmost vertices `∂^ε_{L/R}(𝕣𝕊)` of `𝕣𝕊 ∩ εℤ²` (T:1626) -/
def leftVerts (ε 𝕣 : ℝ) : Set ℂ :=
  {x | x ∈ rS 𝕣 ∩ gridPts ε ∧ ∀ y ∈ rS 𝕣 ∩ gridPts ε, x.re ≤ y.re}
/-- see `leftVerts` -/
def rightVerts (ε 𝕣 : ℝ) : Set ℂ :=
  {x | x ∈ rS 𝕣 ∩ gridPts ε ∧ ∀ y ∈ rS 𝕣 ∩ gridPts ε, y.re ≤ x.re}

end LQGMetric.DFGPS
