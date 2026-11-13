/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.WalkSteps.WalkPath at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dsrc
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dtgt
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateVertex
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsPlaneData
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.OutDarts
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasureIsProbability
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkKernel
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkKernelIsMarkov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.Chain

/-!
# §4 preliminaries: chained edge-end paths and the embedded walk

An edge-end path `ω : ℕ → G.State` is *chained* with dart sequence `D` if step `k + 1` traverses the dart `D k`
and `D k` leaves the vertex occupied at time `k` (`IsDartChain ω D`). Simple random walk is chained almost surely
(`ae_isChained`; the state space is countable by properness). Along a chained path the embedded walk
`Y = Φ.embeddedWalk ω` (frozen definition, unit time per step) satisfies, the polar-template argument A7/A8 and the blueprint's
Lemma `b:lem-walkcurve`:

* on `[k, k+1]` it is the traversal of `D k`: `Y t = Φ.stepCurve (inr (D k)) (t - k)` (`embeddedWalk_eq_of_mem_Icc`);
* at integer times it sits at the walk's vertex: `Y k = Φ(X_k)` (`embeddedWalk_natCast`);
* it is continuous (`continuous_embeddedWalk`);
* `Y([k, k+1]) = Φ(e_k)` (`image_Icc_succ`) and `Y([m, n]) = ⋃_{m ≤ k < n} Φ(e_k)` (`image_Icc_natCast`);
* at non-integer times it lies on the open arc of the current edge (`embeddedWalk_mem_openArc`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal unitInterval

namespace MatedCRTHarmonic.WalkSteps

variable {V E : Type*} {G : LFMultigraph V E}

section Chained

variable {ω : ℕ → G.State} {D : ℕ → G.Dart}

end Chained

/-! ### Simple random walk is chained almost surely -/

/-- The state space carries the discrete σ-algebra, so singletons are measurable. -/
theorem measurableSingletonClass_state : MeasurableSingletonClass G.State :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Simple random walk starts at its starting vertex almost surely. -/
theorem ae_start (x : V) : ∀ᵐ ω ∂G.walkLaw x, ω 0 = Sum.inl x := by
  have := measurableSingletonClass_state (G := G)
  exact Markov.chainLaw_ae_start G.walkKernel _

end MatedCRTHarmonic.WalkSteps
