/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TargetTraceTransition at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnPairProcessLaw
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceLaplaceResolvent

/-!
# Transition law and finite resolvent of the original-process target trace

The target-return pair retains the original holding interval at every visit to
the finite target, including self returns, and deletes the intervening
excursions outside the target.  Reading this pair through `jumpPath` therefore
gives the corresponding target-trace process.  Its transition law is the
canonical induced-chain law, and for the finite-trace speed this identifies its
Laplace transform with the finite occupation resolvent.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.TargetTraceTransition

open ReflectedWalk ReflectedWalk.Theorem16 ReflectedWalk.ContinuousTimeChain
open TargetReturnPairProcessLaw
open FullNetworkForm

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- The original-process trace on `A`, obtained by retaining each holding
interval at a target visit and concatenating those intervals. -/
noncomputable def targetTraceProcess {Ω : Type u} (X : ℝ≥0 → Ω → Option V)
    (A : Finset V) (default : V) (t : ℝ≥0) (ω : Ω) : Option V :=
  jumpPath (targetReturnPair X A default ω) t

/-- At each fixed time, the target trace extracted from an actual reflected
walk is almost-everywhere measurable. -/
theorem aemeasurable_targetTraceProcess (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {x : V} (hx : x ∈ A) (t : ℝ≥0) :
    AEMeasurable (targetTraceProcess PF.X A x t) (PF.P x) := by
  exact (measurable_jumpPath t).comp_aemeasurable
    (aemeasurable_targetReturnPair h hG hA hx)

/-- The fixed-time transition probability of the original-process target
trace equals that of the canonical induced chain with exponential holdings. -/
theorem targetTraceProcess_transition_eq (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ v, 0 < w v)
    {A : Finset V} (hA : A.Nonempty) {x : V} (hx : x ∈ A)
    (t : ℝ≥0) (y : V) :
    PF.P x {ω | targetTraceProcess PF.X A x t ω = some y} =
      (MarkovChain.chainLaw (G.inducedKernel hG hA) x ⊗ₘ holdingKernel w)
        {p | jumpPath p t = some y} := by
  let S : Set ((ℕ → V) × (ℕ → ℝ)) := {p | jumpPath p t = some y}
  have hS : MeasurableSet S := (measurable_jumpPath t) (measurableSet_singleton (some y))
  calc
    PF.P x {ω | targetTraceProcess PF.X A x t ω = some y} =
        (PF.P x).map (targetReturnPair PF.X A x) S := by
      rw [Measure.map_apply_of_aemeasurable
        (aemeasurable_targetReturnPair h hG hA hx) hS]
      rfl
    _ = (MarkovChain.chainLaw (G.inducedKernel hG hA) x ⊗ₘ holdingKernel w) S := by
      rw [map_targetReturnPair h hG hw hA hx]

/-- The original target-trace transition probability is measurable in real
time. -/
theorem measurable_targetTraceProcess_transitionReal
    (h : IsReflectedWalk G w hmin PF) (hG : G.toSimpleGraph.Connected)
    (hw : ∀ v, 0 < w v) {A : Finset V} (hA : A.Nonempty)
    {x : V} (hx : x ∈ A) (y : V) :
    Measurable fun t : ℝ =>
      (PF.P x {ω |
        targetTraceProcess PF.X A x (Real.toNNReal t) ω = some y}).toReal := by
  have heq : (fun t : ℝ =>
      (PF.P x {ω |
        targetTraceProcess PF.X A x (Real.toNNReal t) ω = some y}).toReal) =
      fun t : ℝ =>
        ((MarkovChain.chainLaw (G.inducedKernel hG hA) x ⊗ₘ holdingKernel w)
          {p | jumpPath p (Real.toNNReal t) = some y}).toReal := by
    funext t
    rw [targetTraceProcess_transition_eq h hG hw hA hx]
  rw [heq]
  exact
    (TraceLaplaceConvergence.measurable_jumpPath_vertexProbability
      (MarkovChain.chainLaw (G.inducedKernel hG hA) x ⊗ₘ holdingKernel w) y).ennreal_toReal

/-- For speed `π/m`, the Laplace transform of the original target-trace
transition probability is the finite occupation resolvent applied to the
weighted indicator of the target vertex. -/
theorem targetTraceProcess_laplace_eq_resolvent
    (hG : G.toSimpleGraph.Connected) (A : Finset V) (hA : A.Nonempty)
    (m : V → ℝ) (hm : ∀ v, 0 < m v) (h : IsReflectedWalk G
      (fun v => G.pi v / m v) hmin PF) {alpha : ℝ} (halpha : 0 < alpha)
    (x y : {v // v ∈ A}) :
    (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
      (PF.P x.1 {ω | targetTraceProcess PF.X A x.1 (Real.toNNReal t) ω =
        some y.1}).toReal) =
      finiteTraceOccupationResolvent G hG A hA m alpha
        (weightedValue (fun z : {v // v ∈ A} => m z.1)
          ((finiteTargetGraph G hG A hA).indic y)
          (VertexTest.indic_hasSpeedL2 (finiteTargetGraph G hG A hA)
            (fun z : {v // v ∈ A} => m z.1) y)) x := by
  have hw : ∀ v, 0 < G.pi v / m v := fun v =>
    div_pos (G.pi_pos_of_connected hG v) (hm v)
  have htransition (t : ℝ) :
      (PF.P x.1 {ω | targetTraceProcess PF.X A x.1 (Real.toNNReal t) ω =
        some y.1}).toReal =
      ((MarkovChain.chainLaw (G.inducedKernel hG hA) x.1 ⊗ₘ
          holdingKernel (fun v => G.pi v / m v))
        {p | jumpPath p (Real.toNNReal t) = some y.1}).toReal := by
    rw [targetTraceProcess_transition_eq h hG hw hA x.property]
  simp_rw [htransition]
  exact finiteTrace_jumpPath_laplace_eq_resolvent
    G hG A hA m hm halpha x y

end ReflectedGMS.TargetTraceTransition
