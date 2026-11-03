/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Harmonic.Walk at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateVertex
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Deg
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasureIsProbability
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkKernel
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkKernelIsMarkov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Graph
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.FirstStep

/-!
# Simple random walk on a locally finite multigraph

The edge-end walk `G.walkLaw x` (a `Markov.chainLaw` on `G.State = V ⊕ Dart`, discrete σ-algebra):

* `G.State` is discrete (`instDiscreteMeasurableSpaceState`) and countable when `V` and `E` are;
* one step from `x` charges each out-dart with `(deg x)⁻¹` (`stepMeasure_singleton_inr`) and
  nothing else (`stepMeasure_notOut`);
* almost surely the walk starts at `inl x` and every step traverses an out-dart of the current
  vertex (`ae_isWalkPath`), from the general chain statement `ae_forall_succ_mem`;
* on a connected graph, the walk from any state hits any nonempty `A` with positive probability
  (`hitProb_pos`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace MatedCRTHarmonic.Harmonic

open Markov

section Chain

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
  (κ : Kernel S S) [IsMarkovKernel κ]

/-- If every one-step law `κ u` is carried by `R u`, then almost surely every step `ω n → ω (n+1)`
lands in `R (ω n)`. -/
theorem ae_forall_succ_mem (z : S) (R : S → Set S) (hR : ∀ u, κ u (R u)ᶜ = 0) :
    ∀ᵐ ω ∂chainLaw κ z, ∀ n, ω (n + 1) ∈ R (ω n) := by
  rw [ae_all_iff]
  intro n
  refine measure_mono_null (t := ⋃ p : S × S, {ω | ω n = p.1 ∧ ω (n + 1) = p.2} ∩
    {_ω | p.2 ∉ R p.1}) ?_ (measure_iUnion_null fun p => ?_)
  · intro ω hω
    exact Set.mem_iUnion.mpr ⟨(ω n, ω (n + 1)), ⟨rfl, rfl⟩, hω⟩
  · by_cases hp : p.2 ∈ R p.1
    · simp [hp]
    · refine measure_mono_null Set.inter_subset_left ?_
      rw [chainLaw_eval_eq_eval_succ_eq]
      have : κ p.1 {p.2} = 0 :=
        measure_mono_null (Set.singleton_subset_iff.mpr hp) (hR p.1)
      rw [this, mul_zero]

end Chain

open LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

instance instDiscreteMeasurableSpaceState : DiscreteMeasurableSpace G.State :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance instCountableState [Countable V] [Countable E] : Countable G.State :=
  inferInstanceAs (Countable (V ⊕ (E × Bool)))

/-- The initial state "at vertex `x`". -/
def startState (x : V) : G.State := Sum.inl x

/-- The state "just traversed the dart `d`". -/
def dartState (d : G.Dart) : G.State := Sum.inr d

@[simp] theorem stateVertex_startState (x : V) : G.stateVertex (startState G x) = x := rfl

@[simp] theorem stateVertex_dartState (d : G.Dart) : G.stateVertex (dartState G d) = G.dtgt d := rfl

theorem walkLaw_eq (x : V) : G.walkLaw x = chainLaw G.walkKernel (startState G x) := rfl

instance instIsProbabilityMeasureWalkLaw (x : V) : IsProbabilityMeasure (G.walkLaw x) := by
  rw [walkLaw_eq]; infer_instance

theorem dartState_injective : Function.Injective (dartState G) := fun _ _ h => Sum.inr_injective h

theorem startState_ne_dartState (x : V) (d : G.Dart) : startState G x ≠ dartState G d :=
  Sum.inl_ne_inr

theorem walkKernel_apply (s : G.State) : G.walkKernel s = G.stepMeasure (G.stateVertex s) := rfl

theorem deg_ne_zero (x : V) : G.deg x ≠ 0 := by
  obtain ⟨e, he⟩ := G.exists_inc x
  unfold LFMultigraph.deg
  rw [Finset.card_ne_zero]
  rcases he with h | h
  · exact ⟨(e, false), (mem_outDarts G).mpr h⟩
  · exact ⟨(e, true), (mem_outDarts G).mpr h⟩

theorem stepMeasure_eq (x : V) :
    G.stepMeasure x = (G.deg x : ℝ≥0∞)⁻¹ • ∑ d ∈ G.outDarts x, Measure.dirac (dartState G d) :=
  rfl

theorem stepMeasure_apply (x : V) (s : Set G.State) :
    G.stepMeasure x s =
      (G.deg x : ℝ≥0∞)⁻¹ * ∑ d ∈ G.outDarts x, s.indicator 1 (dartState G d) := by
  rw [stepMeasure_eq, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Measure.dirac_apply]

/-- One step from `x` charges the out-dart `d` with `(deg x)⁻¹`. -/
theorem stepMeasure_singleton_dartState {x : V} {d : G.Dart} (hd : G.dsrc d = x) :
    G.stepMeasure x {dartState G d} = (G.deg x : ℝ≥0∞)⁻¹ := by
  classical
  rw [stepMeasure_apply, Finset.sum_eq_single_of_mem d ((mem_outDarts G).mpr hd)]
  · rw [Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, mul_one]
  · intro b _ hb
    rw [Set.indicator_of_notMem]
    exact fun h => hb (dartState_injective G h)

theorem stepMeasure_singleton_dartState_pos {x : V} {d : G.Dart} (hd : G.dsrc d = x) :
    0 < G.stepMeasure x {dartState G d} := by
  rw [stepMeasure_singleton_dartState G hd]
  exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)

/-- The out-dart states of `x`. -/
def outStates (x : V) : Set G.State := {s | ∃ d : G.Dart, G.dsrc d = x ∧ s = dartState G d}

/-- One step from `x` is carried by the out-dart states of `x`. -/
theorem stepMeasure_notOut (x : V) : G.stepMeasure x (outStates G x)ᶜ = 0 := by
  rw [stepMeasure_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun d hd => ?_)
  rw [Set.indicator_of_notMem]
  simp only [Set.mem_compl_iff, not_not]
  exact ⟨d, (mem_outDarts G).mp hd, rfl⟩

/-- A path of the edge-end walk from `x`: it starts at `inl x` and each step traverses an
out-dart of the current vertex. -/
def IsWalkPath (x : V) (ω : ℕ → G.State) : Prop :=
  ω 0 = startState G x ∧ ∀ n, ω (n + 1) ∈ outStates G (G.stateVertex (ω n))

theorem ae_isWalkPath [Countable V] [Countable E] (x : V) :
    ∀ᵐ ω ∂G.walkLaw x, IsWalkPath G x ω := by
  filter_upwards [chainLaw_ae_start G.walkKernel (startState G x),
    ae_forall_succ_mem G.walkKernel (startState G x) (fun s => outStates G (G.stateVertex s))
      (fun s => stepMeasure_notOut G _)] with ω h0 hs
  exact ⟨h0, hs⟩

/-- `hitTime A` of the vertex path is the hitting time of the vertex preimage. -/
theorem hitTime_vertexPath (A : Set V) (ω : ℕ → G.State) :
    hitTime A (G.vertexPath ω) = hitTime (G.stateVertex ⁻¹' A) ω := rfl

/-- On a connected graph the walk from any state hits a nonempty `A` with positive probability
(by induction along a graph walk, using the first-step equation). -/
theorem chainLaw_hit_pos_of_walk {A : Set V} {a : V} (ha : a ∈ A) :
    ∀ (y : V) (_p : G.adj.Walk y a) (s : G.State), G.stateVertex s = y →
      0 < chainLaw G.walkKernel s {ω | hitTime (G.stateVertex ⁻¹' A) ω < ⊤} := by
  intro y p
  induction p with
  | nil =>
    intro s hs
    have hsA : s ∈ G.stateVertex ⁻¹' A := by
      simp only [Set.mem_preimage, hs]; exact ha
    rw [chainLaw_hitTime_lt_top_of_mem G.walkKernel hsA]
    exact one_pos
  | @cons y y' _ h q ih =>
    intro s hs
    by_cases hsA : s ∈ G.stateVertex ⁻¹' A
    · rw [chainLaw_hitTime_lt_top_of_mem G.walkKernel hsA]
      exact one_pos
    obtain ⟨d, hd1, hd2⟩ := exists_dart_of_adj G h
    rw [chainLaw_hitTime_lt_top_of_notMem G.walkKernel MeasurableSet.of_discrete hsA]
    refine lt_of_lt_of_le ?_ (setLIntegral_le_lintegral {dartState G d} _)
    rw [lintegral_singleton, walkKernel_apply, hs]
    exact ENNReal.mul_pos (ih ha (dartState G d) hd2).ne' (stepMeasure_singleton_dartState_pos G hd1).ne'

theorem hitProb_pos (hconn : G.adj.Connected) {A : Set V} (hA : A.Nonempty) (x : V) :
    0 < G.walkLaw x {ω | hitTime A (G.vertexPath ω) ≠ ⊤} := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨p⟩ := hconn.preconnected x a
  have := chainLaw_hit_pos_of_walk G ha x p (startState G x) rfl
  simpa only [walkLaw_eq, hitTime_vertexPath, lt_top_iff_ne_top] using this

end MatedCRTHarmonic.Harmonic
