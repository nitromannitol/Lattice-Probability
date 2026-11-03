/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GoodScales.Walk at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.Chain
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dsrc
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dtgt
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.OutDarts
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Deg
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateVertex
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasureIsProbability
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkKernel
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkKernelIsMarkov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsPlaneData

/-!
# Walk-level facts for the good-scales estimate

* countability: plane data make `V` countable, hence `E` and the edge-end state space are countable;
* measurability of path events determined by finitely many coordinates (countable state space);
* the vertex path of simple random walk moves along edges almost surely (`ae_stepOK`);
* the law of a vertex-path event only depends on the start vertex of the starting state
  (`chainLaw_vertexEvent_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GoodScales

open Markov

variable {V E : Type*}

/-! ### Countability -/

/-- Plane data (a locally finite family of nonempty sets in `ℂ`) make the vertex set countable. -/
theorem countable_of_isPlaneData {G : LFMultigraph V E} {J : V → Set ℂ}
    (hJ : G.IsPlaneData J) : Countable V :=
  Set.countable_univ_iff.mp
    (hJ.locallyFinite.countable_univ fun x => (hJ.isConnected x).nonempty)

/-- A locally finite multigraph on a countable vertex set has countably many edges. -/
theorem countable_edge (G : LFMultigraph V E) [Countable V] : Countable E := by
  have h : (Set.univ : Set E) ⊆ ⋃ x : V, {e : E | G.src e = x ∨ G.tgt e = x} := fun e _ =>
    Set.mem_iUnion.mpr ⟨G.src e, Or.inl rfl⟩
  exact Set.countable_univ_iff.mp
    ((Set.countable_iUnion fun x => (G.finite_inc x).countable).mono h)

/-- The edge-end state space of a locally finite multigraph on a countable vertex set is
countable. -/
theorem countable_state (G : LFMultigraph V E) [Countable V] : Countable G.State := by
  have := countable_edge G
  exact inferInstanceAs (Countable (V ⊕ (E × Bool)))

/-- The law of simple random walk is a probability measure. -/
instance isProbabilityMeasure_walkLaw (G : LFMultigraph V E) (x : V) :
    IsProbabilityMeasure (G.walkLaw x) := by
  unfold LFMultigraph.walkLaw
  infer_instance

/-! ### Measurability of finitely determined path events -/

/-- On a countable state space with measurable singletons, an event of paths determined by the
coordinates up to time `n` is measurable. -/
theorem measurableSet_of_forall_eq_le {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] {B : Set (ℕ → S)} (n : ℕ)
    (h : ∀ ω ω' : ℕ → S, (∀ m ≤ n, ω m = ω' m) → ω ∈ B → ω' ∈ B) : MeasurableSet B := by
  have hB : B = Preorder.frestrictLe n ⁻¹' (Preorder.frestrictLe n '' B) := by
    ext ω
    constructor
    · intro hω
      exact ⟨ω, hω, rfl⟩
    · rintro ⟨ω', hω', heq⟩
      refine h ω' ω (fun m hm => ?_) hω'
      have := congrFun heq ⟨m, Finset.mem_Iic.mpr hm⟩
      simpa [Preorder.frestrictLe_apply] using this
  rw [hB]
  exact Preorder.measurable_frestrictLe n MeasurableSet.of_discrete

/-! ### Steps of the walk -/

/-- A step of the vertex path from `x` to `y` is admissible: it stays (a loop) or moves to a
neighbour. -/
def StepOK (G : LFMultigraph V E) (x y : V) : Prop := y = x ∨ G.adj.Adj x y

/-- A dart joins its two ends: they are equal (a loop) or adjacent. -/
theorem stepOK_dsrc_dtgt (G : LFMultigraph V E) (d : G.Dart) : StepOK G (G.dsrc d) (G.dtgt d) := by
  by_cases h : G.dtgt d = G.dsrc d
  · exact Or.inl h
  · refine Or.inr ?_
    rw [LFMultigraph.adj, SimpleGraph.fromRel_adj]
    refine ⟨Ne.symm h, ?_⟩
    rcases d with ⟨e, b⟩
    cases b
    · exact Or.inl ⟨e, by simp [LFMultigraph.dsrc], by simp [LFMultigraph.dtgt]⟩
    · exact Or.inr ⟨e, by simp [LFMultigraph.dtgt], by simp [LFMultigraph.dsrc]⟩

theorem mem_outDarts {G : LFMultigraph V E} {x : V} {d : G.Dart} (h : d ∈ G.outDarts x) :
    G.dsrc d = x := by
  classical
  unfold LFMultigraph.outDarts at h
  exact (Finset.mem_filter.mp h).2

/-- One step of simple random walk from `x` never lands at a state whose vertex is not `x` or a
neighbour of `x`. -/
theorem stepMeasure_singleton_eq_zero (G : LFMultigraph V E) (x : V) (s : G.State)
    (h : ¬ StepOK G x (G.stateVertex s)) : G.stepMeasure x {s} = 0 := by
  rw [LFMultigraph.stepMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  have hz : ∀ d ∈ G.outDarts x, (Measure.dirac (show G.State from Sum.inr d)) {s} = 0 := by
    intro d hd
    rw [Measure.dirac_apply' _ (measurableSet_singleton s)]
    refine Set.indicator_of_notMem (fun hds => h ?_) _
    have hs : s = Sum.inr d := (Set.mem_singleton_iff.mp hds).symm
    subst hs
    have h1 := stepOK_dsrc_dtgt G d
    rwa [mem_outDarts hd] at h1
  rw [Finset.sum_eq_zero hz, smul_zero]

/-- The kernel of the edge-end walk at `s` is the step measure at the vertex of `s`. -/
theorem walkKernel_apply (G : LFMultigraph V E) (s : G.State) :
    G.walkKernel s = G.stepMeasure (G.stateVertex s) := rfl

/-- **The vertex path of simple random walk moves along edges** almost surely. -/
theorem ae_stepOK (G : LFMultigraph V E) [Countable G.State] (s₀ : G.State) :
    ∀ᵐ ω ∂chainLaw G.walkKernel s₀, ∀ n,
      StepOK G (G.vertexPath ω n) (G.vertexPath ω (n + 1)) := by
  refine ae_all_iff.mpr fun n => ?_
  rw [ae_iff]
  have hsub : {ω : ℕ → G.State | ¬ StepOK G (G.vertexPath ω n) (G.vertexPath ω (n + 1))} ⊆
      ⋃ q : G.State × G.State, {ω | ¬ StepOK G (G.stateVertex q.1) (G.stateVertex q.2) ∧
        (ω n = q.1 ∧ ω (n + 1) = q.2)} := by
    intro ω hω
    exact Set.mem_iUnion.mpr ⟨(ω n, ω (n + 1)), hω, rfl, rfl⟩
  refine measure_mono_null hsub (measure_iUnion_null fun q => ?_)
  by_cases hq : StepOK G (G.stateVertex q.1) (G.stateVertex q.2)
  · simp [hq]
  · have h0 : chainLaw G.walkKernel s₀ {ω | ω n = q.1 ∧ ω (n + 1) = q.2} = 0 := by
      rw [chainLaw_eval_eq_eval_succ_eq, walkKernel_apply,
        stepMeasure_singleton_eq_zero G _ _ hq, mul_zero]
    refine measure_mono_null (fun ω hω => ?_) h0
    exact hω.2

/-- The walk started at `s₀` starts at `s₀` and moves along edges, almost surely. -/
theorem ae_start_and_stepOK (G : LFMultigraph V E) [Countable G.State] (s₀ : G.State) :
    ∀ᵐ ω ∂chainLaw G.walkKernel s₀, ω 0 = s₀ ∧ ∀ n,
      StepOK G (G.vertexPath ω n) (G.vertexPath ω (n + 1)) := by
  filter_upwards [chainLaw_ae_start G.walkKernel s₀, ae_stepOK G s₀] with ω h1 h2
  exact ⟨h1, h2⟩

/-! ### Vertex-path events only depend on the start vertex -/

theorem vertexPath_consPath_eq {G : LFMultigraph V E} {s s' : G.State}
    (h : G.stateVertex s = G.stateVertex s') (q : ℕ → G.State) :
    G.vertexPath (consPath s q) = G.vertexPath (consPath s' q) := by
  funext n
  cases n with
  | zero => exact h
  | succ k => rfl

/-- The probability of an event of the vertex path only depends on the vertex of the starting
state: the kernel at a state only depends on its vertex, and so does the vertex path at time `0`. -/
theorem chainLaw_vertexEvent_eq (G : LFMultigraph V E) {s s' : G.State}
    (h : G.stateVertex s = G.stateVertex s') {Q : (ℕ → V) → Prop}
    (hQ : MeasurableSet {ω : ℕ → G.State | Q (G.vertexPath ω)}) :
    chainLaw G.walkKernel s {ω | Q (G.vertexPath ω)} =
      chainLaw G.walkKernel s' {ω | Q (G.vertexPath ω)} := by
  rw [chainLaw_apply_eq_lintegral_consPath _ s hQ, chainLaw_apply_eq_lintegral_consPath _ s' hQ]
  have hk : G.walkKernel s = G.walkKernel s' := by
    rw [walkKernel_apply, walkKernel_apply, h]
  have hpre : consPath s ⁻¹' {ω : ℕ → G.State | Q (G.vertexPath ω)} =
      consPath s' ⁻¹' {ω : ℕ → G.State | Q (G.vertexPath ω)} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, vertexPath_consPath_eq h q]
  rw [hk, hpre]

end MatedCRTHarmonic.GoodScales
