/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.WaypointWalk at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Walk
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.Chain

/-!
# Almost-sure strict steps for loopless edge-end walks
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic
open MatedCRTHarmonic.GoodScales
open MatedCRTHarmonic.Markov

variable {E : Type*}

/-- In a loopless multigraph, one transition of the edge-end walk cannot keep the same vertex. -/
theorem waypoint_stepMeasure_no_stay (G : LFMultigraph ℤ E)
    (hloop : ∀ e : E, G.src e ≠ G.tgt e) (x : ℤ) :
    G.stepMeasure x {s | G.stateVertex s = x} = 0 := by
  classical
  rw [LFMultigraph.stepMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  have hz : ∀ d ∈ G.outDarts x,
      (Measure.dirac (show G.State from Sum.inr d)) {s | G.stateVertex s = x} = 0 := by
    intro d hd
    have hsrc : G.dsrc d = x := mem_outDarts hd
    have htgt : G.dtgt d ≠ x := by
      rcases d with ⟨e, b⟩
      cases b with
      | false =>
          simp only [LFMultigraph.dsrc, Bool.false_eq_true, ↓reduceIte] at hsrc
          simp only [LFMultigraph.dtgt, Bool.false_eq_true, ↓reduceIte]
          exact fun h => hloop e (hsrc.trans h.symm)
      | true =>
          simp only [LFMultigraph.dsrc, ↓reduceIte] at hsrc
          simp only [LFMultigraph.dtgt, ↓reduceIte]
          exact fun h => hloop e (h.trans hsrc.symm)
    rw [Measure.dirac_apply' _ MeasurableSet.of_discrete]
    have hnot : (Sum.inr d : LFMultigraph.State G) ∉ {s | G.stateVertex s = x} := by
      change G.dtgt d ≠ x
      exact htgt
    change (if (Sum.inr d : G.State) ∈ {s | G.stateVertex s = x}
      then (1 : ℝ≥0∞) else 0) = 0
    simp [hnot]
  rw [Finset.sum_eq_zero hz, smul_zero]

/-- The transition kernel puts no mass on states with the current vertex. -/
theorem waypoint_walkKernel_no_stay (G : LFMultigraph ℤ E)
    (hloop : ∀ e : E, G.src e ≠ G.tgt e) (s : G.State) :
    G.walkKernel s {t | G.stateVertex t = G.stateVertex s} = 0 := by
  rw [GoodScales.walkKernel_apply]
  exact waypoint_stepMeasure_no_stay G hloop (G.stateVertex s)

/-- Almost surely every vertex transition of the walk is a strict graph edge. -/
theorem waypoint_walkLaw_ae_adj {G : LFMultigraph ℤ E} [Countable (LFMultigraph.State G)]
    (hloop : ∀ e : E, G.src e ≠ G.tgt e) (x : ℤ) :
    ∀ᵐ ξ ∂G.walkLaw x, ∀ j, G.adj.Adj (G.vertexPath ξ j) (G.vertexPath ξ (j + 1)) := by
  have hnostay : ∀ᵐ ξ ∂G.walkLaw x,
      ∀ j, G.vertexPath ξ j ≠ G.vertexPath ξ (j + 1) := by
    refine ae_all_iff.mpr fun j => ?_
    rw [ae_iff]
    change G.walkLaw x {ξ | ¬ G.vertexPath ξ j ≠ G.vertexPath ξ (j + 1)} = 0
    rw [show {ξ : ℕ → LFMultigraph.State G | ¬ G.vertexPath ξ j ≠ G.vertexPath ξ (j + 1)} =
        {ξ | G.vertexPath ξ j = G.vertexPath ξ (j + 1)} by ext; simp]
    change chainLaw G.walkKernel (Sum.inl x)
      {ξ | G.vertexPath ξ j = G.vertexPath ξ (j + 1)} = 0
    have hsub : {ξ : ℕ → LFMultigraph.State G | G.vertexPath ξ j = G.vertexPath ξ (j + 1)} ⊆
        ⋃ p : LFMultigraph.State G × LFMultigraph.State G,
      {ξ | ξ j = p.1 ∧ ξ (j + 1) = p.2 ∧ G.stateVertex p.1 = G.stateVertex p.2} := by
      intro ξ hξ
      refine Set.mem_iUnion.mpr ⟨(ξ j, ξ (j + 1)), ?_⟩
      exact ⟨rfl, rfl, by simpa [LFMultigraph.vertexPath] using hξ⟩
    refine measure_mono_null hsub (measure_iUnion_null fun p => ?_)
    have hzero : chainLaw G.walkKernel (show G.State from Sum.inl x)
        {ξ | ξ j = p.1 ∧ ξ (j + 1) = p.2 ∧ G.stateVertex p.1 = G.stateVertex p.2} = 0 := by
      by_cases heq : G.stateVertex p.1 = G.stateVertex p.2
      · have hsing : G.walkKernel p.1 {p.2} = 0 := by
          refine measure_mono_null (s := {p.2})
            (t := {t | G.stateVertex t = G.stateVertex p.1}) ?_
            (waypoint_walkKernel_no_stay G hloop p.1)
          · intro t ht
            simp only [Set.mem_singleton_iff] at ht
            subst t
            change G.stateVertex p.2 = G.stateVertex p.1
            exact heq.symm
        have hset : {ξ : ℕ → G.State | ξ j = p.1 ∧ ξ (j + 1) = p.2 ∧
            G.stateVertex p.1 = G.stateVertex p.2} =
            {ξ | ξ j = p.1 ∧ ξ (j + 1) = p.2} := by
          ext ξ
          simp [heq]
        rw [hset, chainLaw_eval_eq_eval_succ_eq, hsing, mul_zero]
      · have hempty : {ξ : ℕ → G.State | ξ j = p.1 ∧ ξ (j + 1) = p.2 ∧
            G.stateVertex p.1 = G.stateVertex p.2} = ∅ := by
          ext ξ
          simp [heq]
        rw [hempty, measure_empty]
    refine measure_mono_null (fun ξ hξ => ?_) hzero
    exact ⟨hξ.1, hξ.2.1, hξ.2.2⟩
  filter_upwards [hnostay, GoodScales.ae_stepOK G (Sum.inl x)] with ξ hne hstep
  intro j
  rcases hstep j with hstay | hadj
  · exact False.elim (hne j hstay.symm)
  · exact hadj

end MatedCRTHarmonic.CellFamily

