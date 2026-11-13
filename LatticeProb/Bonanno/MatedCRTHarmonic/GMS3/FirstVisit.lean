/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.FirstVisit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Recurrence

/-!
# Where the walk first visits a set: a deterministic path criterion

The probabilistic step of the maximum principle in GMS [18] Lemma 3.8 ([18]: "by the maximum
principle for the discrete harmonic function `f^s_ε`"), in the form of
a restart at a hitting time ((M1), `hitLaw_eq_setLIntegral`):

* `hitDist_le_of_firstVisit`: let `I ⊆ B`. If every finite walk from `x` (consecutive vertices equal or
  adjacent) whose first visit to `B` happens at its last vertex ends in `G'`, and
  `P_y(X_{T_I} ∈ W) ≤ M` for every `y ∈ G'`, then `P_x(X_{T_I} ∈ W) ≤ M`.
* `hitTime_ne_top_of_firstVisit`: if moreover every walk from `x` that ends outside the finite set `U` visits
  `I` on the way, and every vertex of `U` is connected to a vertex outside `U`, then `I` is visited a.s.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace MatedCRTHarmonic.GMS3

open Markov Harmonic HarmonicInfinity LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- A finite walk of vertices: consecutive vertices are equal or adjacent. -/
def IsStepPath (n : ℕ) (X : ℕ → V) : Prop := ∀ j < n, X (j + 1) = X j ∨ G.adj.Adj (X j) (X (j + 1))

/-- Almost surely the vertex path of the walk from `x` starts at `x` and moves along `G.adj`. -/
theorem ae_isStepPath (hconn : G.adj.Connected) (x : V) :
    ∀ᵐ ω ∂G.walkLaw x, G.stateVertex (ω 0) = x ∧ ∀ n, IsStepPath G n (G.vertexPath ω) := by
  have : Countable V := countable_of_connected G hconn
  have : Countable E := countable_edge G
  filter_upwards [ae_step (isNNChain_walk G) (startState G x)] with ω ⟨h0, hstep⟩
  exact ⟨by rw [h0]; rfl, fun n j _ => hstep j⟩

/-- **The first visit to `B` lies in `G'`**, hence the hitting distribution of `I ⊆ B` is controlled by
its values on `G'` (restart at `T_B`). -/
theorem hitDist_le_of_firstVisit (hconn : G.adj.Connected) {I B G' W : Set V} (hIB : I ⊆ B)
    {x : V} {M : ℝ} (hval : ∀ y ∈ G', hitDist G I y W ≤ ENNReal.ofReal M)
    (hpath : ∀ (n : ℕ) (X : ℕ → V), X 0 = x → IsStepPath G n X → X n ∈ B →
      (∀ j < n, X j ∉ B) → X n ∈ G') :
    hitDist G I x W ≤ ENNReal.ofReal M := by
  rw [hitDist_eq_hitLaw, hitLaw_eq_setLIntegral (isNNChain_walk G) hIB W (startState G x)]
  calc ∫⁻ ω in {ω | hitTime (G.stateVertex ⁻¹' B) ω < ⊤},
        hitLaw G.walkKernel G.stateVertex I W
          (startState G (G.stateVertex (stopState (hitTime (G.stateVertex ⁻¹' B)) ω)))
          ∂chainLaw G.walkKernel (startState G x)
      ≤ ∫⁻ _ in {ω | hitTime (G.stateVertex ⁻¹' B) ω < ⊤}, ENNReal.ofReal M
          ∂chainLaw G.walkKernel (startState G x) := by
        refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
        filter_upwards [ae_isStepPath G hconn x] with ω ⟨h0, hstep⟩ hT
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (lt_top_iff_ne_top.mp hT)
        have hmem := hitTime_eq_coe_iff.mp hn.symm
        rw [stopState_eq_of_eq hn.symm]
        refine hval _ (hpath n (G.vertexPath ω) h0 (hstep n) hmem.1 fun j hj => hmem.2 j hj)
    _ ≤ ENNReal.ofReal M := by
        rw [setLIntegral_const]
        exact mul_le_of_le_one_right' prob_le_one

/-- **The walk visits `I` almost surely** if every walk from `x` leaving the finite set `U` visits `I`
(and every vertex of `U` connects to a vertex outside `U`). -/
theorem walkLaw_hitTime_ne_top_of_exit (hconn : G.adj.Connected) {U : Set V} (hU : U.Finite)
    (hesc : ∀ y ∈ U, ∃ w, w ∉ U ∧ G.adj.Reachable y w) {I : Set V} {x : V}
    (hpath : ∀ (n : ℕ) (X : ℕ → V), X 0 = x → IsStepPath G n X → X n ∉ U → ∃ j ≤ n, X j ∈ I) :
    G.walkLaw x {ω | hitTime I (G.vertexPath ω) ≠ ⊤} = 1 := by
  refine le_antisymm prob_le_one ?_
  rw [← walkLaw_hitTime_compl_ne_top G hU hesc x]
  refine measure_mono_ae ?_
  filter_upwards [ae_isStepPath G hconn x] with ω ⟨h0, hstep⟩ hω
  obtain ⟨n, hn⟩ := (hitTime_ne_top_iff).mp hω
  obtain ⟨j, -, hj⟩ := hpath n (G.vertexPath ω) h0 (hstep n) hn
  exact (hitTime_ne_top_iff).mpr ⟨j, hj⟩

end MatedCRTHarmonic.GMS3
