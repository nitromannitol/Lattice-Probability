/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.HarmonicInfinity.Walk at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Entrance
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Harm
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Walk
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Disconnects
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Recurrent

/-!
# Simple random walk as a nearest-neighbour chain; recurrence

Facts for the frozen edge-end walk `G.walkLaw`.

* `G.Recurrent` (the frozen definition `LFMultigraph.Recurrent`):
  from every vertex, simple random walk hits every vertex almost surely
  (hitting form of the recurrence result; it gives a.s. hitting of every nonempty set,
  `walkLaw_hitTime_ne_top`, also from dart states, `chainLaw_hitTime_ne_top`).
* `walkTrace G F ω`: the vertices visited strictly before the first visit to `F`.
* `hitDist G I x W`: the hitting distribution of `I` from `x`.
* `isNNChain_walk`: the edge-end walk is a nearest-neighbour chain on `G.adj`, so the general
  results of `HarmonicInfinity/Chain.lean` and `HarmonicInfinity/Entrance.lean` apply;
  `hitDist_le_add`, `abs_hitDist_sub_le` are the hitting-distribution bounds for the walk.
* `entryProb A e s`: the probability that the walk from `s` visits `A` and enters it through `e`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace MatedCRTHarmonic.HarmonicInfinity

open Markov Harmonic

variable {V E : Type*} (G : LFMultigraph V E)

/-- The vertices visited by the walk strictly before its first visit to `F` (`trace_{<T_F}(X)`;
all visited vertices if `F` is never visited). -/
def walkTrace (F : Set V) (ω : ℕ → G.State) : Set V :=
  {v | ∃ m : ℕ, (m : ℕ∞) < hitTime F (G.vertexPath ω) ∧ G.vertexPath ω m = v}

/-- The hitting distribution of `I` from `x`: the probability that the walk visits `I` and first
does so at a vertex of `W`. -/
def hitDist (I : Set V) (x : V) (W : Set V) : ℝ≥0∞ :=
  G.walkLaw x {ω | hitTime I (G.vertexPath ω) ≠ ⊤ ∧
    G.vertexPath ω (hitTime I (G.vertexPath ω)).toNat ∈ W}

/-- The (unconditioned) probability, from the state `s`, that the walk visits `A` and enters it
through the edge `e`. -/
def entryProb (A : Set V) (e : E) (s : G.State) : ℝ≥0∞ :=
  chainLaw G.walkKernel s (hitEvent (G.stateVertex ⁻¹' A) {t | stateEdge G t = some e})

/-! ### The walk is a nearest-neighbour chain -/

/-- The edge-end walk is a nearest-neighbour chain on `G.adj`, with vertex map `stateVertex` and
start states `inl x`. -/
theorem isNNChain_walk : IsNNChain G.walkKernel G.stateVertex (startState G) G.adj where
  π_start _ := rfl
  kernel_eq _ := rfl
  step_null s := by
    refine measure_mono_null (fun t ht => ?_) (stepMeasure_notOut G (G.stateVertex s))
    refine fun hout => ht ?_
    obtain ⟨d, hd, rfl⟩ := hout
    have h := GoodScales.stepOK_dsrc_dtgt G d
    rw [hd] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem hitDist_eq_hitLaw (I : Set V) (x : V) (W : Set V) :
    hitDist G I x W = hitLaw G.walkKernel G.stateVertex I W (startState G x) :=
  rfl

theorem walkTrace_eq_traceBefore (F : Set V) (ω : ℕ → G.State) :
    walkTrace G F ω = traceBefore G.stateVertex F ω :=
  rfl

theorem disconnects_iff_graphSeparates (U A B : Set V) :
    G.Disconnects U A B ↔ GraphSeparates G.adj U A B :=
  Iff.rfl

/-! ### Hitting-distribution bounds for the walk -/

/-- **C3 for simple random walk** ([18, Lemma 3.10]; the recurrence argument): for all `I, W, x, y`,
`P_y(X_{T_I} ∈ W) ≤ P_x(X_{T_I} ∈ W) + (1 - P_x(walk before T_I disconnects y from I))`. -/
theorem hitDist_le_add [Countable V] (I W : Set V) (x y : V) :
    hitDist G I y W ≤ hitDist G I x W +
      (1 - G.walkLaw x {ω | G.Disconnects (walkTrace G I ω) {y} I}) := by
  have : Countable E := Harmonic.countable_edge G
  exact hitLaw_le_add (isNNChain_walk G) I W x y

/-- **C3 for simple random walk, real one-sided form** (the shape of the one-sided estimate, without its
hypotheses of connectivity, recurrence and `x, y ∉ I`). -/
theorem toReal_hitDist_sub_le [Countable V] (I W : Set V) (x y : V) :
    (hitDist G I y W).toReal - (hitDist G I x W).toReal ≤
      1 - (G.walkLaw x {ω | G.Disconnects (walkTrace G I ω) {y} I}).toReal := by
  have : Countable E := Harmonic.countable_edge G
  exact toReal_hitLaw_sub_le (isNNChain_walk G) I W x y

/-! ### Recurrence -/

/-- On a recurrent graph the walk from every vertex visits every nonempty set almost surely. -/
theorem walkLaw_hitTime_ne_top {G : LFMultigraph V E} (hrec : G.Recurrent) {I : Set V}
    (hI : I.Nonempty) (x : V) : G.walkLaw x {ω | hitTime I (G.vertexPath ω) ≠ ⊤} = 1 := by
  obtain ⟨y, hy⟩ := hI
  refine le_antisymm prob_le_one ?_
  rw [← hrec x y]
  exact measure_mono fun ω hω =>
    ne_top_of_le_ne_top hω (hitTime_anti (Set.singleton_subset_iff.mpr hy) _)

/-- On a recurrent graph the walk from every state visits every nonempty set almost surely. -/
theorem chainLaw_hitTime_ne_top {G : LFMultigraph V E} (hrec : G.Recurrent) {I : Set V}
    (hI : I.Nonempty) (s : G.State) :
    chainLaw G.walkKernel s {ω | hitTime (G.stateVertex ⁻¹' I) ω ≠ ⊤} = 1 := by
  have h := chainLaw_vertexEvent (isNNChain_walk G) s (Q := fun X => hitTime I X ≠ ⊤)
    (measurableSet_hitTime_eq_top (A := G.stateVertex ⁻¹' I) MeasurableSet.of_discrete).compl
  exact h.trans (walkLaw_hitTime_ne_top hrec hI _)

/-- **C3 for simple random walk, total-variation form** (recurrent graphs, nonempty `I`):
`|P_x(X_{T_I} ∈ W) - P_y(X_{T_I} ∈ W)| ≤ 1 - P_x(walk before T_I disconnects y from I)`. -/
theorem abs_hitDist_sub_le [Countable V] {G : LFMultigraph V E} (hrec : G.Recurrent) {I : Set V}
    (hI : I.Nonempty) (W : Set V) (x y : V) :
    |(hitDist G I x W).toReal - (hitDist G I y W).toReal| ≤
      1 - (G.walkLaw x {ω | G.Disconnects (walkTrace G I ω) {y} I}).toReal := by
  have : Countable E := Harmonic.countable_edge G
  exact abs_hitLaw_sub_le (isNNChain_walk G) I W (chainLaw_hitTime_ne_top hrec hI _)
    (chainLaw_hitTime_ne_top hrec hI _)

/-! ### The entry-edge law -/

theorem entryProb_le_one (A : Set V) (e : E) (s : G.State) : entryProb G A e s ≤ 1 :=
  prob_le_one

/-! ### The entrance decomposition for the walk -/

/-- **(M2) for the entry-edge law** (the recurrence argument, C4 step (i)): if `A ⊆ B`, the inner boundary of
`B` avoids `A` and `x ∉ B`, then
`P_x(enter A through e) = ∑_w P_x(X_{T_B} = w) · P_w(enter A through e)`. -/
theorem entryProb_eq_tsum [Countable V] {A B : Set V} (hAB : A ⊆ B)
    (hbd : ∀ w ∈ innerBoundary G.adj B, w ∉ A) (e : E) {x : V} (hx : x ∉ B) :
    entryProb G A e (startState G x) =
      ∑' w, hitDist G B x {w} * entryProb G A e (startState G w) := by
  have : Countable E := Harmonic.countable_edge G
  exact chainLaw_hitEvent_eq_tsum (isNNChain_walk G) hAB hbd _ (s := startState G x) hx

/-- From `x ∉ B` the walk enters `B` through its inner boundary. -/
theorem hitDist_singleton_eq_zero [Countable V] {B : Set V} {x : V} (hx : x ∉ B) {w : V}
    (hw : w ∉ innerBoundary G.adj B) : hitDist G B x {w} = 0 := by
  have : Countable E := Harmonic.countable_edge G
  exact hitLaw_singleton_eq_zero (isNNChain_walk G) (s := startState G x) hx hw

/-- On a recurrent graph the hitting distribution of a nonempty set has total mass one. -/
theorem tsum_hitDist_singleton [Countable V] {G : LFMultigraph V E} (hrec : G.Recurrent)
    {B : Set V} (hB : B.Nonempty) (x : V) : ∑' w, hitDist G B x {w} = 1 :=
  (tsum_hitLaw_singleton B (startState G x)).trans (walkLaw_hitTime_ne_top hrec hB x)

theorem hitDist_eq_sum (B : Set V) (x : V) (W : Finset V) :
    hitDist G B x W = ∑ w ∈ W, hitDist G B x {w} :=
  hitLaw_eq_sum B W (startState G x)

end MatedCRTHarmonic.HarmonicInfinity
