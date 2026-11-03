/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.HarmonicInfinity.Chain at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.StrongMarkov
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Walk

/-!
# Hitting distributions of nearest-neighbour chains and separation

A maximum-principle proof of [18, Lemma 3.10] = [19, Lemma 3.12] that avoids Wilson's algorithm.

Setting (`IsNNChain κ π start Γ`): a Markov chain with kernel `κ` on a countable discrete state
space `S`, a vertex map `π : S → V`, a section `start : V → S` of `π` (the chain "started at the
vertex `v`" is `chainLaw κ (start v)`), and a simple graph `Γ` on `V`, such that the one-step law
from a state only depends on its vertex and every step stays at the same vertex or moves to a
`Γ`-neighbour. No reversibility, recurrence or connectivity is assumed. The edge-end walk of an
`LFMultigraph` is the instance `HarmonicInfinity.isNNChain_walk` (`HarmonicInfinity/Walk.lean`).

* `hitEvent I Z`: the chain visits the set of states `I`, and the state at the first visit lies in
  `Z`; `hitLaw κ π I W s` is the probability from `s` that the first visit to the vertex set `I`
  happens at a vertex of `W` (the hitting distribution of `I`).
* `chainLaw_hitEvent_eq_setLIntegral` (**(M1)**, restart at an earlier hitting time): if `I ⊆ B`,
  `P_s(hitEvent I Z) = ∫_{T_B < ⊤} P_{X_{T_B}}(hitEvent I Z) dP_s`.
* `chainLaw_vertexEvent`, `chainLaw_hitEvent_eq_of_notMem`: path events of the vertex path, and
  hitting events of `A` from states outside `A`, only depend on the vertex of the starting state.
* `exists_walk_hitLaw_le` (**C2**, superlevel path): if `g(y) = hitLaw(start y) > 0`, there is a
  `Γ`-walk from `y` to some `a ∈ I` along which `g ≥ g(y)`.
* `hitLaw_le_add` (**C3**, the TV bound by the separation probability): for every `W`,
  `P_y(X_{T_I} ∈ W) ≤ P_x(X_{T_I} ∈ W) + (1 - P_x(D))`, where `D` is the event that the vertices
  visited strictly before `T_I` separate `{y}` from `I` in `Γ`; `abs_hitLaw_sub_le` is the
  two-sided (total-variation) form when `I` is hit almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace MatedCRTHarmonic.HarmonicInfinity

open Markov

/-! ### Separation, traces and hitting events -/

section Defs

variable {S V : Type*}

/-- `U` separates `A` from `B` in the graph `Γ`: every `Γ`-walk from a vertex of `A` to a vertex
of `B` visits `U` (the frozen `LFMultigraph.Disconnects` is the case `Γ = G.adj`). -/
def GraphSeparates (Γ : SimpleGraph V) (U A B : Set V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ w : Γ.Walk a b, ∃ y ∈ w.support, y ∈ U

/-- The vertices visited strictly before the first visit to the vertex set `I`
(`trace_{<T_I}(X)` of the recurrence argument; all visited vertices if `I` is never visited). -/
def traceBefore (π : S → V) (I : Set V) (ω : ℕ → S) : Set V :=
  {v | ∃ m : ℕ, (m : ℕ∞) < hitTime (π ⁻¹' I) ω ∧ π (ω m) = v}

/-- The path visits the set of states `I`, and the state at its first visit lies in `Z`. -/
def hitEvent (I Z : Set S) : Set (ℕ → S) :=
  {ω | hitTime I ω ≠ ⊤ ∧ stopState (hitTime I) ω ∈ Z}

variable [MeasurableSpace S]

/-- The hitting distribution of the vertex set `I` from the state `s`: the probability that the
chain visits `I` and its first visit is at a vertex of `W`. -/
def hitLaw (κ : Kernel S S) [IsMarkovKernel κ] (π : S → V) (I W : Set V) (s : S) : ℝ≥0∞ :=
  chainLaw κ s (hitEvent (π ⁻¹' I) (π ⁻¹' W))

/-- A **nearest-neighbour chain** on the graph `Γ`: the kernel at a state only depends on its
vertex, `start` is a section of the vertex map, and each step stays at the current vertex or
moves to a `Γ`-neighbour (with probability one). -/
structure IsNNChain (κ : Kernel S S) (π : S → V) (start : V → S) (Γ : SimpleGraph V) : Prop where
  /-- `start v` is a state at the vertex `v`. -/
  π_start : ∀ v, π (start v) = v
  /-- The one-step law only depends on the current vertex. -/
  kernel_eq : ∀ s, κ s = κ (start (π s))
  /-- Each step stays at the current vertex or moves to a neighbour. -/
  step_null : ∀ s, κ s {t | π t = π s ∨ Γ.Adj (π s) (π t)}ᶜ = 0

end Defs

/-! ### Pure path facts -/

section PathFacts

variable {S : Type*}

/-- Hitting times are antitone in the target set. -/
theorem hitTime_anti {A B : Set S} (hAB : A ⊆ B) (ω : ℕ → S) : hitTime B ω ≤ hitTime A ω :=
  le_hitTime_iff.mpr fun _ hn => hitTime_le_of_mem (hAB hn)

/-- If `I` is not visited before time `n`, the path visits `I` with first-visit state in `Z` iff
the path shifted by `n` does. -/
theorem mem_hitEvent_iff_walkShift {I Z : Set S} {ω : ℕ → S} {n : ℕ}
    (hn : (n : ℕ∞) ≤ hitTime I ω) : ω ∈ hitEvent I Z ↔ walkShift n ω ∈ hitEvent I Z := by
  have key := hitTime_eq_add_hitTime_walkShift (A := I) hn
  have hiff : hitTime I ω ≠ ⊤ ↔ hitTime I (walkShift n ω) ≠ ⊤ := by
    rw [key]
    exact ⟨fun h h' => h (by rw [h', add_top]), fun h h' =>
      h (WithTop.add_eq_top.mp h' |>.resolve_left (ENat.natCast_ne_top n))⟩
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := hiff.mp h1
    refine ⟨h1', ?_⟩
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h1'
    have hst : stopState (hitTime I) ω = ω (n + k) := by
      rw [stopState_eq_of_eq (n := n + k) (by rw [key, ← hk]; push_cast; rfl)]
    rw [stopState_eq_of_eq hk.symm, walkShift_apply, ← hst]
    exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨hiff.mpr h1, ?_⟩
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h1
    have hst : stopState (hitTime I) ω = ω (n + k) := by
      rw [stopState_eq_of_eq (n := n + k) (by rw [key, ← hk]; push_cast; rfl)]
    rw [hst]
    rw [stopState_eq_of_eq hk.symm, walkShift_apply] at h2
    exact h2

/-- **Restart identity (set form).** If `I ⊆ B`, the event "the first visit to `I` is in `Z`" is
the event "`B` is visited, and the path restarted at `T_B` first visits `I` in `Z`". -/
theorem hitEvent_eq_inter_stopShift {I B : Set S} (hIB : I ⊆ B) (Z : Set S) :
    hitEvent I Z = {ω | hitTime B ω < ⊤} ∩ stopShift (hitTime B) ⁻¹' hitEvent I Z := by
  ext ω
  have hle := hitTime_anti hIB ω
  constructor
  · intro h
    have hlt : hitTime B ω < ⊤ := lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr h.1)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hlt.ne
    refine ⟨hlt, ?_⟩
    rw [Set.mem_preimage, stopShift_eq_of_eq hn.symm]
    exact (mem_hitEvent_iff_walkShift (hn ▸ hle)).mp h
  · rintro ⟨hlt, h⟩
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (show hitTime B ω < ⊤ from hlt).ne
    rw [Set.mem_preimage, stopShift_eq_of_eq hn.symm] at h
    exact (mem_hitEvent_iff_walkShift (hn ▸ hle)).mpr h

/-- Prepending a state outside `I` does not change the hitting event of `I`. -/
theorem consPath_mem_hitEvent_iff {I Z : Set S} {t : S} (ht : t ∉ I) (q : ℕ → S) :
    consPath t q ∈ hitEvent I Z ↔ q ∈ hitEvent I Z := by
  have h1 : (1 : ℕ∞) ≤ hitTime I (consPath t q) := by
    rw [hitTime_consPath_of_notMem ht]
    exact le_add_self
  have := mem_hitEvent_iff_walkShift (I := I) (Z := Z) (ω := consPath t q) (n := 1)
    (by exact_mod_cast h1)
  rwa [walkShift_one_consPath] at this

end PathFacts

/-! ### Measurability -/

section Measurability

variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem measurableSet_hitEvent (I Z : Set S) : MeasurableSet (hitEvent I Z) :=
  (measurableSet_hitTime_eq_top (A := I) MeasurableSet.of_discrete).compl.inter
    (measurable_stopState (measurable_hitTime (A := I) MeasurableSet.of_discrete)
      MeasurableSet.of_discrete)

theorem measurableSet_hitTime_lt_top' (B : Set S) :
    MeasurableSet {ω : ℕ → S | hitTime B ω < ⊤} :=
  measurableSet_hitTime_lt_top (A := B) MeasurableSet.of_discrete

theorem measurable_stopState_hitTime (B : Set S) : Measurable (stopState (hitTime B) (S := S)) :=
  measurable_stopState (measurable_hitTime (A := B) MeasurableSet.of_discrete)

end Measurability

/-! ### The restart identity (M1) and state independence -/

section Markov

variable {S V : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (κ : Kernel S S) [IsMarkovKernel κ]

/-- **(M1) Restart at an earlier hitting time** (strong Markov property at `T_B`): if `I ⊆ B`,
`P_z(hitEvent I Z) = ∫_{T_B < ⊤} P_{X_{T_B}}(hitEvent I Z) dP_z`. No finiteness of `T_B` is
assumed. -/
theorem chainLaw_hitEvent_eq_setLIntegral (z : S) {I B : Set S} (hIB : I ⊆ B) (Z : Set S) :
    chainLaw κ z (hitEvent I Z) =
      ∫⁻ ω in {ω | hitTime B ω < ⊤}, chainLaw κ (stopState (hitTime B) ω) (hitEvent I Z)
        ∂chainLaw κ z := by
  conv_lhs => rw [hitEvent_eq_inter_stopShift hIB Z]
  exact chainLaw_lt_top_inter_stopShift_preimage κ z
    (isStoppingTime_hitTime (A := B) MeasurableSet.of_discrete) (measurableSet_hitEvent I Z)

/-- Two starting states with the same one-step law and the same first-step preimage of an event
give the event the same probability. -/
theorem chainLaw_eq_of_consPath_preimage_eq {s s' : S} (hk : κ s = κ s') {F : Set (ℕ → S)}
    (hF : MeasurableSet F) (hpre : consPath s ⁻¹' F = consPath s' ⁻¹' F) :
    chainLaw κ s F = chainLaw κ s' F := by
  rw [chainLaw_apply_eq_lintegral_consPath κ s hF, chainLaw_apply_eq_lintegral_consPath κ s' hF,
    hk, hpre]

variable {κ} {π : S → V} {start : V → S} {Γ : SimpleGraph V}

/-- Events of the vertex path only depend on the vertex of the starting state. -/
theorem chainLaw_vertexEvent (hc : IsNNChain κ π start Γ) (s : S) {Q : (ℕ → V) → Prop}
    (hQ : MeasurableSet {ω : ℕ → S | Q fun n => π (ω n)}) :
    chainLaw κ s {ω | Q fun n => π (ω n)} = chainLaw κ (start (π s)) {ω | Q fun n => π (ω n)} := by
  refine chainLaw_eq_of_consPath_preimage_eq κ (hc.kernel_eq s) hQ ?_
  have hX : ∀ q : ℕ → S, (fun n => π (consPath s q n)) =
      fun n => π (consPath (start (π s)) q n) := by
    intro q
    funext n
    cases n with
    | zero => exact (hc.π_start (π s)).symm
    | succ k => rfl
  ext q
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hX q]

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- The hitting event of the vertex set `I` is an event of the vertex path. -/
theorem hitEvent_preimage_eq (I W : Set V) :
    hitEvent (π ⁻¹' I) (π ⁻¹' W) =
      {ω : ℕ → S | (fun X : ℕ → V => hitTime I X ≠ ⊤ ∧ X (hitTime I X).toNat ∈ W)
        fun n => π (ω n)} :=
  rfl

/-- The hitting distribution from a state is the hitting distribution from its vertex. -/
theorem hitLaw_eq_start (hc : IsNNChain κ π start Γ) (I W : Set V) (s : S) :
    hitLaw κ π I W s = hitLaw κ π I W (start (π s)) := by
  unfold hitLaw
  rw [hitEvent_preimage_eq]
  exact chainLaw_vertexEvent hc s (Q := fun X => hitTime I X ≠ ⊤ ∧ X (hitTime I X).toNat ∈ W)
    (measurableSet_hitEvent (π ⁻¹' I) (π ⁻¹' W))

/-- From a state outside `A`, the probability of a hitting event of `A` only depends on the vertex
of the starting state. -/
theorem chainLaw_hitEvent_eq_of_notMem (hc : IsNNChain κ π start Γ) {A : Set V} (Z : Set S)
    {s : S} (hs : π s ∉ A) :
    chainLaw κ s (hitEvent (π ⁻¹' A) Z) = chainLaw κ (start (π s)) (hitEvent (π ⁻¹' A) Z) := by
  refine chainLaw_eq_of_consPath_preimage_eq κ (hc.kernel_eq s) (measurableSet_hitEvent _ _) ?_
  have hs' : start (π s) ∉ π ⁻¹' A := by
    rw [Set.mem_preimage, hc.π_start]
    exact hs
  ext q
  rw [Set.mem_preimage, Set.mem_preimage, consPath_mem_hitEvent_iff (show s ∉ π ⁻¹' A from hs),
    consPath_mem_hitEvent_iff hs']

/-- Almost surely the chain starts at its initial state and moves along `Γ`. -/
theorem ae_step [Countable S] (hc : IsNNChain κ π start Γ) (s : S) :
    ∀ᵐ ω ∂chainLaw κ s, ω 0 = s ∧
      ∀ n, π (ω (n + 1)) = π (ω n) ∨ Γ.Adj (π (ω n)) (π (ω (n + 1))) := by
  filter_upwards [chainLaw_ae_start κ s,
    Harmonic.ae_forall_succ_mem κ s (fun u => {t | π t = π u ∨ Γ.Adj (π u) (π t)})
      hc.step_null] with ω h0 hs
  exact ⟨h0, hs⟩

omit [DiscreteMeasurableSpace S] in
/-- The hitting distribution is at most one. -/
theorem hitLaw_le_one (π : S → V) (I W : Set V) (s : S) : hitLaw κ π I W s ≤ 1 :=
  prob_le_one

/-- **(M1) for hitting distributions.** If `I ⊆ B`,
`hitLaw I W (s) = ∫_{T_B < ⊤} hitLaw I W (start X_{T_B}) dP_s`. -/
theorem hitLaw_eq_setLIntegral (hc : IsNNChain κ π start Γ) {I B : Set V} (hIB : I ⊆ B)
    (W : Set V) (s : S) :
    hitLaw κ π I W s =
      ∫⁻ ω in {ω | hitTime (π ⁻¹' B) ω < ⊤},
        hitLaw κ π I W (start (π (stopState (hitTime (π ⁻¹' B)) ω))) ∂chainLaw κ s := by
  unfold hitLaw
  rw [chainLaw_hitEvent_eq_setLIntegral κ s (Set.preimage_mono hIB)]
  refine setLIntegral_congr_fun (measurableSet_hitTime_lt_top' _) fun ω _ => ?_
  exact hitLaw_eq_start hc I W _

end Markov

/-! ### A superlevel path to `I` -/

section Superlevel

variable {S V : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
  {κ : Kernel S S} [IsMarkovKernel κ] {π : S → V} {start : V → S} {Γ : SimpleGraph V}

/-- **C2 (superlevel path, the recurrence argument).** Let `g(v) = P_v(X_{T_I} ∈ W)`. If `g(y) > 0`, there is
a `Γ`-walk from `y` to a vertex `a ∈ I` all of whose vertices `v` satisfy `g(v) ≥ g(y)`.

Proof: otherwise let `U` be the set of vertices reachable from `y` by a walk outside `I` along which
`g ≥ g(y)`. At the exit time `σ` from `U` (`σ ≤ T_I`) the walk is at a neighbour of `U` where
`g < g(y)`, and the restart identity at `σ` gives `g(y) = E_y[g(X_σ); σ < ∞] < g(y)`. -/
theorem exists_walk_hitLaw_le (hc : IsNNChain κ π start Γ) (I W : Set V) (y : V)
    (hy : 0 < hitLaw κ π I W (start y)) :
    ∃ a ∈ I, ∃ w : Γ.Walk y a, ∀ v ∈ w.support,
      hitLaw κ π I W (start y) ≤ hitLaw κ π I W (start v) := by
  set g : V → ℝ≥0∞ := fun v => hitLaw κ π I W (start v) with hg
  set c := g y with hcdef
  by_cases hyI : y ∈ I
  · exact ⟨y, hyI, SimpleGraph.Walk.nil, fun v hv => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      rw [hv]⟩
  by_contra hcon
  push Not at hcon
  -- the vertices reachable from `y` outside `I` along `g ≥ c`
  set U : Set V := {v | ∃ w : Γ.Walk y v, ∀ u ∈ w.support, u ∉ I ∧ c ≤ g u} with hU
  have hyU : y ∈ U := ⟨SimpleGraph.Walk.nil, fun u hu => by
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
    exact hu ▸ ⟨hyI, le_rfl⟩⟩
  have hIU : I ⊆ Uᶜ := by
    rintro v hv ⟨w, hw⟩
    exact (hw v w.end_mem_support).1 hv
  set σ := hitTime (π ⁻¹' Uᶜ) with hσ
  set P := chainLaw κ (start y) with hP
  -- (M1) at `σ`
  have hM1 : c = ∫⁻ ω in {ω | σ ω < ⊤}, g (π (stopState σ ω)) ∂P :=
    hitLaw_eq_setLIntegral hc hIU W (start y)
  -- at `σ` the walk is at a vertex with `g < c`
  have hkey : ∀ᵐ ω ∂P, ω ∈ {ω | σ ω < ⊤} → g (π (stopState σ ω)) < c := by
    filter_upwards [ae_step hc (start y)] with ω ⟨h0, hstep⟩ hlt
    have hlt' : σ ω < ⊤ := hlt
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hlt'.ne
    obtain ⟨hnU, hbefore⟩ := hitTime_eq_coe_iff.mp hn.symm
    rw [stopState_eq_of_eq hn.symm]
    have hn0 : n ≠ 0 := by
      rintro rfl
      refine hnU ?_
      rw [h0, hc.π_start]
      exact hyU
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hkU : π (ω k) ∈ U := not_not.mp (hbefore k (Nat.lt_succ_self k))
    obtain ⟨wk, hwk⟩ := hkU
    have hadj : Γ.Adj (π (ω k)) (π (ω (k + 1))) := by
      rcases hstep k with h | h
      · exact absurd (h ▸ ⟨wk, hwk⟩ : π (ω (k + 1)) ∈ U) hnU
      · exact h
    by_contra hge
    push Not at hge
    have hsupp : ∀ u ∈ (wk.concat hadj).support, u ∈ wk.support ∨ u = π (ω (k + 1)) := by
      intro u hu
      rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hu
      exact hu
    by_cases hvI : π (ω (k + 1)) ∈ I
    · obtain ⟨u, hu, hgu⟩ := hcon _ hvI (wk.concat hadj)
      rcases hsupp u hu with hu' | rfl
      · exact absurd (hwk u hu').2 (not_le.mpr hgu)
      · exact absurd hge (not_le.mpr hgu)
    · refine hnU ⟨wk.concat hadj, fun u hu => ?_⟩
      rcases hsupp u hu with hu' | rfl
      · exact hwk u hu'
      · exact ⟨hvI, hge⟩
  -- the strict inequality `∫_{σ<⊤} g(X_σ) < c · P(σ < ⊤) ≤ c`
  have hmeas : MeasurableSet {ω : ℕ → S | σ ω < ⊤} := measurableSet_hitTime_lt_top' _
  have hpos : P {ω | σ ω < ⊤} ≠ 0 := by
    refine (lt_of_lt_of_le hy (measure_mono fun ω hω => ?_)).ne'
    exact lt_of_le_of_lt (hitTime_anti (Set.preimage_mono hIU) ω) (lt_top_iff_ne_top.mpr hω.1)
  have hfin : ∫⁻ ω in {ω | σ ω < ⊤}, g (π (stopState σ ω)) ∂P ≠ ⊤ := by
    rw [← hM1]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (hitLaw_le_one (κ := κ) π I W _)
  have hlt := lintegral_strict_mono (μ := P.restrict {ω | σ ω < ⊤})
    (g := fun _ => c) (by rwa [Ne, Measure.restrict_eq_zero]) aemeasurable_const hfin
    ((ae_restrict_iff' hmeas).mpr hkey)
  rw [← hM1, lintegral_const, Measure.restrict_apply_univ] at hlt
  have : c * P {ω | σ ω < ⊤} ≤ c := mul_le_of_le_one_right' prob_le_one
  exact absurd (lt_of_lt_of_le hlt this) (lt_irrefl c)

end Superlevel

/-! ### The total-variation bound by the separation probability -/

section Separation

variable {S V : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
  {κ : Kernel S S} [IsMarkovKernel κ] {π : S → V} {start : V → S} {Γ : SimpleGraph V}

omit [Countable S] in
/-- The lower bound behind C3: if every vertex of a walk from `y` to `I` has `g ≥ c`, then
`c · P_s(D) ≤ g(s)`, where `D` is the event that the vertices visited before `T_I` separate `{y}`
from `I`. -/
theorem mul_chainLaw_separates_le (hc : IsNNChain κ π start Γ) (I W : Set V) {y a : V} (ha : a ∈ I)
    (w : Γ.Walk y a) {c : ℝ≥0∞} (hw : ∀ v ∈ w.support, c ≤ hitLaw κ π I W (start v)) (s : S) :
    c * chainLaw κ s {ω | GraphSeparates Γ (traceBefore π I ω) {y} I} ≤ hitLaw κ π I W s := by
  set g : V → ℝ≥0∞ := fun v => hitLaw κ π I W (start v) with hg
  set B : Set V := {v | v ∈ w.support} ∪ I with hB
  set σ := hitTime (π ⁻¹' B) with hσ
  set P := chainLaw κ s with hP
  have hIB : I ⊆ B := Set.subset_union_right
  have hM1 : hitLaw κ π I W s = ∫⁻ ω in {ω | σ ω < ⊤}, g (π (stopState σ ω)) ∂P :=
    hitLaw_eq_setLIntegral hc hIB W s
  have hmeas : MeasurableSet {ω : ℕ → S | σ ω < ⊤} := measurableSet_hitTime_lt_top' _
  -- on `D`, the walk `w` is crossed before `T_I`, at a vertex where `g ≥ c`
  have hsub : {ω | GraphSeparates Γ (traceBefore π I ω) {y} I} ⊆
      {ω | c ≤ g (π (stopState σ ω))} ∩ {ω | σ ω < ⊤} := by
    intro ω hD
    obtain ⟨v, hv, m, hm, hmv⟩ := hD y (Set.mem_singleton y) a ha w
    have hmB : ω m ∈ π ⁻¹' B := by
      rw [Set.mem_preimage, hmv]
      exact Or.inl hv
    have hσm : σ ω ≤ m := hitTime_le_of_mem hmB
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top m) hσm)
    refine ⟨?_, show σ ω < ⊤ by rw [← hn]; exact ENat.natCast_lt_top n⟩
    show c ≤ g (π (stopState σ ω))
    rw [stopState_eq_of_eq hn.symm]
    have hnB := (hitTime_eq_coe_iff.mp hn.symm).1
    have hnI : π (ω n) ∉ I := notMem_of_lt_hitTime (lt_of_le_of_lt (hn ▸ hσm) hm)
    rcases hnB with hnw | hnI'
    · exact hw _ hnw
    · exact absurd hnI' hnI
  calc c * P {ω | GraphSeparates Γ (traceBefore π I ω) {y} I}
      ≤ c * (P.restrict {ω | σ ω < ⊤}) {ω | c ≤ g (π (stopState σ ω))} := by
        rw [Measure.restrict_apply' hmeas]
        exact mul_le_mul_right (measure_mono hsub) c
    _ ≤ ∫⁻ ω in {ω | σ ω < ⊤}, g (π (stopState σ ω)) ∂P := by
        have hmf : Measurable fun ω : ℕ → S => g (π (stopState σ ω)) :=
          (Measurable.of_discrete (f := fun t : S => g (π t))).comp
            (measurable_stopState_hitTime _)
        exact mul_meas_ge_le_lintegral₀ hmf.aemeasurable c
    _ = hitLaw κ π I W s := hM1.symm

/-- **C3 ([18, Lemma 3.10], maximum-principle proof; the recurrence argument).** For a nearest-neighbour chain,
every vertex set `I`, every `W` and all vertices `x, y`:
`P_y(X_{T_I} ∈ W) ≤ P_x(X_{T_I} ∈ W) + (1 - P_x(D))`, where `D` is the event that the vertices
visited by the chain from `x` strictly before `T_I` separate `{y}` from `I` in `Γ`. No recurrence,
reversibility or connectivity is needed. -/
theorem hitLaw_le_add (hc : IsNNChain κ π start Γ) (I W : Set V) (x y : V) :
    hitLaw κ π I W (start y) ≤ hitLaw κ π I W (start x) +
      (1 - chainLaw κ (start x) {ω | GraphSeparates Γ (traceBefore π I ω) {y} I}) := by
  set c := hitLaw κ π I W (start y) with hcdef
  set D := chainLaw κ (start x) {ω | GraphSeparates Γ (traceBefore π I ω) {y} I} with hD
  rcases eq_zero_or_pos c with h0 | hpos
  · rw [h0]
    exact zero_le
  obtain ⟨a, ha, w, hw⟩ := exists_walk_hitLaw_le hc I W y hpos
  have hlow := mul_chainLaw_separates_le hc I W ha w hw (start x)
  have hD1 : D ≤ 1 := prob_le_one
  have hc1 : c ≤ 1 := hitLaw_le_one (κ := κ) π I W _
  calc c = c * (D + (1 - D)) := by rw [add_tsub_cancel_of_le hD1, mul_one]
    _ = c * D + c * (1 - D) := mul_add _ _ _
    _ ≤ hitLaw κ π I W (start x) + 1 * (1 - D) := add_le_add hlow (mul_le_mul_left hc1 _)
    _ = hitLaw κ π I W (start x) + (1 - D) := by rw [one_mul]

omit [Countable S] in
/-- The hitting distributions of `W` and `Wᶜ` add up to the probability of visiting `I`. -/
theorem hitLaw_add_hitLaw_compl (I W : Set V) (s : S) :
    hitLaw κ π I W s + hitLaw κ π I Wᶜ s = chainLaw κ s {ω | hitTime (π ⁻¹' I) ω ≠ ⊤} := by
  unfold hitLaw
  rw [← measure_union _ (measurableSet_hitEvent _ _)]
  · congr 1
    ext ω
    simp only [hitEvent, Set.mem_union, Set.mem_ofPred_eq, Set.preimage_compl, Set.mem_compl_iff]
    tauto
  · refine Set.disjoint_left.mpr fun ω h1 h2 => h2.2 h1.2

omit [DiscreteMeasurableSpace S] [Countable S] in
theorem hitLaw_ne_top (I W : Set V) (s : S) : hitLaw κ π I W s ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hitLaw_le_one π I W s)

/-- **C3, real one-sided form** (the shape of the one-sided estimate):
`P_y(X_{T_I} ∈ W) - P_x(X_{T_I} ∈ W) ≤ 1 - P_x(D)`. -/
theorem toReal_hitLaw_sub_le (hc : IsNNChain κ π start Γ) (I W : Set V) (x y : V) :
    (hitLaw κ π I W (start y)).toReal - (hitLaw κ π I W (start x)).toReal ≤
      1 - (chainLaw κ (start x) {ω | GraphSeparates Γ (traceBefore π I ω) {y} I}).toReal := by
  set D := chainLaw κ (start x) {ω | GraphSeparates Γ (traceBefore π I ω) {y} I} with hD
  have hD1 : D ≤ 1 := prob_le_one
  have h := hitLaw_le_add hc I W x y
  have h1D : 1 - D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hfin : hitLaw κ π I W (start x) + (1 - D) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hitLaw_ne_top I W _, h1D⟩
  have h' := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hfin h) hfin).mpr h
  rw [ENNReal.toReal_add (hitLaw_ne_top I W _) h1D, ENNReal.toReal_sub_of_le hD1 ENNReal.one_ne_top,
    ENNReal.toReal_one] at h'
  linarith

/-- **C3, total-variation form.** If `I` is hit almost surely from `x` and from `y`, then for every
`W`, `|P_x(X_{T_I} ∈ W) - P_y(X_{T_I} ∈ W)| ≤ 1 - P_x(D)`. -/
theorem abs_hitLaw_sub_le (hc : IsNNChain κ π start Γ) (I W : Set V) {x y : V}
    (hx : chainLaw κ (start x) {ω | hitTime (π ⁻¹' I) ω ≠ ⊤} = 1)
    (hy : chainLaw κ (start y) {ω | hitTime (π ⁻¹' I) ω ≠ ⊤} = 1) :
    |(hitLaw κ π I W (start x)).toReal - (hitLaw κ π I W (start y)).toReal| ≤
      1 - (chainLaw κ (start x) {ω | GraphSeparates Γ (traceBefore π I ω) {y} I}).toReal := by
  have hsum : ∀ z : V, chainLaw κ (start z) {ω | hitTime (π ⁻¹' I) ω ≠ ⊤} = 1 →
      (hitLaw κ π I W (start z)).toReal + (hitLaw κ π I Wᶜ (start z)).toReal = 1 := by
    intro z hz
    rw [← ENNReal.toReal_add (hitLaw_ne_top I W _) (hitLaw_ne_top I Wᶜ _),
      hitLaw_add_hitLaw_compl, hz, ENNReal.toReal_one]
  have h1 := toReal_hitLaw_sub_le hc I W x y
  have h2 := toReal_hitLaw_sub_le hc I Wᶜ x y
  have hx' := hsum x hx
  have hy' := hsum y hy
  rw [abs_le]
  constructor <;> linarith

end Separation

end MatedCRTHarmonic.HarmonicInfinity
