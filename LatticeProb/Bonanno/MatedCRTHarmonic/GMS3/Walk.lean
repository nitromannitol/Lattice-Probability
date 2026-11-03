/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Walk at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Energy
import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Walk

/-!
# Simple random walk: exit from finite sets, first-step equations, escape probabilities

Probabilistic inputs of the deterministic part of GMS [18] §3 (exit from finite sets, first-step equations, and the Green function identity). Everything is
stated for the frozen edge-end walk `G.walkLaw` and the hitting distributions `hitDist`.

* `chainLaw_exists_notMem_eq_one` (generic Markov chains): if from every state of a finite set `A` the
  chain leaves `A` with positive probability, it leaves `A` almost surely (geometric trials, for any finite set);
* `chainLaw_hitTime_compl_ne_top`, `walkLaw_hitTime_compl_ne_top` (**exit lemma**): if every vertex of a
  finite set `U` is connected to a vertex outside `U`, the walk from every state visits `Uᶜ` a.s.;
* `lintegral_stepMeasure`, `hitDist_dartState`: one step of the walk is the uniform average over the
  darts at the current vertex, and a hitting probability from a dart state is the one from its head;
* `hitDist_eq_avg` (**first-step equation**): `P_x(X_{T_I} ∈ W) = deg(x)⁻¹ ∑_{d at x} P_{dtgt d}(X_{T_I} ∈ W)`
  for `x ∉ I`; `hitDist_of_mem`: for `x ∈ I` it is `1[x ∈ W]`;
* `hitDist_add_compl_eq_one`: under the exit lemma the hitting distribution has total mass one;
* `escProb G a W = P_a[T_W < T_a^+]` (after its first step, the walk visits `W` before returning to `a`),
  with its first-step form `escProb_eq_avg`, and the return probability `returnProb G a = P_a[T_a^+ < ⊤]`
  with `returnProb_eq_avg`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace MatedCRTHarmonic.GMS3

open Markov Harmonic HarmonicInfinity LFMultigraph

/-! ### Generic Markov chains: leaving a finite set -/

section Generic

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] (κ : Kernel S S)
  [IsMarkovKernel κ]

/-- **A chain leaves a finite set almost surely** if it leaves it with positive probability from every
state of the set (geometric trials). Ported from the private
`Embedded.chainLaw_ae_eventually_outside_finset`, for a finite `Set`. -/
theorem chainLaw_exists_notMem_eq_one {A : Set S} (hA : A.Finite)
    (hpos : ∀ s ∈ A, 0 < chainLaw κ s {ω : ℕ → S | ∃ n, ω n ∉ A}) (x : S) :
    chainLaw κ x {ω : ℕ → S | ∃ n, ω n ∉ A} = 1 := by
  classical
  have hAm : MeasurableSet A := hA.measurableSet
  let escape : Set (ℕ → S) := {ω | ∃ n, ω n ∉ A}
  let stay : Set (ℕ → S) := {ω | ∀ n, ω n ∈ A}
  have hescape : MeasurableSet escape := by
    have heq : escape = ⋃ n : ℕ, {ω : ℕ → S | ω n ∉ A} := by
      ext ω; simp [escape]
    rw [heq]
    exact MeasurableSet.iUnion fun n => hAm.compl.preimage (measurable_pi_apply n)
  have hstay : MeasurableSet stay := by
    have heq : stay = ⋂ n : ℕ, {ω : ℕ → S | ω n ∈ A} := by
      ext ω; simp [stay]
    rw [heq]
    exact MeasurableSet.iInter fun n => hAm.preimage (measurable_pi_apply n)
  have hstayEq : stay = escapeᶜ := by
    ext ω; simp [stay, escape]
  suffices hstay0 : chainLaw κ x stay = 0 by
    rw [hstayEq, measure_compl hescape (measure_ne_top _ _), measure_univ] at hstay0
    exact le_antisymm prob_le_one (tsub_eq_zero_iff_le.mp hstay0)
  by_cases hx : x ∈ A
  · let q : S → ℝ≥0∞ := fun s => chainLaw κ s escape
    let ε : ℝ≥0∞ := ∏ s ∈ hA.toFinset, q s
    have hqle (s : S) : q s ≤ 1 := prob_le_one
    have hεpos : 0 < ε := by
      apply pos_iff_ne_zero.mpr
      rw [Finset.prod_ne_zero_iff]
      intro s hs
      exact (hpos s (hA.mem_toFinset.mp hs)).ne'
    have hεle (s : S) (hs : s ∈ A) : ε ≤ q s := by
      have hs' : s ∈ hA.toFinset := hA.mem_toFinset.mpr hs
      calc (∏ t ∈ hA.toFinset, q t) = (∏ t ∈ hA.toFinset.erase s, q t) * q s :=
            (Finset.prod_erase_mul _ q hs').symm
        _ ≤ 1 * q s := mul_le_mul_of_nonneg_right (Finset.prod_le_one fun t _ => hqle t) bot_le
        _ = q s := one_mul _
    have hstayBound (s : S) (hs : s ∈ A) : chainLaw κ s stay ≤ 1 - ε := by
      rw [hstayEq, measure_compl hescape (measure_ne_top _ _), measure_univ]
      exact tsub_le_tsub_left (hεle s hs) 1
    let coord (n : ℕ) : Set (ℕ → S) := {ω | ω n ∈ A}
    let stayPrefix (n : ℕ) : Set (ℕ → S) := {ω | ∀ j ≤ n, ω j ∈ A}
    have hcoord (n : ℕ) : MeasurableSet (coord n) := hAm.preimage (measurable_pi_apply n)
    have hprefixEq (n : ℕ) : stayPrefix n = ⋂ j ≤ n, coord j := by
      ext ω; simp [stayPrefix, coord]
    have hstayEqIInter : stay = ⋂ n, coord n := by
      ext ω; simp [stay, coord]
    have hprefixMeas (n : ℕ) :
        MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] (stayPrefix n) := by
      rw [hprefixEq]
      refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj => ?_
      exact hAm.preimage (measurable_eval_piLE (S := S) hj)
    have hdecomp (n : ℕ) : chainLaw κ x stay =
        ∫⁻ ω in stayPrefix n, chainLaw κ (ω n) stay ∂chainLaw κ x := by
      have hset : stay = stayPrefix n ∩ walkShift n ⁻¹' stay := by
        ext ω
        change (∀ m, ω m ∈ A) ↔ (∀ j ≤ n, ω j ∈ A) ∧ ∀ k, walkShift n ω k ∈ A
        simp only [walkShift_apply]
        constructor
        · intro h
          exact ⟨fun j _ => h j, fun k => h (n + k)⟩
        · rintro ⟨hprefix, hshift⟩ m
          by_cases hm : m ≤ n
          · exact hprefix m hm
          · have heq : n + (m - n) = m := Nat.add_sub_of_le (Nat.le_of_not_ge hm)
            rw [← heq]
            exact hshift (m - n)
      calc chainLaw κ x stay = chainLaw κ x (stayPrefix n ∩ walkShift n ⁻¹' stay) :=
            congrArg (chainLaw κ x) hset
        _ = ∫⁻ ω in stayPrefix n, chainLaw κ (ω n) stay ∂chainLaw κ x :=
            chainLaw_inter_walkShift_preimage_of_piLE κ x n (hprefixMeas n) hstay
    have hbound (n : ℕ) : chainLaw κ x stay ≤ (1 - ε) * chainLaw κ x (stayPrefix n) := by
      rw [hdecomp n]
      calc (∫⁻ ω in stayPrefix n, chainLaw κ (ω n) stay ∂chainLaw κ x)
          ≤ ∫⁻ _ in stayPrefix n, (1 - ε) ∂chainLaw κ x :=
            setLIntegral_mono measurable_const fun ω hω =>
              hstayBound (ω n) (by simpa [stayPrefix] using hω n le_rfl)
        _ = (1 - ε) * chainLaw κ x (stayPrefix n) := setLIntegral_const _ _
    have htend : Tendsto (fun n => chainLaw κ x (stayPrefix n)) atTop
        (𝓝 (chainLaw κ x stay)) := by
      have h := tendsto_measure_iInter_le (μ := chainLaw κ x) (s := coord)
        (fun n => (hcoord n).nullMeasurableSet) ⟨0, measure_ne_top (chainLaw κ x) (coord 0)⟩
      simpa only [hprefixEq, hstayEqIInter] using h
    have hfactorFinite : 1 - ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have hprod : Tendsto (fun n => (1 - ε) * chainLaw κ x (stayPrefix n)) atTop
        (𝓝 ((1 - ε) * chainLaw κ x stay)) :=
      ((ENNReal.continuous_const_mul hfactorFinite).tendsto _).comp htend
    have hlim : chainLaw κ x stay ≤ (1 - ε) * chainLaw κ x stay :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hprod (Filter.Eventually.of_forall hbound)
    by_contra hne
    have hposStay : 0 < chainLaw κ x stay := pos_iff_ne_zero.mpr hne
    have hfactor : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hεpos.ne'
    have hlt : (1 - ε) * chainLaw κ x stay < chainLaw κ x stay := by
      rw [mul_comm]
      simpa using ENNReal.mul_lt_mul_right hposStay.ne' (measure_ne_top (chainLaw κ x) stay)
        hfactor
    exact (not_lt_of_ge hlim) hlt
  · refine measure_mono_null (t := {ω : ℕ → S | ¬ ω 0 = x}) (fun ω hω => ?_)
      (ae_iff.mp (chainLaw_ae_start κ x))
    intro h0
    have h1 : ω 0 ∈ A := (show ∀ n, ω n ∈ A from hω) 0
    rw [h0] at h1
    exact hx h1

end Generic

/-! ### The walk -/

variable {V E : Type*} (G : LFMultigraph V E)

/-- The states at a given vertex form a finite set. -/
theorem finite_stateVertex_preimage_singleton (v : V) :
    (G.stateVertex ⁻¹' {v}).Finite := by
  have hD : {d : G.Dart | G.dtgt d = v}.Finite := by
    refine ((G.finite_inc v).prod (Set.finite_univ : (Set.univ : Set Bool).Finite)).subset ?_
    rintro ⟨e, b⟩ hd
    simp only [Set.mem_ofPred_eq] at hd
    refine ⟨?_, Set.mem_univ _⟩
    cases b
    · exact Or.inr hd
    · exact Or.inl hd
  refine ((Set.finite_singleton (startState G v)).union (hD.image (dartState G))).subset ?_
  intro s hs
  cases s with
  | inl w =>
    left
    have : w = v := hs
    rw [this]
    rfl
  | inr d => exact Or.inr ⟨d, hs, rfl⟩

theorem finite_stateVertex_preimage {U : Set V} (hU : U.Finite) :
    (G.stateVertex ⁻¹' U).Finite := by
  rw [← Set.biUnion_of_singleton U, Set.preimage_iUnion₂]
  exact hU.biUnion fun v _ => finite_stateVertex_preimage_singleton G v

/-- **Exit lemma** : if every vertex of the finite set `U` is connected to a vertex
outside `U`, the walk from every state visits `Uᶜ` almost surely. -/
theorem chainLaw_hitTime_compl_ne_top {U : Set V} (hU : U.Finite)
    (hesc : ∀ x ∈ U, ∃ y, y ∉ U ∧ G.adj.Reachable x y) (s : G.State) :
    chainLaw G.walkKernel s {ω | hitTime (G.stateVertex ⁻¹' Uᶜ) ω ≠ ⊤} = 1 := by
  have hset : {ω : ℕ → G.State | hitTime (G.stateVertex ⁻¹' Uᶜ) ω ≠ ⊤} =
      {ω | ∃ n, ω n ∉ G.stateVertex ⁻¹' U} := by
    ext ω
    rw [Set.mem_ofPred_eq, hitTime_ne_top_iff]
    rfl
  rw [hset]
  refine chainLaw_exists_notMem_eq_one G.walkKernel (finite_stateVertex_preimage G hU)
    (fun t ht => ?_) s
  obtain ⟨y, hy, ⟨p⟩⟩ := hesc (G.stateVertex t) ht
  have h := chainLaw_hit_pos_of_walk G (A := Uᶜ) (a := y) hy (G.stateVertex t) p t rfl
  refine lt_of_lt_of_le h (measure_mono fun ω hω => ?_)
  rw [Set.mem_ofPred_eq, hitTime_lt_top_iff] at hω
  exact hω

theorem walkLaw_hitTime_compl_ne_top {U : Set V} (hU : U.Finite)
    (hesc : ∀ x ∈ U, ∃ y, y ∉ U ∧ G.adj.Reachable x y) (x : V) :
    G.walkLaw x {ω | hitTime Uᶜ (G.vertexPath ω) ≠ ⊤} = 1 :=
  chainLaw_hitTime_compl_ne_top G hU hesc (startState G x)

/-! ### One step of the walk -/

theorem lintegral_stepMeasure (x : V) (F : G.State → ℝ≥0∞) :
    ∫⁻ s, F s ∂G.stepMeasure x = (G.deg x : ℝ≥0∞)⁻¹ * ∑ d ∈ G.outDarts x, F (dartState G d) := by
  rw [stepMeasure_eq, lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  exact lintegral_dirac _ _

/-- A hitting distribution from a dart state is the one from the head of the dart. -/
theorem hitDist_dartState (I W : Set V) (d : G.Dart) :
    chainLaw G.walkKernel (dartState G d) (hitEvent (G.stateVertex ⁻¹' I) (G.stateVertex ⁻¹' W)) =
      hitDist G I (G.dtgt d) W :=
  hitLaw_eq_start (isNNChain_walk G) I W (dartState G d)

/-- **First-step equation** for hitting distributions: for `x ∉ I`,
`P_x(X_{T_I} ∈ W) = deg(x)⁻¹ ∑_{d at x} P_{dtgt d}(X_{T_I} ∈ W)`. -/
theorem hitDist_eq_avg {I : Set V} {x : V} (hx : x ∉ I) (W : Set V) :
    hitDist G I x W = (G.deg x : ℝ≥0∞)⁻¹ * ∑ d ∈ G.outDarts x, hitDist G I (G.dtgt d) W := by
  rw [hitDist_eq_hitLaw]
  unfold hitLaw
  rw [chainLaw_apply_eq_lintegral_consPath _ _ (measurableSet_hitEvent _ _)]
  have hpre : consPath (startState G x) ⁻¹' hitEvent (G.stateVertex ⁻¹' I) (G.stateVertex ⁻¹' W) =
      hitEvent (G.stateVertex ⁻¹' I) (G.stateVertex ⁻¹' W) := by
    ext q
    exact consPath_mem_hitEvent_iff (show startState G x ∉ G.stateVertex ⁻¹' I from hx) q
  rw [hpre, walkKernel_apply, stateVertex_startState, lintegral_stepMeasure]
  congr 1
  exact Finset.sum_congr rfl fun d _ => hitDist_dartState G I W d

/-- Started in `I`, the walk is at its first visit to `I` at time `0`. -/
theorem hitDist_of_mem {I : Set V} {x : V} (hx : x ∈ I) (W : Set V) :
    hitDist G I x W = W.indicator 1 x := by
  have hae : ∀ᵐ ω ∂G.walkLaw x, ω ∈ hitEvent (G.stateVertex ⁻¹' I) (G.stateVertex ⁻¹' W) ↔
      x ∈ W := by
    filter_upwards [chainLaw_ae_start G.walkKernel (startState G x)] with ω h0
    have hT : hitTime (G.stateVertex ⁻¹' I) ω = 0 := by
      rw [hitTime_eq_zero_iff, h0]
      exact hx
    simp only [hitEvent, Set.mem_ofPred_eq, hT, ne_eq, ENat.zero_ne_top, not_false_eq_true,
      true_and, Set.mem_preimage]
    rw [stopState_eq_of_eq (n := 0) (by rw [hT]; rfl), h0]
    rfl
  rw [hitDist_eq_hitLaw]
  unfold hitLaw
  by_cases hW : x ∈ W
  · rw [Set.indicator_of_mem hW, Pi.one_apply, ← walkLaw_eq]
    refine le_antisymm prob_le_one ?_
    rw [← measure_univ (μ := G.walkLaw x)]
    exact (measure_congr (by filter_upwards [hae] with ω hω; simp [hω, hW])).ge
  · rw [Set.indicator_of_notMem hW, ← walkLaw_eq]
    exact measure_eq_zero_iff_ae_notMem.mpr (by filter_upwards [hae] with ω hω; simpa [hW] using hω)

/-- Under the exit lemma the hitting distribution of `I` is a probability vector:
`P_x(X_{T_I} ∈ W) + P_x(X_{T_I} ∈ Wᶜ) = 1`. -/
theorem hitDist_add_compl_eq_one {I : Set V} {x : V}
    (hI : G.walkLaw x {ω | hitTime I (G.vertexPath ω) ≠ ⊤} = 1) (W : Set V) :
    hitDist G I x W + hitDist G I x Wᶜ = 1 := by
  rw [hitDist_eq_hitLaw, hitDist_eq_hitLaw, hitLaw_add_hitLaw_compl]
  exact hI

theorem hitDist_le_one (I W : Set V) (x : V) : hitDist G I x W ≤ 1 := prob_le_one

theorem hitDist_ne_top (I W : Set V) (x : V) : hitDist G I x W ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hitDist_le_one G I W x)

/-! ### Escape and return probabilities -/

theorem measurableSet_hitTime_ne_top' (B : Set G.State) :
    MeasurableSet {ω : ℕ → G.State | hitTime B ω ≠ ⊤} := by
  simpa only [lt_top_iff_ne_top] using measurableSet_hitTime_lt_top' B

/-- `P_a[T_W < T_a^+]`: after its first step, the walk from `a` visits `W` before it returns to `a`
(its first visit to `{a} ∪ W` after time `1` lies in `W`). -/
def escProb (a : V) (W : Set V) : ℝ≥0∞ :=
  G.walkLaw a (walkShift 1 ⁻¹'
    hitEvent (G.stateVertex ⁻¹' insert a W) (G.stateVertex ⁻¹' W))

/-- `P_a[T_a^+ < ⊤]`: the walk from `a` returns to `a`. -/
def returnProb (a : V) : ℝ≥0∞ :=
  G.walkLaw a (walkShift 1 ⁻¹' {ω | hitTime (G.stateVertex ⁻¹' {a}) ω ≠ ⊤})

/-- First step for path events of the shifted walk. -/
theorem walkLaw_walkShift_one (a : V) {F : Set (ℕ → G.State)} (hF : MeasurableSet F) :
    G.walkLaw a (walkShift 1 ⁻¹' F) =
      (G.deg a : ℝ≥0∞)⁻¹ * ∑ d ∈ G.outDarts a, chainLaw G.walkKernel (dartState G d) F := by
  rw [walkLaw_eq, chainLaw_apply_eq_lintegral_consPath _ _ ((measurable_walkShift 1) hF)]
  have hpre : consPath (startState G a) ⁻¹' (walkShift 1 ⁻¹' F) = F := by
    ext q
    simp only [Set.mem_preimage, walkShift_one_consPath]
  rw [hpre, walkKernel_apply, stateVertex_startState, lintegral_stepMeasure]

theorem escProb_eq_avg (a : V) (W : Set V) :
    escProb G a W = (G.deg a : ℝ≥0∞)⁻¹ *
      ∑ d ∈ G.outDarts a, hitDist G (insert a W) (G.dtgt d) W := by
  unfold escProb
  rw [walkLaw_walkShift_one G a (measurableSet_hitEvent _ _)]
  congr 1
  exact Finset.sum_congr rfl fun d _ => hitDist_dartState G _ _ d

/-- The probability of visiting `A` (time `0` included) from a dart state is the one from its head. -/
theorem chainLaw_dartState_hitTime_ne_top (A : Set V) (d : G.Dart) :
    chainLaw G.walkKernel (dartState G d) {ω | hitTime (G.stateVertex ⁻¹' A) ω ≠ ⊤} =
      G.walkLaw (G.dtgt d) {ω | hitTime A (G.vertexPath ω) ≠ ⊤} := by
  have h := chainLaw_vertexEvent (isNNChain_walk G) (dartState G d) (Q := fun X => hitTime A X ≠ ⊤)
    (measurableSet_hitTime_eq_top (A := G.stateVertex ⁻¹' A) MeasurableSet.of_discrete).compl
  exact h

theorem returnProb_eq_avg (a : V) :
    returnProb G a = (G.deg a : ℝ≥0∞)⁻¹ *
      ∑ d ∈ G.outDarts a, G.walkLaw (G.dtgt d) {ω | hitTime {a} (G.vertexPath ω) ≠ ⊤} := by
  unfold returnProb
  rw [walkLaw_walkShift_one G a (measurableSet_hitTime_ne_top' G _)]
  congr 1
  exact Finset.sum_congr rfl fun d _ => chainLaw_dartState_hitTime_ne_top G {a} d

end MatedCRTHarmonic.GMS3
