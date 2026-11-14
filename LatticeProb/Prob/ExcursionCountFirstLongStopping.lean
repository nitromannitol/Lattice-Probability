import LatticeProb.Analysis.ExcursionCountFirstLong
import LatticeProb.Prob.ExcursionCountStopped

/-!
# The end of the first long excursion is a stopping time

For a path `f : ℝ≥0 → ℝ` and `ε > 0`, `longEnd f ε ∈ ℝ≥0∞` is the end of the first excursion of `f` above its running
minimum from time `0` of length larger than `ε` (`⊤` if there is none): the infimum of `longEndSet` of the forward
ladder set of `nnExtend f` from `0`.

* `longEnd_le_iff`: for a continuous path, `longEnd f ε ≤ t` iff some end of a long gap of the ladder set is `≤ t`;
* `exists_measurableSet_exists_mem_longEndSet_le`: for a process with measurable values at rational times, the event
  that some end of a long gap of the ladder set is `≤ t` agrees on continuous paths with a measurable set (a countable
  description at rational times);
* `isStoppingTime_longEnd`: for a real process with continuous paths, `longEnd` is a stopping time of the natural
  filtration (the event `{longEnd ≤ t}` depends only on the path stopped at `t`);
* `longEndTrunc`, `isStoppingTime_longEndTrunc`: the truncation at a horizon `N`, a finite stopping time.
-/

open MeasureTheory Set
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

variable {ε : ℝ}

open Classical in
/-- The end of the first excursion of `f` above its running minimum from time `0` of length larger than `ε`
(`⊤` if there is none). -/
noncomputable def longEnd (f : ℝ≥0 → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  if (longEndSet (forwardLadderSet (nnExtend f) 0) ε).Nonempty then
    ENNReal.ofReal (sInf (longEndSet (forwardLadderSet (nnExtend f) 0) ε))
  else ⊤

theorem longEnd_ne_top_iff (f : ℝ≥0 → ℝ) :
    longEnd f ε ≠ ⊤ ↔ (longEndSet (forwardLadderSet (nnExtend f) 0) ε).Nonempty := by
  unfold longEnd
  split_ifs with hne
  · exact ⟨fun _ => hne, fun _ => ENNReal.ofReal_ne_top⟩
  · exact ⟨fun h => absurd rfl h, fun h => absurd h hne⟩

theorem longEnd_of_nonempty {f : ℝ≥0 → ℝ} (hne : (longEndSet (forwardLadderSet (nnExtend f) 0) ε).Nonempty) :
    longEnd f ε = ENNReal.ofReal (sInf (longEndSet (forwardLadderSet (nnExtend f) 0) ε)) := by
  simp only [longEnd, hne, ↓reduceIte]

/-- **The event `{longEnd ≤ t}`.** For a continuous path, `longEnd f ε ≤ t` iff some end of a gap of length larger than
`ε` of the forward ladder set is at most `t`. -/
theorem longEnd_le_iff {f : ℝ≥0 → ℝ} (hf : Continuous f) (hε : 0 < ε) (t : ℝ≥0) :
    longEnd f ε ≤ t ↔ ∃ x ∈ longEndSet (forwardLadderSet (nnExtend f) 0) ε, x ≤ t := by
  by_cases hne : (longEndSet (forwardLadderSet (nnExtend f) 0) ε).Nonempty
  · rw [longEnd_of_nonempty hne, ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
    constructor
    · intro h
      exact ⟨_, csInf_mem_longEndSet (isClosed_forwardLadderSet (continuous_nnExtend hf)) hε hne, h⟩
    · rintro ⟨x, hx, hxt⟩
      exact (csInf_le (bddBelow_longEndSet hε) hx).trans hxt
  · have htop : longEnd f ε = ⊤ := by
      by_contra h
      exact hne ((longEnd_ne_top_iff f).1 h)
    rw [htop]
    constructor
    · intro h
      exact absurd h (not_le.2 ENNReal.coe_lt_top)
    · rintro ⟨x, hx, -⟩
      exact absurd ⟨x, hx⟩ hne

section Measurability

/-- **A countable description of `{ρ ≤ t}`.** For a process `X` with measurable values at rational times and `ε > 0`,
there is a measurable set `S` such that, for every `ω` with a continuous path, `ω ∈ S` iff some end of a gap of length
larger than `ε` of the forward ladder set of `X ω` from `0` is at most `t`. -/
theorem exists_measurableSet_exists_mem_longEndSet_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {X : Ω → ℝ → ℝ}
    (hX : ∀ q : ℚ, Measurable fun ω => X ω q) (hε : 0 < ε) (t : ℝ) :
    ∃ S : Set Ω, MeasurableSet S ∧ ∀ ω, Continuous (X ω) →
      (ω ∈ S ↔ ∃ x ∈ longEndSet (forwardLadderSet (X ω) 0) ε, x ≤ t) := by
  have hDm : ∀ q : ℚ, Measurable fun ω => X ω q - ⨅ p : {p : ℚ // (p : ℝ) ∈ Icc (0 : ℝ) q}, X ω p := by
    intro q
    have h := measurable_sub_iInf_rat hX 0 q
    rw [Rat.cast_zero] at h
    exact h
  refine ⟨{ω | ∃ r u : ℚ, ((0 : ℝ) ≤ r ∧ (r : ℝ) + ε < u ∧ (u : ℝ) < t) ∧
      (∃ n : ℕ, ∀ q : ℚ, (q : ℝ) ∈ Icc (r : ℝ) u →
        1 / ((n : ℝ) + 1) ≤ X ω q - ⨅ p : {p : ℚ // (p : ℝ) ∈ Icc (0 : ℝ) q}, X ω p) ∧
      ∀ n : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc (u : ℝ) t ∧
        X ω q - ⨅ p : {p : ℚ // (p : ℝ) ∈ Icc (0 : ℝ) q}, X ω p < 1 / ((n : ℝ) + 1)}, ?_, ?_⟩
  · refine measurableSet_setOfPred.2 ?_
    refine Measurable.exists fun r => Measurable.exists fun u => Measurable.and measurable_const
      (Measurable.and ?_ ?_)
    · exact Measurable.exists fun n => Measurable.forall fun q => Measurable.imp measurable_const
        (measurableSet_setOfPred.1 (measurableSet_le measurable_const (hDm q)))
    · exact Measurable.forall fun n => Measurable.exists fun q => Measurable.and measurable_const
        (measurableSet_setOfPred.1 (measurableSet_lt (hDm q) measurable_const))
  · intro ω hω
    have hinf : ∀ q : ℚ, 0 ≤ (q : ℝ) →
        sInf (X ω '' Icc 0 q) = ⨅ p : {p : ℚ // (p : ℝ) ∈ Icc (0 : ℝ) q}, X ω p := by
      intro q hq
      have h0 : ((0 : ℚ) : ℝ) ≤ q := by rw [Rat.cast_zero]; exact hq
      have h := sInf_image_Icc_eq_iInf_rat_of_le hω h0
      rw [Rat.cast_zero] at h
      exact h
    constructor
    · rintro ⟨r, u, ⟨hr, hru, hut⟩, ⟨n, hn⟩, hall⟩
      have hru' : (r : ℝ) < u := by linarith
      have hu0 : (0 : ℝ) ≤ u := hr.trans hru'.le
      have hfree : ∀ y ∈ Icc (r : ℝ) u, y ∉ forwardLadderSet (X ω) 0 := by
        refine (forall_notMem_forwardLadderSet_iff hω hr hru').2 ⟨n, fun q hq => ?_⟩
        rw [hinf q (hr.trans hq.1)]
        exact hn q hq
      obtain ⟨x, hxK, hux, hxt⟩ := (exists_mem_forwardLadderSet_iff hω hu0 hut).2 fun m => by
        obtain ⟨q, hq, hlt⟩ := hall m
        refine ⟨q, hq, ?_⟩
        rw [hinf q (hu0.trans hq.1)]
        exact hlt
      exact ⟨x, ⟨hxK, r, u, hr, hru, hux, hfree⟩, hxt⟩
    · rintro ⟨x, ⟨hxK, r, u, hr, hru, hux, hfree⟩, hxt⟩
      have hru' : (r : ℝ) < u := by linarith
      have hu0 : (0 : ℝ) ≤ u := hr.trans hru'.le
      have hux' : (u : ℝ) < x := lt_of_le_of_ne hux fun h =>
        hfree u ⟨hru'.le, le_rfl⟩ (by rw [h]; exact hxK)
      have hut : (u : ℝ) < t := hux'.trans_le hxt
      refine ⟨r, u, ⟨hr, hru, hut⟩, ?_, fun m => ?_⟩
      · obtain ⟨n, hn⟩ := (forall_notMem_forwardLadderSet_iff hω hr hru').1 hfree
        refine ⟨n, fun q hq => ?_⟩
        rw [← hinf q (hr.trans hq.1)]
        exact hn q hq
      · obtain ⟨q, hq, hlt⟩ := (exists_mem_forwardLadderSet_iff hω hu0 hut).1 ⟨x, hxK, hux, hxt⟩ m
        refine ⟨q, hq, ?_⟩
        rw [← hinf q (hu0.trans hq.1)]
        exact hlt

end Measurability

section StoppingTime

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-- **The end of the first long excursion is a stopping time** of the natural filtration of the `ℝ ^ 1`-lift, for a
real process with continuous paths: `{longEnd ≤ t}` is described by the path stopped at `t`. -/
theorem isStoppingTime_longEnd (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (hε : 0 < ε) :
    IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => longEnd (fun t => B t ω) ε := by
  intro t
  have hZ : ∀ q : ℚ, Measurable[natFiltration (liftOne B) (stronglyMeasurable_liftOne hm) t]
      fun ω => nnExtend (stopWithDrift t fun s => B s ω) q := by
    intro q
    have h1 : Measurable[natFiltration (liftOne B) (stronglyMeasurable_liftOne hm) t]
        (B (min (q : ℝ).toNNReal t)) :=
      ((stronglyAdapted_natFiltration_real hm) (min (q : ℝ).toNNReal t)).measurable.mono
        ((natFiltration (liftOne B) (stronglyMeasurable_liftOne hm)).mono (min_le_right _ _)) le_rfl
    simp only [nnExtend, stopWithDrift]
    exact h1.sub_const _
  obtain ⟨S, hS, hSiff⟩ := exists_measurableSet_exists_mem_longEndSet_le
    (mΩ := natFiltration (liftOne B) (stronglyMeasurable_liftOne hm) t) hZ hε t
  refine MeasurableSet.congr hS ?_
  ext ω
  have hcongr : forwardLadderSet (nnExtend (stopWithDrift t fun s => B s ω)) 0 ∩ Icc 0 (t : ℝ) =
      forwardLadderSet (nnExtend fun s => B s ω) 0 ∩ Icc 0 (t : ℝ) :=
    forwardLadderSet_inter_Icc_congr fun u hu => nnExtend_stopWithDrift_of_le hu.2
  exact ((hSiff ω (continuous_nnExtend (continuous_stopWithDrift (hcont ω) t))).trans
    (exists_mem_longEndSet_le_congr hε hcongr)).trans (longEnd_le_iff (hcont ω) hε t).symm

omit [MeasurableSpace Ω] in
/-- The end of the first long excursion truncated at the horizon `N`, with values in `ℝ≥0`. -/
noncomputable def longEndTrunc (B : ℝ≥0 → Ω → ℝ) (ε : ℝ) (N : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (longEnd (fun t => B t ω) ε ⊓ (N : ℝ≥0∞)).toNNReal

omit [MeasurableSpace Ω] in
theorem coe_longEndTrunc (B : ℝ≥0 → Ω → ℝ) (ε : ℝ) (N : ℝ≥0) (ω : Ω) :
    ((longEndTrunc B ε N ω : ℝ≥0) : ℝ≥0∞) = longEnd (fun t => B t ω) ε ⊓ (N : ℝ≥0∞) := by
  rw [longEndTrunc, ENNReal.coe_toNNReal]
  exact (lt_of_le_of_lt inf_le_right ENNReal.coe_lt_top).ne

/-- The truncated end of the first long excursion is a (finite) stopping time. -/
theorem isStoppingTime_longEndTrunc (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (hε : 0 < ε) (N : ℝ≥0) :
    IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => ((longEndTrunc B ε N ω : ℝ≥0) : ℝ≥0∞) := by
  have h := (isStoppingTime_longEnd hm hcont hε).min_const (i := N)
  have hfun : (fun ω => ((longEndTrunc B ε N ω : ℝ≥0) : ℝ≥0∞))
      = fun ω => min (longEnd (fun t => B t ω) ε) (N : ℝ≥0∞) := by
    funext ω
    exact coe_longEndTrunc B ε N ω
  rw [hfun]
  exact h

omit [MeasurableSpace Ω] in
/-- Before the horizon, the truncated time is the end `ρ` of the first long excursion. -/
theorem coe_longEndTrunc_eq_csInf (hε : 0 < ε) (N : ℝ≥0) (ω : Ω)
    (h : longEnd (fun t => B t ω) ε ≤ (N : ℝ≥0∞)) :
    ((longEndTrunc B ε N ω : ℝ≥0) : ℝ) =
      sInf (longEndSet (forwardLadderSet (nnExtend fun t => B t ω) 0) ε) := by
  have hne : (longEndSet (forwardLadderSet (nnExtend fun t => B t ω) 0) ε).Nonempty :=
    (longEnd_ne_top_iff _).1 (ne_top_of_le_ne_top ENNReal.coe_ne_top h)
  have hρ : 0 ≤ sInf (longEndSet (forwardLadderSet (nnExtend fun t => B t ω) 0) ε) :=
    le_csInf hne fun x hx => (hε.trans (lt_of_mem_longEndSet hx)).le
  rw [longEndTrunc, inf_eq_left.2 h, longEnd_of_nonempty hne, ENNReal.coe_toNNReal_eq_toReal,
    ENNReal.toReal_ofReal hρ]

end StoppingTime

end LatticeProb.LadderSet
