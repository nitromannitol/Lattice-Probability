import LatticeProb.Prob.ExcursionCountFirstLongStopping

/-!
# Restarting at the end of the first long excursion

For a real Brownian motion `B` with continuous paths, a level `b ≥ 0`, `ε > 0` and `k : ℕ`, write `J` for the number
of excursions of `B` above its running minimum of length larger than `ε` completed before the first passage below
`B 0 - b` (`pathExcursionCount`), and `ρ` for the end of the first such excursion (`longEnd`). Restarting `B` at `ρ`
(truncated at a horizon `N`) by the strong Markov property loses at most one excursion, which gives

  `P(ρ < N, k + 1 ≤ J) ≤ P(1 ≤ J) P(k ≤ J)`.

* `measurable_coe_of_isStoppingTime`, `measurable_apply_min_of_isStoppingTime`: a finite stopping time, and the values
  of the motion stopped at it, are measurable for the σ-algebra at the stopping time;
* `measurableSet_lt_and_forall_rat_le`: the event that the stopping time is before the horizon and that the stopped
  motion stays above `B 0 - b` at rational times is measurable;
* `exists_nnExtend_lt_of_forall_nat`: a path unbounded below along the integers goes below every level after every time;
* `measure_longEnd_lt_and_succ_le_pathExcursionCount_le`: the bound above.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

/-- A path that is unbounded below along the integers goes below every level after every time. -/
theorem exists_nnExtend_lt_of_forall_nat {f : ℝ≥0 → ℝ} (hf : ∀ m k : ℕ, ∃ n : ℕ, k ≤ n ∧ f n < -(m : ℝ))
    (T c : ℝ) : ∃ s, T ≤ s ∧ nnExtend f s < c := by
  obtain ⟨n, hkn, hn⟩ := hf ⌈-c⌉₊ ⌈T⌉₊
  refine ⟨n, (Nat.le_ceil T).trans (by exact_mod_cast hkn), ?_⟩
  have h1 : nnExtend f (n : ℝ) = f n := by simp [nnExtend]
  rw [h1]
  have h2 : -c ≤ (⌈-c⌉₊ : ℝ) := Nat.le_ceil _
  linarith

/-- The event that `τ` is before the horizon `N` and that `X` stopped at `τ` stays above `X 0 - b` at rational times
is measurable, if `τ` and the stopped values are. -/
theorem measurableSet_lt_and_forall_rat_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {τ : Ω → ℝ≥0}
    {X : ℝ≥0 → Ω → ℝ} (hτ : Measurable τ) (hX : ∀ q : ℝ≥0, Measurable fun ω => X (min q (τ ω)) ω) (b : ℝ)
    (N : ℝ≥0) :
    MeasurableSet {ω | τ ω < N ∧ ∀ q : ℚ, X 0 ω - b ≤ X (min (q : ℝ).toNNReal (τ ω)) ω} := by
  have h0 : Measurable (X 0) := by
    have he : (fun ω => X (min 0 (τ ω)) ω) = X 0 := by
      funext ω
      rw [min_eq_left zero_le]
    rw [← he]
    exact hX 0
  rw [ofPred_and]
  refine (measurableSet_lt hτ measurable_const).inter ?_
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun q => measurableSet_le (h0.sub_const b) (hX _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {ε : ℝ}

/-- A finite stopping time is measurable for the σ-algebra at itself. -/
theorem measurable_coe_of_isStoppingTime {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime F fun ω => (τ ω : ℝ≥0∞)) : Measurable[hτ.measurableSpace] τ := by
  have h := ENNReal.measurable_toNNReal.comp hτ.measurable
  have he : (ENNReal.toNNReal ∘ fun ω => ((τ ω : ℝ≥0) : ℝ≥0∞)) = τ := by
    funext ω
    simp
  rwa [he] at h

/-- **The stopped motion is measurable for the past at the stopping time.** For a real process with measurable
coordinates and continuous paths and a finite stopping time `τ` of the natural filtration, `B (min q τ)` is measurable
for the σ-algebra at `τ`. -/
theorem measurable_apply_min_of_isStoppingTime (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞)) (q : ℝ≥0) :
    Measurable[hτ.measurableSpace] fun ω => B (min q (τ ω)) ω := by
  have hτm := measurable_coe_of_isStoppingTime hτ
  have hS := (measurable_pi_apply q).comp (measurable_stopWithDrift hm hcont τ hτ)
  have hD : Measurable[hτ.measurableSpace] fun ω => ((q - τ ω : ℝ≥0) : ℝ) :=
    (NNReal.continuous_coe.comp (continuous_const.sub continuous_id)).measurable.comp hτm
  have he : (fun ω => B (min q (τ ω)) ω) = fun ω =>
      stopWithDrift (τ ω) (fun t => B t ω) q + ((q - τ ω : ℝ≥0) : ℝ) := by
    funext ω
    simp only [stopWithDrift, sub_add_cancel]
  rw [he]
  exact hS.add hD

/-- **One restart at the end of the first long excursion.** For a real Brownian motion with continuous paths, a level
`b ≥ 0`, `ε > 0`, a horizon `N` and `k : ℕ`: the probability that the first excursion above the running minimum of
length larger than `ε` ends before `N` and that at least `k + 1` such excursions are completed before the first passage
below `B 0 - b` is at most `P(1 ≤ J) P(k ≤ J)`. -/
theorem measure_longEnd_lt_and_succ_le_pathExcursionCount_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ}
    (hb : 0 ≤ b) (hε : 0 < ε) (N : ℝ≥0) (k : ℕ) :
    P {ω | longEnd (fun t => B t ω) ε < N ∧ k + 1 ≤ pathExcursionCount (fun t => B t ω) b ε} ≤
      P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε} *
        P {ω | k ≤ pathExcursionCount (fun t => B t ω) b ε} := by
  have hτ := isStoppingTime_longEndTrunc hm hcont hε N
  have hA := measurableSet_lt_and_forall_rat_le (mΩ := hτ.measurableSpace) (measurable_coe_of_isStoppingTime hτ)
    (measurable_apply_min_of_isStoppingTime hm hcont _ hτ) b N
  have hG := MatedCRTHarmonic.MatedCRT.BrownianPathFacts.ae_unboundedBelowInt hB.toIsPreBrownianReal hm
  calc P {ω | longEnd (fun t => B t ω) ε < N ∧ k + 1 ≤ pathExcursionCount (fun t => B t ω) b ε}
      ≤ P ({ω | longEndTrunc B ε N ω < N ∧
            ∀ q : ℚ, B 0 ω - b ≤ B (min (q : ℝ).toNNReal (longEndTrunc B ε N ω)) ω} ∩
          {ω | k ≤ pathExcursionCount
            (fun t => B (longEndTrunc B ε N ω + t) ω - B (longEndTrunc B ε N ω) ω) b ε}) := by
        refine measure_mono_ae (hG.mono fun ω hω hs => ?_)
        obtain ⟨hlt, hk⟩ := hs
        have hX := continuous_nnExtend (hcont ω)
        have hle : longEnd (fun t => B t ω) ε ≤ N := hlt.le
        have hρ := coe_longEndTrunc_eq_csInf hε N ω hle
        have hne := exists_nnExtend_lt_of_forall_nat (f := fun t => B t ω) hω 0 (nnExtend (fun t => B t ω) 0 - b)
        obtain ⟨-, hρτ, hrest⟩ := excursionCount_le_restart_csInf_longEndSet
          (Y := nnExtend fun t => B (longEndTrunc B ε N ω + t) ω - B (longEndTrunc B ε N ω) ω)
          (c := -B (longEndTrunc B ε N ω) ω) hX hε hne hk
        refine ⟨⟨?_, fun q => ?_⟩, hrest ?_ (exists_nnExtend_lt_of_forall_nat (f := fun t => B t ω) hω _ _)⟩
        · have h1 : ((longEndTrunc B ε N ω : ℝ≥0) : ℝ≥0∞) < N := by
            rw [coe_longEndTrunc, inf_eq_left.2 hle]
            exact hlt
          exact ENNReal.coe_lt_coe.1 h1
        · have h := (le_firstPassageBelow_iff_forall_Icc hX hb hne).1 hρτ
            ((min (q : ℝ).toNNReal (longEndTrunc B ε N ω) : ℝ≥0) : ℝ)
            ⟨NNReal.coe_nonneg _, (NNReal.coe_le_coe.2 (min_le_right _ _)).trans_eq hρ⟩
          simpa only [nnExtend, Real.toNNReal_zero, Real.toNNReal_coe] using h
        · intro u hu
          rw [← hρ]
          simp only [nnExtend]
          rw [Real.toNNReal_add (NNReal.coe_nonneg _) hu, Real.toNNReal_coe]
          ring
    _ = P {ω | longEndTrunc B ε N ω < N ∧
            ∀ q : ℚ, B 0 ω - b ≤ B (min (q : ℝ).toNNReal (longEndTrunc B ε N ω)) ω} *
          P {ω | k ≤ pathExcursionCount (fun t => B t ω) b ε} :=
        restart_le_pathExcursionCount hB hm hcont (longEndTrunc B ε N) hτ _ hA b hε k
    _ ≤ P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε} *
          P {ω | k ≤ pathExcursionCount (fun t => B t ω) b ε} := by
        gcongr ?_ * _
        refine measure_mono_ae (hG.mono fun ω hω hs => ?_)
        obtain ⟨hlt, hall⟩ := hs
        have hX := continuous_nnExtend (hcont ω)
        have hne := exists_nnExtend_lt_of_forall_nat (f := fun t => B t ω) hω 0 (nnExtend (fun t => B t ω) 0 - b)
        have hlt' : longEnd (fun t => B t ω) ε < N := by
          have h1 : ((longEndTrunc B ε N ω : ℝ≥0) : ℝ≥0∞) < N := ENNReal.coe_lt_coe.2 hlt
          rw [coe_longEndTrunc] at h1
          rcases inf_lt_iff.1 h1 with h | h
          · exact h
          · exact absurd h (lt_irrefl _)
        have hρ := coe_longEndTrunc_eq_csInf hε N ω hlt'.le
        have hρL := csInf_mem_longEndSet (isClosed_forwardLadderSet hX) hε
          ((longEnd_ne_top_iff _).1 (ne_top_of_lt hlt'))
        have hρpos : 0 < sInf (longEndSet (forwardLadderSet (nnExtend fun t => B t ω) 0) ε) :=
          hε.trans (lt_of_mem_longEndSet hρL)
        have hrat : ∀ q : ℚ,
            (q : ℝ) ∈ Icc 0 (sInf (longEndSet (forwardLadderSet (nnExtend fun t => B t ω) 0) ε)) →
              nnExtend (fun t => B t ω) 0 - b ≤ nnExtend (fun t => B t ω) q := by
          intro q hq
          have h := hall q
          rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 (hq.2.trans_eq hρ.symm))] at h
          simpa only [nnExtend, Real.toNNReal_zero] using h
        have hfb := (le_firstPassageBelow_iff_forall_Icc hX hb hne).2
          (le_of_forall_rat_mem_Icc hX.continuousOn hρpos hrat)
        exact one_le_excursionCount_of_mem_longEndSet hε hρL hfb

end LatticeProb.LadderSet
