import LatticeProb.Prob.ExcursionCountFirstLongRestart

/-!
# Geometric tail of the excursion count

For a real Brownian motion `B` with continuous paths, a level `b ≥ 0` and `ε > 0`, write `J` for the number of
excursions of `B` above its running minimum of length larger than `ε` completed before the first passage below
`B 0 - b` (`pathExcursionCount`). Restarting at the end of the first such excursion gives

  `P(k + 1 ≤ J) ≤ P(1 ≤ J) P(k ≤ J)`,   hence   `P(k ≤ J) ≤ P(1 ≤ J) ^ k`.

* `longEnd_ne_top_of_one_le_pathExcursionCount`: if a long excursion is completed before the first passage, the end of
  the first long excursion is finite;
* `measure_succ_le_pathExcursionCount_le`: the one-step bound above (the horizon of the restart is sent to infinity);
* `measure_le_pathExcursionCount_le_pow`: the geometric tail;
* `pathExcursionCount_eq_zero_of_le`, `measure_one_le_pathExcursionCount_lt_one`: no long excursion is completed when
  the first passage happens by time `ε`, which has positive probability, so the ratio `P(1 ≤ J)` is smaller than `1`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

/-- For a continuous path that goes below `f 0 - b`, a long excursion completed before the first passage below
`f 0 - b` forces the end of the first excursion of length larger than `ε` to be finite. -/
theorem longEnd_ne_top_of_one_le_pathExcursionCount {f : ℝ≥0 → ℝ} (hf : Continuous f) {b ε : ℝ} (hε : 0 < ε)
    (hne : ∃ s, 0 ≤ s ∧ nnExtend f s < nnExtend f 0 - b) (h : 1 ≤ pathExcursionCount f b ε) :
    longEnd f ε ≠ ⊤ :=
  (longEnd_ne_top_iff f).2 ⟨_, mem_longEndSet_of_one_le_excursionCount hε
    (firstPassageBelow_mem_forwardLadderSet (continuous_nnExtend hf) hne) h⟩

/-- If a path goes below `f 0 - b` by time `ε`, no excursion of length larger than `ε` is completed before the first
passage below `f 0 - b`. -/
theorem pathExcursionCount_eq_zero_of_le {f : ℝ≥0 → ℝ} {b ε s : ℝ} (hε : 0 < ε) (hs0 : 0 ≤ s) (hsε : s ≤ ε)
    (hs : nnExtend f s < nnExtend f 0 - b) : pathExcursionCount f b ε = 0 := by
  have hτ : firstPassageBelow (nnExtend f) 0 b ≤ ε :=
    (csInf_le (s := {t | 0 ≤ t ∧ nnExtend f t < nnExtend f 0 - b}) ⟨0, fun _ hr => hr.1⟩ ⟨hs0, hs⟩).trans hsε
  by_contra hne
  have h1 : 1 ≤ excursionCount (forwardLadderSet (nnExtend f) 0) 0 (firstPassageBelow (nnExtend f) 0 b) ε :=
    Nat.one_le_iff_ne_zero.2 hne
  obtain ⟨r, u, hint, -⟩ := (le_excursionCount_iff hε 1).1 h1
  obtain ⟨h0, h1, h2, -⟩ := hint 0
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {ε : ℝ}

/-- **One-step bound for the excursion count.** For a real Brownian motion with continuous paths, `b ≥ 0`, `ε > 0`
and `k : ℕ`: `P(k + 1 ≤ J) ≤ P(1 ≤ J) P(k ≤ J)`. -/
theorem measure_succ_le_pathExcursionCount_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ}
    (hb : 0 ≤ b) (hε : 0 < ε) (k : ℕ) :
    P {ω | k + 1 ≤ pathExcursionCount (fun t => B t ω) b ε} ≤
      P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε} *
        P {ω | k ≤ pathExcursionCount (fun t => B t ω) b ε} := by
  have hG := MatedCRTHarmonic.MatedCRT.BrownianPathFacts.ae_unboundedBelowInt hB.toIsPreBrownianReal hm
  have hmono : Monotone fun N : ℕ => {ω | longEnd (fun t => B t ω) ε < ((N : ℝ≥0) : ℝ≥0∞) ∧
      k + 1 ≤ pathExcursionCount (fun t => B t ω) b ε} := by
    intro N M hNM ω hω
    exact ⟨hω.1.trans_le (by exact_mod_cast hNM), hω.2⟩
  calc P {ω | k + 1 ≤ pathExcursionCount (fun t => B t ω) b ε}
      ≤ P (⋃ N : ℕ, {ω | longEnd (fun t => B t ω) ε < ((N : ℝ≥0) : ℝ≥0∞) ∧
          k + 1 ≤ pathExcursionCount (fun t => B t ω) b ε}) := by
        refine measure_mono_ae (hG.mono fun ω hω hk => ?_)
        have hne := exists_nnExtend_lt_of_forall_nat (f := fun t => B t ω) hω 0
          (nnExtend (fun t => B t ω) 0 - b)
        obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (longEnd_ne_top_of_one_le_pathExcursionCount (hcont ω) hε hne
          (le_trans (by omega) hk))
        exact mem_iUnion.2 ⟨N, by rwa [ENNReal.coe_natCast], hk⟩
    _ = ⨆ N : ℕ, P {ω | longEnd (fun t => B t ω) ε < ((N : ℝ≥0) : ℝ≥0∞) ∧
          k + 1 ≤ pathExcursionCount (fun t => B t ω) b ε} := hmono.measure_iUnion
    _ ≤ _ := iSup_le fun N =>
          measure_longEnd_lt_and_succ_le_pathExcursionCount_le hB hm hcont hb hε (N : ℝ≥0) k

/-- **Geometric tail of the excursion count.** For a real Brownian motion with continuous paths, `b ≥ 0`, `ε > 0`
and `k : ℕ`: `P(k ≤ J) ≤ P(1 ≤ J) ^ k`. -/
theorem measure_le_pathExcursionCount_le_pow [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ}
    (hb : 0 ≤ b) (hε : 0 < ε) (k : ℕ) :
    P {ω | k ≤ pathExcursionCount (fun t => B t ω) b ε} ≤
      P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε} ^ k := by
  induction k with
  | zero => rw [pow_zero]; exact prob_le_one
  | succ k ih =>
    calc P {ω | k + 1 ≤ pathExcursionCount (fun t => B t ω) b ε}
        ≤ P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε} *
            P {ω | k ≤ pathExcursionCount (fun t => B t ω) b ε} :=
          measure_succ_le_pathExcursionCount_le hB hm hcont hb hε k
      _ ≤ P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε} *
            P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε} ^ k := by gcongr _ * ?_
      _ = _ := (pow_succ' _ _).symm

/-- **The ratio of the geometric tail is smaller than `1`.** For a real Brownian motion with continuous paths, any
level `b` and `ε > 0`, the probability that a long excursion is completed before the first passage below `B 0 - b`
is smaller than `1`: with positive probability `B ε < B 0 - b`. -/
theorem measure_one_le_pathExcursionCount_lt_one [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (b : ℝ) (hε : 0 < ε) :
    P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε} < 1 := by
  set e : ℝ≥0 := ⟨ε, hε.le⟩ with he
  have hL := hB.toIsPreBrownianReal.hasLaw_sub e 0
  have hv : nndist (e : ℝ) ((0 : ℝ≥0) : ℝ) ≠ 0 := fun h =>
    hε.ne' (nndist_eq_zero.1 h)
  have hpos : P ((B e - B 0) ⁻¹' Iio (-b)) ≠ 0 := by
    rw [← Measure.map_apply_of_aemeasurable hL.aemeasurable measurableSet_Iio, hL.map_eq]
    intro h0
    have := gaussianReal_absolutelyContinuous' 0 hv h0
    simp at this
  have hsub : (B e - B 0) ⁻¹' Iio (-b) ⊆ {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε}ᶜ := by
    intro ω hω
    simp only [mem_preimage, mem_Iio, Pi.sub_apply] at hω
    have hJ := pathExcursionCount_eq_zero_of_le (f := fun t => B t ω) (b := b) hε hε.le le_rfl (by
      simp only [nnExtend, Real.toNNReal_zero, Real.toNNReal_of_nonneg hε.le]
      change B e ω < B 0 ω - b
      linarith)
    simp [hJ]
  have hmeas := measurableSet_le_pathExcursionCount hm hcont b hε 1
  calc P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε}
      < P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε} +
          P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε}ᶜ :=
        ENNReal.lt_add_right (measure_ne_top _ _) fun h => hpos (measure_mono_null hsub h)
    _ = 1 := by rw [measure_add_measure_compl hmeas, measure_univ]

end LatticeProb.LadderSet
