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
  the first passage happens by time `ε`, which has positive probability, so the ratio `P(1 ≤ J)` is smaller than `1`;
* `lintegral_natCast_eq_tsum_measure_le`, `lintegral_natCast_mul_pred_eq_tsum`: tail-sum formulas for the first and
  second factorial moments of an `ℕ`-valued random variable;
* `lintegral_pathExcursionCount_le`, `lintegral_pathExcursionCount_lt_top`: `E J ≤ p / (1 - p) < ∞`, `p = P(1 ≤ J)`;
* `lintegral_pathExcursionCount_mul_pred_le`: `E[J (J - 1)] ≤ 2 q² / (1 - q)²`, `q = P(1 ≤ J)`.
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

section Moments

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}

/-- **Tail-sum formula.** For an `ℕ`-valued random variable `X`, `E X = ∑ₖ P(k + 1 ≤ X)`. -/
theorem lintegral_natCast_eq_tsum_measure_le {X : Ω' → ℕ} (hX : ∀ k, MeasurableSet {ω | k ≤ X ω}) :
    ∫⁻ ω, (X ω : ℝ≥0∞) ∂μ = ∑' k : ℕ, μ {ω | k + 1 ≤ X ω} := by
  have h : ∀ ω, (X ω : ℝ≥0∞) = ∑' k : ℕ, {ω | k + 1 ≤ X ω}.indicator 1 ω := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (X ω)) fun k hk => indicator_of_notMem (by
        simp only [Finset.mem_range, not_lt] at hk
        show ¬ (k + 1 ≤ X ω)
        omega) _]
    trans ∑ k ∈ Finset.range (X ω), (1 : ℝ≥0∞)
    · simp
    · refine Finset.sum_congr rfl fun k hk => (indicator_of_mem (a := ω) (s := {ω | k + 1 ≤ X ω}) ?_ 1).symm
      simp only [Finset.mem_range] at hk
      show k + 1 ≤ X ω
      omega
  simp_rw [h]
  rw [lintegral_tsum fun k => (measurable_one.indicator (hX (k + 1))).aemeasurable]
  simp_rw [lintegral_indicator_one (hX _)]

/-- **Tail-sum formula for the second factorial moment.** For an `ℕ`-valued random variable `X`,
`E[X (X - 1)] = ∑ₖ 2 k P(k + 1 ≤ X)`. -/
theorem lintegral_natCast_mul_pred_eq_tsum {X : Ω' → ℕ} (hX : ∀ k, MeasurableSet {ω | k ≤ X ω}) :
    ∫⁻ ω, ((X ω * (X ω - 1) : ℕ) : ℝ≥0∞) ∂μ = ∑' k : ℕ, 2 * (k : ℝ≥0∞) * μ {ω | k + 1 ≤ X ω} := by
  have h : ∀ ω, ((X ω * (X ω - 1) : ℕ) : ℝ≥0∞) =
      ∑' k : ℕ, {ω | k + 1 ≤ X ω}.indicator (fun _ => 2 * (k : ℝ≥0∞)) ω := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (X ω)) fun k hk => indicator_of_notMem (by
        simp only [Finset.mem_range, not_lt] at hk
        show ¬ (k + 1 ≤ X ω)
        omega) _]
    trans ∑ k ∈ Finset.range (X ω), 2 * (k : ℝ≥0∞)
    · rw [← Finset.sum_range_id_mul_two (X ω), Nat.cast_mul, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    · refine Finset.sum_congr rfl fun k hk =>
        (indicator_of_mem (a := ω) (s := {ω | k + 1 ≤ X ω}) ?_ (fun _ => 2 * (k : ℝ≥0∞))).symm
      simp only [Finset.mem_range] at hk
      show k + 1 ≤ X ω
      omega
  simp_rw [h]
  rw [lintegral_tsum fun k => (measurable_const.indicator (hX (k + 1))).aemeasurable]
  simp_rw [lintegral_indicator_const (hX _)]

end Moments

/-- **Finite mean of the excursion count.** For a real Brownian motion with continuous paths, `b ≥ 0` and `ε > 0`:
`E J ≤ p (1 - p)⁻¹` with `p = P(1 ≤ J)`. -/
theorem lintegral_pathExcursionCount_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ}
    (hb : 0 ≤ b) (hε : 0 < ε) :
    ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P ≤
      P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε} *
        (1 - P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε})⁻¹ := by
  rw [lintegral_natCast_eq_tsum_measure_le (measurableSet_le_pathExcursionCount hm hcont b hε),
    ← ENNReal.tsum_geometric_add_one]
  exact ENNReal.tsum_le_tsum fun k => measure_le_pathExcursionCount_le_pow hB hm hcont hb hε (k + 1)

theorem lintegral_pathExcursionCount_lt_top [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ}
    (hb : 0 ≤ b) (hε : 0 < ε) :
    ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P < ⊤ :=
  (lintegral_pathExcursionCount_le hB hm hcont hb hε).trans_lt (ENNReal.mul_lt_top (measure_lt_top _ _)
    (ENNReal.inv_lt_top.2 (tsub_pos_of_lt (measure_one_le_pathExcursionCount_lt_one hB hm hcont b hε))))

/-- **Second factorial moment of the excursion count.** For a real Brownian motion with continuous paths, `b ≥ 0` and
`ε > 0`: `E[J (J - 1)] ≤ 2 q² / (1 - q)²` with `q = P(1 ≤ J)`. -/
theorem lintegral_pathExcursionCount_mul_pred_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ}
    (hb : 0 ≤ b) (hε : 0 < ε) :
    ∫⁻ ω, ((pathExcursionCount (fun t => B t ω) b ε * (pathExcursionCount (fun t => B t ω) b ε - 1) : ℕ) :
        ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (2 * (P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε}).toReal ^ 2 /
        (1 - (P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε}).toReal) ^ 2) := by
  rw [lintegral_natCast_mul_pred_eq_tsum (measurableSet_le_pathExcursionCount hm hcont b hε)]
  have hp := measure_one_le_pathExcursionCount_lt_one hB hm hcont b hε
  set p := P {ω | 1 ≤ pathExcursionCount (fun t => B t ω) b ε} with hp_def
  set q := p.toReal with hq_def
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq1 : q < 1 := by
    have := (ENNReal.toReal_lt_toReal hp.ne_top ENNReal.one_ne_top).2 hp
    rwa [ENNReal.toReal_one] at this
  have hpq : p = ENNReal.ofReal q := (ENNReal.ofReal_toReal hp.ne_top).symm
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one (r := q)
    (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])).mul_left (2 * q)
  have hterm : ∀ k : ℕ, ENNReal.ofReal (2 * q * (k * q ^ k)) = 2 * (k : ℝ≥0∞) * p ^ (k + 1) := by
    intro k
    rw [hpq, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * q),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ k),
      ENNReal.ofReal_pow hq0, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
    ring
  calc ∑' k : ℕ, 2 * (k : ℝ≥0∞) * P {ω | k + 1 ≤ pathExcursionCount (fun t => B t ω) b ε}
      ≤ ∑' k : ℕ, 2 * (k : ℝ≥0∞) * p ^ (k + 1) := ENNReal.tsum_le_tsum fun k => by
        gcongr _ * ?_
        exact measure_le_pathExcursionCount_le_pow hB hm hcont hb hε (k + 1)
    _ = ∑' k : ℕ, ENNReal.ofReal (2 * q * (k * q ^ k)) := by simp_rw [hterm]
    _ = ENNReal.ofReal (∑' k : ℕ, 2 * q * (k * q ^ k)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs.summable).symm
    _ = ENNReal.ofReal (2 * q ^ 2 / (1 - q) ^ 2) := by rw [hs.tsum_eq]; congr 1; ring

end LatticeProb.LadderSet
