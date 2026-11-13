import Mathlib
import LatticeProb.Prob.BrownianExit
import LatticeProb.Prob.BrownianMarkov
import LatticeProb.Prob.ContinuousPathStepTimes
import LatticeProb.Prob.BrownianIncrementCount

/-!
# Exit of the unit ball against the displacement times of Brownian motion

Let `B` be a Brownian motion on `ℝ ^ d` started at `0` and `σ_k(r)` its successive times of
displacement by `r` (`stepTime`).  With the grid-counting lemmas for continuous paths and for Brownian
increments, we bound, with explicit constants,

* the probability that `B` reaches norm `1` by time `σ_K(r)` (`measure_exit_by_stepTime_le`), and
* the probability that `B` stays in the open unit ball up to time `σ_K(r)`
  (`measure_stays_in_ball_le`).

For `K ≈ r ^ -(2 - ζ)` the first is superpolynomially small in `r`, and for `K ≈ r ^ -(2 + ζ)` so is
the second.  The event `‖B_t‖ ≥ 1` is the larger event `∃ t ≤ σ_K`, so the bounds hold for the
first exit time of the ball.  They do not depend on the time parametrization of `B`, so they hold
for Brownian motion with any constant diffusivity.
-/

open MeasureTheory ProbabilityTheory Set

open scoped NNReal ENNReal

universe u

namespace LatticeProb

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}

/-- The first coordinate of a Brownian motion on `ℝ ^ d`, scaled by `√d`, is a real Brownian
motion. -/
lemma IsBrownianSpace.isPreBrownianReal_coord0 (hd : 0 < d) (hB : IsBrownianSpace d 0 B P) :
    IsPreBrownianReal (fun t ω => Real.sqrt d * B t ω ⟨0, hd⟩) P := by
  have h := (hB.coord ⟨0, hd⟩).toIsPreBrownianReal
  simpa using h

/-- An increment of the scaled first coordinate is at most `√d` times the norm increment. -/
lemma abs_sqrt_mul_coord_sub_le (hd : 0 < d) (a b : EuclideanSpace ℝ (Fin d)) :
    |Real.sqrt d * a ⟨0, hd⟩ - Real.sqrt d * b ⟨0, hd⟩| ≤ Real.sqrt d * ‖a - b‖ := by
  have h1 : |a ⟨0, hd⟩ - b ⟨0, hd⟩| ≤ ‖a - b‖ := by
    have := PiLp.norm_apply_le (a - b) ⟨0, hd⟩
    simpa [Real.norm_eq_abs] using this
  rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)

/-- A large increment of the scaled first coordinate gives a large norm increment. -/
lemma two_mul_le_norm_sub_of_big (hd : 0 < d) {a b : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (h : 2 * Real.sqrt d * r ≤ |Real.sqrt d * a ⟨0, hd⟩ - Real.sqrt d * b ⟨0, hd⟩|) :
    2 * r ≤ ‖a - b‖ := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have h2 := (abs_sqrt_mul_coord_sub_le hd a b)
  refine le_of_mul_le_mul_left ?_ hsd
  calc Real.sqrt d * (2 * r) = 2 * Real.sqrt d * r := by ring
    _ ≤ _ := h.trans h2

open Classical in
/-- **The motion reaches the unit sphere only after enough displacement times.**  For a Brownian
motion `B` on `ℝ ^ d` started at `0`, `r > 0`, `K ≤ m q / 2` (with `q` the Gaussian tail at
`2 √d`) and `T > m r ^ 2`, the probability that `‖B t‖ ≥ 1` for some `t ≤ σ_K(r)` is at most the sum
of the Hoeffding bound `2 exp (-(m q ^ 2 / 8))` for having fewer than `K` displacement windows among
the first `m` windows of length `r ^ 2`, and the exit tail `C exp (-c / T)` for reaching the unit
sphere before time `T`. -/
theorem measure_exit_by_stepTime_le (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)), IsBrownianSpace d 0 B P → 0 < d →
        ∀ (r : ℝ≥0), 0 < r → ∀ (K m : ℕ), 0 < m →
        (K : ℝ) ≤ m * gaussTail (2 * Real.sqrt d) / 2 → ∀ T : ℝ, (m : ℝ) * (r : ℝ) ^ 2 < T →
        P {ω | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ stepTime (fun t => B t ω) (r : ℝ) K ∧ 1 ≤ ‖B t ω‖}
          ≤ ENNReal.ofReal (2 * Real.exp (-(m * gaussTail (2 * Real.sqrt d) ^ 2 / 8)))
            + ENNReal.ofReal (C * Real.exp (-(c * 1 ^ 2 / T))) := by
  obtain ⟨C, c, hC, hc, hexit⟩ := brownian_exit_tail_closed d
  refine ⟨C, c, hC, hc, ?_⟩
  intro Ω _ P _ B hB hd r hr K m hm hK T hT
  have hT0 : 0 < T := lt_of_le_of_lt (by positivity) hT
  set s : ℝ≥0 := r ^ 2 with hs_def
  have hs : 0 < s := pow_pos hr 2
  have hsqrt : Real.sqrt (s : ℝ) = r := by
    rw [hs_def, NNReal.coe_pow, Real.sqrt_sq (NNReal.coe_nonneg r)]
  have hY := IsBrownianSpace.isPreBrownianReal_coord0 hd hB
  have hcount := measure_card_bigIncrement_lt_le hY hs (2 * Real.sqrt d) m K hm hK
  beta_reduce at hcount
  have hex := hexit 0 Ω P inferInstance B hB 1 one_pos T hT0
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ stepTime (fun t => B t ω) (r : ℝ) K ∧
      1 ≤ ‖B t ω‖} → ω ∈ ({ω | ((Finset.range m).filter (fun j : ℕ =>
        2 * Real.sqrt d * Real.sqrt (s : ℝ) ≤ |Real.sqrt d * B (((j + 1 : ℕ) : ℝ≥0) * s) ω ⟨0, hd⟩
          - Real.sqrt d * B ((j : ℝ≥0) * s) ω ⟨0, hd⟩|)).card < K} ∪
        {ω | ∃ t : ℝ≥0, (t : ℝ) < T ∧ 1 ≤ ‖B t ω - 0‖}) := by
    filter_upwards [hB.cont] with ω hcont
    rintro ⟨t, ht, hnorm⟩
    by_cases hlt : ((Finset.range m).filter (fun j : ℕ =>
        2 * Real.sqrt d * Real.sqrt (s : ℝ) ≤ |Real.sqrt d * B (((j + 1 : ℕ) : ℝ≥0) * s) ω ⟨0, hd⟩
          - Real.sqrt d * B ((j : ℝ≥0) * s) ω ⟨0, hd⟩|)).card < K
    · exact Or.inl hlt
    · right
      rw [not_lt] at hlt
      set J := (Finset.range m).filter (fun j : ℕ =>
        2 * Real.sqrt d * Real.sqrt (s : ℝ) ≤ |Real.sqrt d * B (((j + 1 : ℕ) : ℝ≥0) * s) ω ⟨0, hd⟩
          - Real.sqrt d * B ((j : ℝ≥0) * s) ω ⟨0, hd⟩|) with hJ
      have hJm : ∀ j ∈ J, j < m := fun j hj => Finset.mem_range.1 (Finset.mem_filter.1 hj).1
      have hJb : ∀ j ∈ J, 2 * (r : ℝ) ≤
          ‖B (((j + 1 : ℕ) : ℝ≥0) * s) ω - B ((j : ℝ≥0) * s) ω‖ := by
        intro j hj
        have h := (Finset.mem_filter.1 hj).2
        rw [hsqrt] at h
        exact two_mul_le_norm_sub_of_big hd h
      have hle := stepTime_card_le (f := fun t => B t ω) hcont (r := (r : ℝ))
        (by exact_mod_cast hr) (s := s) (m := m) J hJm hJb
      have hKle : stepTime (fun t => B t ω) (r : ℝ) K ≤
          stepTime (fun t => B t ω) (r : ℝ) J.card := monotone_stepTime hlt
      have h3 : (t : ℝ≥0∞) ≤ (((m : ℝ≥0) * s : ℝ≥0) : ℝ≥0∞) := ht.trans (hKle.trans hle)
      have h4 : (t : ℝ) ≤ (m : ℝ) * (r : ℝ) ^ 2 := by
        have := ENNReal.coe_le_coe.1 h3
        have h5 : (t : ℝ) ≤ (((m : ℝ≥0) * s : ℝ≥0) : ℝ) := by exact_mod_cast this
        simpa [hs_def] using h5
      exact ⟨t, lt_of_le_of_lt h4 hT, by simpa using hnorm⟩
  calc _ ≤ P ({ω | ((Finset.range m).filter (fun j : ℕ =>
        2 * Real.sqrt d * Real.sqrt (s : ℝ) ≤ |Real.sqrt d * B (((j + 1 : ℕ) : ℝ≥0) * s) ω ⟨0, hd⟩
          - Real.sqrt d * B ((j : ℝ≥0) * s) ω ⟨0, hd⟩|)).card < K} ∪
        {ω | ∃ t : ℝ≥0, (t : ℝ) < T ∧ 1 ≤ ‖B t ω - 0‖}) := measure_mono_ae hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add hcount hex

/-- **Few large oscillations on short windows.**  The probability that a Brownian motion on `ℝ ^ d`
started at `0` has, for some window `[t, t']` of length at most `s` starting at a time `t ≤ T`,
a displacement `‖B t' - B t‖ ≥ r`, is at most `(⌊T / s⌋ + 1) C exp (-(c (r / 2) ^ 2 / (3 s)))`.  The
windows are covered by the grid windows `[i s, (i + 3) s]`, `i ≤ T / s`, and each is controlled by the
exit tail of the restarted motion. -/
theorem measure_oscillation_le (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)), IsBrownianSpace d 0 B P →
        ∀ (r : ℝ), 0 < r → ∀ (s T : ℝ≥0), 0 < s →
        P {ω | ∃ t t' : ℝ≥0, t ≤ T ∧ t ≤ t' ∧ t' ≤ t + s ∧ r ≤ ‖B t' ω - B t ω‖}
          ≤ ((⌊(T : ℝ) / s⌋₊ + 1 : ℕ) : ℝ≥0∞)
            * ENNReal.ofReal (C * Real.exp (-(c * (r / 2) ^ 2 / (3 * s)))) := by
  obtain ⟨C, c, hC, hc, hexit⟩ := brownian_exit_tail_closed d
  refine ⟨C, c, hC, hc, ?_⟩
  intro Ω _ P _ B hB r hr s T hs
  set N := ⌊(T : ℝ) / s⌋₊ with hN
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  let F : ℕ → Set Ω := fun i => {ω | ∃ u : ℝ≥0, (u : ℝ) < 3 * s ∧
    r / 2 ≤ ‖B ((i : ℝ≥0) * s + u) ω - B ((i : ℝ≥0) * s) ω - 0‖}
  have hF : ∀ i, P (F i) ≤ ENNReal.ofReal (C * Real.exp (-(c * (r / 2) ^ 2 / (3 * s)))) := by
    intro i
    have hsh := hB.shift ((i : ℝ≥0) * s)
    exact hexit 0 Ω P inferInstance _ hsh (r / 2) (by positivity) (3 * s) (by positivity)
  have hsub : {ω | ∃ t t' : ℝ≥0, t ≤ T ∧ t ≤ t' ∧ t' ≤ t + s ∧ r ≤ ‖B t' ω - B t ω‖} ⊆
      ⋃ i ∈ Finset.range (N + 1), F i := by
    rintro ω ⟨t, t', htT, htt', ht's, hr'⟩
    set i := ⌊(t : ℝ) / s⌋₊ with hi
    have hiN : i ≤ N := Nat.floor_le_floor (div_le_div_of_nonneg_right (by exact_mod_cast htT)
      hs'.le)
    have hg1 : ((i : ℝ≥0) * s : ℝ≥0) ≤ t := by
      have : (i : ℝ) ≤ (t : ℝ) / s := Nat.floor_le (by positivity)
      have h2 : (i : ℝ) * s ≤ t := by rwa [le_div_iff₀ hs'] at this
      exact_mod_cast h2
    have hg2 : (t : ℝ) < (i : ℝ) * s + s := by
      have : (t : ℝ) / s < i + 1 := Nat.lt_floor_add_one _
      rw [div_lt_iff₀ hs'] at this
      linarith
    set g : ℝ≥0 := (i : ℝ≥0) * s with hg
    have hg1' : (g : ℝ) ≤ t := by exact_mod_cast hg1
    have hg2' : (g : ℝ) = (i : ℝ) * s := by simp [hg]
    have hgt' : g ≤ t' := hg1.trans htt'
    have ht'g : (t' : ℝ) ≤ t + s := by exact_mod_cast ht's
    refine Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hiN)) ?_
    have htri : r ≤ ‖B t' ω - B g ω‖ + ‖B t ω - B g ω‖ := by
      calc r ≤ ‖B t' ω - B t ω‖ := hr'
        _ = ‖(B t' ω - B g ω) - (B t ω - B g ω)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    by_cases hcase : r / 2 ≤ ‖B t' ω - B g ω‖
    · refine ⟨t' - g, ?_, ?_⟩
      · have : ((t' - g : ℝ≥0) : ℝ) = t' - g := NNReal.coe_sub hgt'
        rw [this]
        nlinarith
      · rw [add_tsub_cancel_of_le hgt', sub_zero]
        exact hcase
    · refine ⟨t - g, ?_, ?_⟩
      · have : ((t - g : ℝ≥0) : ℝ) = t - g := NNReal.coe_sub hg1
        rw [this]
        nlinarith
      · rw [add_tsub_cancel_of_le hg1, sub_zero]
        push Not at hcase
        linarith
  calc P {ω | ∃ t t' : ℝ≥0, t ≤ T ∧ t ≤ t' ∧ t' ≤ t + s ∧ r ≤ ‖B t' ω - B t ω‖}
      ≤ P (⋃ i ∈ Finset.range (N + 1), F i) := measure_mono hsub
    _ ≤ ∑ i ∈ Finset.range (N + 1), P (F i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range (N + 1), ENNReal.ofReal (C * Real.exp (-(c * (r / 2) ^ 2 / (3 * s)))) :=
        Finset.sum_le_sum fun i _ => hF i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

open Classical in
/-- **A Brownian motion that stays in the unit ball for a long time.**  With `s = 1`, `K = 1`:
if `m < T` and `1 ≤ m q / 2`, the probability that `‖B t‖ < 1` for all `t < T` is at most
`2 exp (-(m q ^ 2 / 8))`: each of the `m` unit time windows then carries an increment of the first
coordinate below `2 √d`, which has probability `1 - q` and independent. -/
theorem measure_forall_norm_lt_one_le [IsProbabilityMeasure P] (hd : 0 < d)
    (hB : IsBrownianSpace d 0 B P) (m : ℕ) (hm : 0 < m)
    (hq : 1 ≤ (m : ℝ) * gaussTail (2 * Real.sqrt d) / 2) {T : ℝ} (hmT : (m : ℝ) < T) :
    P {ω | ∀ t : ℝ≥0, (t : ℝ) < T → ‖B t ω‖ < 1}
      ≤ ENNReal.ofReal (2 * Real.exp (-(m * gaussTail (2 * Real.sqrt d) ^ 2 / 8))) := by
  have hY := IsBrownianSpace.isPreBrownianReal_coord0 hd hB
  have hcount := measure_card_bigIncrement_lt_le hY (s := 1) one_pos (2 * Real.sqrt d) m 1 hm
    (by exact_mod_cast hq)
  beta_reduce at hcount
  refine le_trans (measure_mono ?_) hcount
  intro ω hω
  have hempty : ((Finset.range m).filter (fun j : ℕ => 2 * Real.sqrt d * Real.sqrt ((1 : ℝ≥0) : ℝ)
      ≤ |Real.sqrt d * B (((j + 1 : ℕ) : ℝ≥0) * 1) ω ⟨0, hd⟩
        - Real.sqrt d * B ((j : ℝ≥0) * 1) ω ⟨0, hd⟩|)) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun j hj => ?_
    have hj' : j < m := Finset.mem_range.1 hj
    have hj1 : (((j + 1 : ℕ) : ℝ≥0) * 1 : ℝ≥0) = ((j + 1 : ℕ) : ℝ≥0) := mul_one _
    have hj2 : ((j : ℝ≥0) * 1 : ℝ≥0) = (j : ℝ≥0) := mul_one _
    rw [hj1, hj2]
    have h1 : ‖B ((j + 1 : ℕ) : ℝ≥0) ω‖ < 1 := hω _ (by
      have : ((j + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hj'
      push_cast at this ⊢
      linarith)
    have h2 : ‖B (j : ℝ≥0) ω‖ < 1 := hω _ (by
      have : (j : ℝ) < m := by exact_mod_cast hj'
      push_cast
      linarith)
    have h3 := abs_sqrt_mul_coord_sub_le hd (B ((j + 1 : ℕ) : ℝ≥0) ω) (B (j : ℝ≥0) ω)
    have h4 : ‖B ((j + 1 : ℕ) : ℝ≥0) ω - B (j : ℝ≥0) ω‖ < 2 :=
      lt_of_le_of_lt (norm_sub_le _ _) (by linarith)
    have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    rw [NNReal.coe_one, Real.sqrt_one, mul_one, not_le]
    calc _ ≤ Real.sqrt d * ‖B ((j + 1 : ℕ) : ℝ≥0) ω - B (j : ℝ≥0) ω‖ := h3
      _ < Real.sqrt d * 2 := mul_lt_mul_of_pos_left h4 hsd
      _ = 2 * Real.sqrt d := mul_comm _ _
  show (Finset.filter _ _).card < 1
  rw [hempty]
  simp

open Classical in
/-- **A Brownian motion that stays in the unit ball up to the `K`-th displacement time.**  Let
`T ≤ K s`, `0 < s`, `m < T` and `1 ≤ m q / 2`.  The probability that `‖B t‖ < 1` for all `t` below
the `K`-th displacement time `σ_K(r)` is at most the unit-window bound `2 exp (-(m q ^ 2 / 8))` plus
the oscillation bound of `measure_oscillation_le`: either some window of length `s` below `T` has
displacement `≥ r` (and then the displacement times may come early), or all of them are below `r`, in
which case `σ_K(r) ≥ min T (K s) = T`. -/
theorem measure_stays_in_ball_le (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)), IsBrownianSpace d 0 B P → 0 < d →
        ∀ (r : ℝ≥0), 0 < r → ∀ (K : ℕ) (s T : ℝ≥0), 0 < s → T ≤ (K : ℝ≥0) * s →
        ∀ m : ℕ, 0 < m → 1 ≤ (m : ℝ) * gaussTail (2 * Real.sqrt d) / 2 → (m : ℝ) < T →
        P {ω | ∀ t : ℝ≥0, (t : ℝ≥0∞) < stepTime (fun t => B t ω) (r : ℝ) K → ‖B t ω‖ < 1}
          ≤ ENNReal.ofReal (2 * Real.exp (-(m * gaussTail (2 * Real.sqrt d) ^ 2 / 8)))
            + ((⌊(T : ℝ) / s⌋₊ + 1 : ℕ) : ℝ≥0∞)
              * ENNReal.ofReal (C * Real.exp (-(c * ((r : ℝ) / 2) ^ 2 / (3 * s)))) := by
  obtain ⟨C, c, hC, hc, hosc⟩ := measure_oscillation_le.{u} d
  refine ⟨C, c, hC, hc, ?_⟩
  intro Ω _ P _ B hB hd r hr K s T hs hTK m hm hq hmT
  have h1 := measure_forall_norm_lt_one_le (P := P) hd hB m hm hq hmT
  have h2 := hosc Ω P B hB r (by exact_mod_cast hr) s T hs
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | ∀ t : ℝ≥0, (t : ℝ≥0∞) < stepTime (fun t => B t ω) (r : ℝ) K →
      ‖B t ω‖ < 1} → ω ∈ ({ω | ∀ t : ℝ≥0, (t : ℝ) < T → ‖B t ω‖ < 1} ∪
      {ω | ∃ t t' : ℝ≥0, t ≤ T ∧ t ≤ t' ∧ t' ≤ t + s ∧ (r : ℝ) ≤ ‖B t' ω - B t ω‖}) := by
    refine Filter.Eventually.of_forall fun ω hω => ?_
    by_cases hosc' : ∃ t t' : ℝ≥0, t ≤ T ∧ t ≤ t' ∧ t' ≤ t + s ∧ (r : ℝ) ≤ ‖B t' ω - B t ω‖
    · exact Or.inr hosc'
    · left
      push Not at hosc'
      have hmin := min_le_stepTime (f := fun t => B t ω) (r := (r : ℝ)) T s
        (fun t t' h1 h2 h3 => hosc' t t' h1 h2 h3) K
      have hTK' : (T : ℝ≥0∞) ≤ (K : ℝ≥0∞) * s := by
        have : ((T : ℝ≥0) : ℝ≥0∞) ≤ (((K : ℝ≥0) * s : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hTK
        simpa using this
      rw [min_eq_left hTK'] at hmin
      intro t ht
      refine hω t (lt_of_lt_of_le ?_ hmin)
      exact_mod_cast ht
  calc _ ≤ P ({ω | ∀ t : ℝ≥0, (t : ℝ) < T → ‖B t ω‖ < 1} ∪
      {ω | ∃ t t' : ℝ≥0, t ≤ T ∧ t ≤ t' ∧ t' ≤ t + s ∧ (r : ℝ) ≤ ‖B t' ω - B t ω‖}) :=
        measure_mono_ae hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add h1 h2

end LatticeProb
