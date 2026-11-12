import LatticeProb.Gauss.CircleAverageTailUniform
import LatticeProb.Gauss.CircleAverageDyadicSum

/-!
# Summable one-point tails of circle averages along shrinking circles

For a whole-plane Gaussian free field `h`, a scale `s > 0`, centres `c k` with `‖c k‖ ≤ M s / 2ᵏ`
and the circle averages `h_{s/2ᵏ}(c k)` along the dyadic radii `s / 2ᵏ`, the probabilities
`P{-η k < ξ (h_{s/2ᵏ}(c k) + A log (s / 2ᵏ))}` are summable in `k` as soon as `ξ > 0` and
`η < ξ A log 2`.  Indeed the event forces `h_{s/2ᵏ}(c k) ≥ b k - A log s` with
`b = A log 2 - η / ξ > 0`, while `Var (h_{s/2ᵏ}(c k) - h_1(0)) ≤ k log 2 + const`, so the Gaussian tail
gives `≲ exp (-(b² / (2 log 2)) k)`.

* `LatticeProb.Gauss.exists_pos_eventually_quadratic_of_pos`: the elementary asymptotic inequality
  `2 κ n (m n + L) ≤ (b n - K)²` for large `n`, for any `b > 0` and `m > 0`;
* `LatticeProb.Gauss.IsWholePlaneGFF.tsum_measure_shell_circle_exp_ne_top`: the summable tail.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.Gauss

/-- **Elementary asymptotics.** If `m > 0` and `b > 0` there are `κ > 0` and `n₀` such that for all
`n ≥ n₀`: `m n + L > 0`, `b n - K ≥ 0` and `2 κ n (m n + L) ≤ (b n - K)²`. -/
theorem exists_pos_eventually_quadratic_of_pos {m b K L : ℝ} (hm : 0 < m) (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < m * n + L ∧ 0 ≤ b * n - K ∧ 2 * κ * n * (m * n + L) ≤ (b * n - K) ^ 2 := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = b / (4 * m) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; positivity
  have htm : 2 * (t * m) < b := by
    have : t * m = b / 4 := by rw [ht]; field_simp
    rw [this]; linarith
  obtain ⟨κ', hκ', n₀, h⟩ := exists_pos_eventually_quadratic (m := t * m) (c := b) (K := K)
    (L := t * L) (mul_pos htpos hm) htm
  refine ⟨(2 * (t * m) + κ') * t, by positivity, n₀, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h n hn
  have e : t * m * n + t * L = t * (m * n + L) := by ring
  rw [e] at h1 h3
  refine ⟨lt_of_mul_lt_mul_left (by rwa [mul_zero]) htpos.le, h2, ?_⟩
  calc 2 * ((2 * (t * m) + κ') * t) * n * (m * n + L)
      = 2 * (2 * (t * m) + κ') * n * (t * (m * n + L)) := by ring
    _ ≤ (b * n - K) ^ 2 := h3

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Summable one-point tails along shrinking circles.** Let `h` be a whole-plane Gaussian free
field, `s > 0`, `ξ > 0`, `A, η, M ∈ ℝ` with `η < ξ A log 2`, and `c k ∈ ℂ` with
`‖c k‖ ≤ M s / 2ᵏ`.  Then `∑ₖ P{-η k < ξ (h_{s/2ᵏ}(c k) + A log (s / 2ᵏ))} < ∞`, that is the
events `e^{-η k} < e^{ξ (h_{s/2ᵏ}(c k) + A log (s / 2ᵏ))}` have summable probabilities. -/
theorem tsum_measure_shell_circle_exp_ne_top (hh : IsWholePlaneGFF P hC hcirc)
    {s ξ A η M : ℝ} (hs : 0 < s) (hξ : 0 < ξ) (hη : η < ξ * A * Real.log 2) {c : ℕ → ℂ}
    (hc : ∀ k : ℕ, ‖c k‖ ≤ M * (s / 2 ^ k)) :
    ∑' k : ℕ, P {ω | -η * k < ξ * (hcirc ω (s / 2 ^ k) (c k) +
      A * Real.log (s / 2 ^ k))} ≠ ⊤ := by
  have hP := hh.isProbabilityMeasure
  have hm : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = A * Real.log 2 - η / ξ := ⟨_, rfl⟩
  have hbpos : 0 < b := by
    have : η / ξ < A * Real.log 2 := by rw [div_lt_iff₀ hξ]; linarith
    linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |M| * s := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * Real.log (1 + R) - Real.log s := ⟨_, rfl⟩
  obtain ⟨κ, hκ, n₀, hn₀⟩ :=
    exists_pos_eventually_quadratic_of_pos (K := A * Real.log s) (L := L) hm hbpos
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₀ ≤ n₁ ∧ s ≤ n₁ :=
    ⟨max n₀ ⌈s⌉₊, le_max_left _ _, (Nat.le_ceil s).trans (Nat.cast_le.2 (le_max_right _ _))⟩
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = 2 + Real.exp (κ * n₁) := ⟨_, rfl⟩
  have hM2 : 2 ≤ M' := by rw [hM']; linarith [Real.exp_pos (κ * n₁)]
  have hbound : ∀ k : ℕ, P {ω | -η * k < ξ * (hcirc ω (s / 2 ^ k) (c k) +
      A * Real.log (s / 2 ^ k))} ≤ ENNReal.ofReal (M' * Real.exp (-(κ * k))) := by
    intro k
    by_cases hk : k < n₁
    · -- small levels: the probability is at most one
      refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hkr : (k : ℝ) ≤ n₁ := Nat.cast_le.2 hk.le
      have hexp : Real.exp (κ * k) ≤ Real.exp (κ * n₁) :=
        Real.exp_le_exp.2 (by nlinarith)
      have hmul : Real.exp (κ * k) * Real.exp (-(κ * k)) = 1 := by
        rw [← Real.exp_add]; simp
      have hle : Real.exp (κ * k) ≤ M' := by rw [hM']; linarith
      calc (1 : ℝ) = Real.exp (κ * k) * Real.exp (-(κ * k)) := hmul.symm
        _ ≤ M' * Real.exp (-(κ * k)) := mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    · -- large levels: Gaussian tail
      have hk' : n₁ ≤ k := not_lt.1 hk
      obtain ⟨hV, hapos, hq⟩ := hn₀ k (hn₁.1.trans hk')
      set r := s / 2 ^ k with hr
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      have hr0 : 0 < r := div_pos hs h2k
      have hsk : s ≤ k := hn₁.2.trans (Nat.cast_le.2 hk')
      have hkk : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
      have hr1 : r ≤ 1 := (div_le_one h2k).2 (hsk.trans hkk.le)
      have hzn : ‖c k‖ ≤ R * 1 := by
        refine (hc k).trans ?_
        rw [mul_one, hR]
        calc M * r ≤ |M| * r := mul_le_mul_of_nonneg_right (le_abs_self M) hr0.le
          _ ≤ |M| * s :=
            mul_le_mul_of_nonneg_left (div_le_self hs.le (one_le_pow₀ one_le_two)) (abs_nonneg M)
      have hvar := hh.variance_circle_sub_start_le hr0 hr1 one_pos hR0 hzn
      rw [mul_one] at hvar
      have hlog : Real.log r = Real.log s - k * Real.log 2 := by
        rw [hr, Real.log_div hs.ne' h2k.ne', Real.log_pow]
      have hlogr : -Real.log r + 2 * Real.log (1 + R) = Real.log 2 * k + L := by
        rw [hlog, hL]; ring
      rw [hlogr] at hvar
      have htail := hh.measure_circle_sub_ge_le hr0 one_pos (c k) 0 hV hvar hapos
      have hone := hh.ae_circleAverage_one_zero
      have hincl : {ω | -η * k < ξ * (hcirc ω r (c k) + A * Real.log r)} ⊆
          {ω | b * k - A * Real.log s ≤ hcirc ω r (c k)} := by
        intro ω hω
        simp only [mem_ofPred_eq] at hω ⊢
        rw [hlog] at hω
        have e : ξ * (b * k - A * Real.log s) =
            ξ * A * Real.log 2 * k - η * k - ξ * A * Real.log s := by
          rw [hb]; field_simp
        refine le_of_lt (lt_of_mul_lt_mul_left ?_ hξ.le)
        rw [e]
        linarith
      have hsub : {ω | b * k - A * Real.log s ≤ hcirc ω r (c k)} ≤ᵐ[P]
          {ω | b * k - A * Real.log s ≤ |hcirc ω r (c k) - hcirc ω 1 0|} :=
        hone.mono fun ω h0 hω => by
          simp only [mem_ofPred_eq] at hω ⊢
          rw [h0, sub_zero]
          exact hω.trans (le_abs_self _)
      refine (measure_mono hincl).trans ((measure_mono_ae hsub).trans (htail.trans ?_))
      refine ENNReal.ofReal_le_ofReal ?_
      have hq' : κ * k ≤ (b * k - A * Real.log s) ^ 2 / (2 * (Real.log 2 * k + L)) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith [hq]
      exact mul_le_mul hM2 (Real.exp_le_exp.2 (neg_le_neg hq')) (Real.exp_pos _).le (by linarith)
  -- summability
  have hterm : ∀ k : ℕ, ENNReal.ofReal (M' * Real.exp (-(κ * k))) =
      ENNReal.ofReal (M' * (Real.exp (-κ)) ^ k) := fun k => by
    congr 1
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  have hsum : Summable fun k : ℕ => M' * (Real.exp (-κ)) ^ k :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (by linarith))).mul_left M'
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

end IsWholePlaneGFF

end LatticeProb.Gauss
