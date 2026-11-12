import Mathlib
import LatticeProb.LQG.LQGBallMassGrid

/-!
# Single-ball LQG mass tails from dyadic radii

The single-ball tail estimates `BallMassUpperTail` and `BallMassLowerTail` quantify over every small radius `r`.
For the γ-LQG measure of the whole-plane Gaussian free field they are proved by the exact scaling of the field
about the centre, which is available at the dyadic radii `2^{-j}`. This file shows that dyadic radii suffice:
a radius `r ∈ [2^{-(j+1)}, 2^{-j})` is compared with `2^{-j}` (upper tail, the ball grows) or with `2^{-(j+1)}`
(lower tail, the ball shrinks), and the factor `2^{|b|}` lost in the threshold is absorbed by moving the exponent
slightly towards `(2 ∓ γ)²/2`.

## Main results

* `exists_dyadicScale_bracket`: every `r ∈ (0, 1)` lies in some `[2^{-(j+1)}, 2^{-j})`.
* `ballMassUpperTail_of_dyadic`, `ballMassLowerTail_of_dyadic`: the single-ball tails from their dyadic forms.
* `wholePlaneLQGBallMassBoundsLP_of_dyadic`: the uniform estimate `WholePlaneLQGBallMassBoundsLP` from the dyadic
  single-ball tails for every γ-LQG measure of the whole-plane Gaussian free field.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

open LatticeProb.Gauss

namespace LatticeProb.LQG

/-- The dyadic scales are positive. -/
theorem dyadicScale_pos_bracket (j : ℕ) : 0 < dyadicScale j := pow_pos (by norm_num) j

/-- `2^{-(j+1)} = 2^{-j}/2`. -/
theorem dyadicScale_succ_eq_half (j : ℕ) : dyadicScale (j + 1) = dyadicScale j / 2 := by
  unfold dyadicScale
  rw [pow_succ]
  ring

/-- The dyadic scales decrease. -/
theorem dyadicScale_le_of_le {i j : ℕ} (h : i ≤ j) : dyadicScale j ≤ dyadicScale i :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- The dyadic scales are at most `1`. -/
theorem dyadicScale_le_one' (j : ℕ) : dyadicScale j ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

/-- Every `r ∈ (0, 1)` lies in a dyadic bracket `[2^{-(j+1)}, 2^{-j})`. -/
theorem exists_dyadicScale_bracket {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ j : ℕ, dyadicScale (j + 1) ≤ r ∧ r < dyadicScale j := by
  classical
  have hex : ∃ j : ℕ, dyadicScale (j + 1) ≤ r := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr0 (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨n, (dyadicScale_le_of_le (Nat.le_succ n)).trans hn.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  by_contra hcon
  push Not at hcon
  rcases hk : Nat.find hex with _ | k
  · rw [hk] at hcon
    have h1 : dyadicScale 0 = 1 := by simp [dyadicScale]
    linarith
  · exact Nat.find_min hex (show k < Nat.find hex by omega) (by rw [hk] at hcon; exact hcon)

/-- For `1 ≤ x ≤ 2`, `x^b ≤ 2^{|b|}`. -/
theorem rpow_le_two_rpow_abs {x b : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) : x ^ b ≤ (2 : ℝ) ^ |b| :=
  (Real.rpow_le_rpow_of_exponent_le hx1 (le_abs_self b)).trans
    (Real.rpow_le_rpow (by linarith) hx2 (abs_nonneg b))

/-- For `a > 0` and `K`, eventually as `r → 0+`, `K r^a < 1`. -/
theorem eventually_mul_rpow_lt_one (K : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), K * r ^ a < 1 := by
  have h := (tendsto_rpow_nhdsGT_zero ha).const_mul K
  rw [mul_zero] at h
  exact h.eventually (gt_mem_nhds one_pos)

/-- The single-ball upper tail from its dyadic form: if for every `b < (2-γ)²/2` the probability that a ball of
radius `2^{-j}` centred in the unit square has mass larger than `2^{-jb}` is at most `C 2^{-jθ}` for some
`θ > 2` and all large `j`, then `BallMassUpperTail P γ μ`. -/
theorem ballMassUpperTail_of_dyadic {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {μ : Ω → Measure ℂ}
    (h : ∀ b : ℝ, b < (2 - γ) ^ 2 / 2 → ∃ θ : ℝ, 2 < θ ∧ ∃ C : ℝ, ∃ j₀ : ℕ,
      ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ j : ℕ, j₀ ≤ j →
        P {ω | ENNReal.ofReal (dyadicScale j ^ b) < μ ω (ball z (dyadicScale j))} ≤
          ENNReal.ofReal (C * dyadicScale j ^ θ)) :
    BallMassUpperTail P γ μ := by
  intro b hb
  set b' := (b + (2 - γ) ^ 2 / 2) / 2 with hb'
  have hbb' : b < b' := by rw [hb']; linarith
  obtain ⟨θ, hθ, C, j₀, hC⟩ := h b' (by rw [hb']; linarith)
  obtain ⟨r₁, hr₁, H1⟩ :=
    exists_pos_forall_of_eventually_nhdsGT (eventually_mul_rpow_lt_one ((2 : ℝ) ^ |b'|) (sub_pos.2 hbb'))
  refine ⟨θ, hθ, max C 0 * 2 ^ θ, min r₁ (dyadicScale j₀), lt_min hr₁ (dyadicScale_pos_bracket j₀), ?_⟩
  intro z hz r hr hrr
  have hrj₀ : r < dyadicScale j₀ := lt_of_lt_of_le hrr (min_le_right _ _)
  obtain ⟨j, hj1, hj2⟩ := exists_dyadicScale_bracket hr (hrj₀.trans_le (dyadicScale_le_one' j₀))
  have hjj₀ : j₀ ≤ j := by
    by_contra hlt
    push Not at hlt
    have := dyadicScale_le_of_le (show j + 1 ≤ j₀ by omega)
    linarith
  set d := dyadicScale j with hd_def
  have hd : 0 < d := dyadicScale_pos_bracket j
  have hd2 : d ≤ 2 * r := by
    rw [dyadicScale_succ_eq_half] at hj1
    linarith
  have hthr : d ^ b' ≤ r ^ b := by
    have h1 : d ^ b' = (d / r) ^ b' * r ^ b' := by
      rw [← Real.mul_rpow (div_pos hd hr).le hr.le, div_mul_cancel₀ _ hr.ne']
    have h2 : r ^ b' = r ^ (b' - b) * r ^ b := by
      rw [← Real.rpow_add hr]
      ring_nf
    have h3 : (d / r) ^ b' ≤ (2 : ℝ) ^ |b'| :=
      rpow_le_two_rpow_abs (by rw [le_div_iff₀ hr]; linarith) (by rw [div_le_iff₀ hr]; linarith)
    have h4 := H1 r hr (lt_of_lt_of_le hrr (min_le_left _ _))
    have hrb : 0 ≤ r ^ b := Real.rpow_nonneg hr.le b
    have hrbb : 0 ≤ r ^ (b' - b) := Real.rpow_nonneg hr.le _
    rw [h1, h2]
    calc (d / r) ^ b' * (r ^ (b' - b) * r ^ b)
        ≤ (2 : ℝ) ^ |b'| * (r ^ (b' - b) * r ^ b) :=
          mul_le_mul_of_nonneg_right h3 (mul_nonneg hrbb hrb)
      _ = ((2 : ℝ) ^ |b'| * r ^ (b' - b)) * r ^ b := by ring
      _ ≤ 1 * r ^ b := mul_le_mul_of_nonneg_right h4.le hrb
      _ = r ^ b := one_mul _
  calc P {ω | ENNReal.ofReal (r ^ b) < μ ω (ball z r)}
      ≤ P {ω | ENNReal.ofReal (d ^ b') < μ ω (ball z d)} := by
        apply measure_mono
        intro ω hω
        show ENNReal.ofReal (d ^ b') < μ ω (ball z d)
        calc ENNReal.ofReal (d ^ b') ≤ ENNReal.ofReal (r ^ b) := ENNReal.ofReal_le_ofReal hthr
          _ < μ ω (ball z r) := hω
          _ ≤ μ ω (ball z d) := measure_mono (ball_subset_ball hj2.le)
    _ ≤ ENNReal.ofReal (C * d ^ θ) := hC z hz j hjj₀
    _ ≤ ENNReal.ofReal (max C 0 * 2 ^ θ * r ^ θ) := by
        apply ENNReal.ofReal_le_ofReal
        have hdθ : d ^ θ ≤ (2 * r) ^ θ := Real.rpow_le_rpow hd.le hd2 (by linarith)
        rw [Real.mul_rpow (by norm_num) hr.le] at hdθ
        have hdθ0 : 0 ≤ d ^ θ := Real.rpow_nonneg hd.le θ
        calc C * d ^ θ ≤ max C 0 * d ^ θ := mul_le_mul_of_nonneg_right (le_max_left _ _) hdθ0
          _ ≤ max C 0 * (2 ^ θ * r ^ θ) := mul_le_mul_of_nonneg_left hdθ (le_max_right _ _)
          _ = max C 0 * 2 ^ θ * r ^ θ := by ring

/-- The single-ball lower tail from its dyadic form: if for every `c > (2+γ)²/2` the probability that a ball of
radius `2^{-j}` centred in the unit square has mass smaller than `2^{-jc}` is at most `C 2^{-jθ}` for some
`θ > 2` and all large `j`, then `BallMassLowerTail P γ μ`. -/
theorem ballMassLowerTail_of_dyadic {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {μ : Ω → Measure ℂ}
    (h : ∀ c : ℝ, (2 + γ) ^ 2 / 2 < c → ∃ θ : ℝ, 2 < θ ∧ ∃ C : ℝ, ∃ j₀ : ℕ,
      ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ j : ℕ, j₀ ≤ j →
        P {ω | μ ω (ball z (dyadicScale j)) < ENNReal.ofReal (dyadicScale j ^ c)} ≤
          ENNReal.ofReal (C * dyadicScale j ^ θ)) :
    BallMassLowerTail P γ μ := by
  intro c hc
  set c' := ((2 + γ) ^ 2 / 2 + c) / 2 with hc'
  have hc'c : c' < c := by rw [hc']; linarith
  obtain ⟨θ, hθ, C, j₀, hC⟩ := h c' (by rw [hc']; linarith)
  obtain ⟨r₁, hr₁, H1⟩ :=
    exists_pos_forall_of_eventually_nhdsGT (eventually_mul_rpow_lt_one ((2 : ℝ) ^ |c|) (sub_pos.2 hc'c))
  refine ⟨θ, hθ, max C 0, min r₁ (dyadicScale j₀), lt_min hr₁ (dyadicScale_pos_bracket j₀), ?_⟩
  intro z hz r hr hrr
  have hrj₀ : r < dyadicScale j₀ := lt_of_lt_of_le hrr (min_le_right _ _)
  obtain ⟨j, hj1, hj2⟩ := exists_dyadicScale_bracket hr (hrj₀.trans_le (dyadicScale_le_one' j₀))
  have hjj₀ : j₀ ≤ j + 1 := by
    by_contra hlt
    push Not at hlt
    have := dyadicScale_le_of_le (show j + 1 ≤ j₀ by omega)
    linarith
  set d := dyadicScale (j + 1) with hd_def
  have hd : 0 < d := dyadicScale_pos_bracket (j + 1)
  have hr2 : r ≤ 2 * d := by
    rw [hd_def, dyadicScale_succ_eq_half]
    linarith
  have hthr : r ^ c ≤ d ^ c' := by
    have h1 : r ^ c = (r / d) ^ c * d ^ c := by
      rw [← Real.mul_rpow (div_pos hr hd).le hd.le, div_mul_cancel₀ _ hd.ne']
    have h2 : d ^ c = d ^ (c - c') * d ^ c' := by
      rw [← Real.rpow_add hd]
      ring_nf
    have h3 : (r / d) ^ c ≤ (2 : ℝ) ^ |c| :=
      rpow_le_two_rpow_abs (by rw [le_div_iff₀ hd]; linarith) (by rw [div_le_iff₀ hd]; linarith)
    have h4 := H1 d hd (lt_of_le_of_lt hj1 (lt_of_lt_of_le hrr (min_le_left _ _)))
    have hdc : 0 ≤ d ^ c' := Real.rpow_nonneg hd.le c'
    have hdcc : 0 ≤ d ^ (c - c') := Real.rpow_nonneg hd.le _
    rw [h1, h2]
    calc (r / d) ^ c * (d ^ (c - c') * d ^ c')
        ≤ (2 : ℝ) ^ |c| * (d ^ (c - c') * d ^ c') :=
          mul_le_mul_of_nonneg_right h3 (mul_nonneg hdcc hdc)
      _ = ((2 : ℝ) ^ |c| * d ^ (c - c')) * d ^ c' := by ring
      _ ≤ 1 * d ^ c' := mul_le_mul_of_nonneg_right h4.le hdc
      _ = d ^ c' := one_mul _
  calc P {ω | μ ω (ball z r) < ENNReal.ofReal (r ^ c)}
      ≤ P {ω | μ ω (ball z d) < ENNReal.ofReal (d ^ c')} := by
        apply measure_mono
        intro ω hω
        show μ ω (ball z d) < ENNReal.ofReal (d ^ c')
        calc μ ω (ball z d) ≤ μ ω (ball z r) := measure_mono (ball_subset_ball hj1)
          _ < ENNReal.ofReal (r ^ c) := hω
          _ ≤ ENNReal.ofReal (d ^ c') := ENNReal.ofReal_le_ofReal hthr
    _ ≤ ENNReal.ofReal (C * d ^ θ) := hC z hz (j + 1) hjj₀
    _ ≤ ENNReal.ofReal (max C 0 * r ^ θ) := by
        apply ENNReal.ofReal_le_ofReal
        have hdθ : d ^ θ ≤ r ^ θ := Real.rpow_le_rpow hd.le hj1 (by linarith)
        have hdθ0 : 0 ≤ d ^ θ := Real.rpow_nonneg hd.le θ
        calc C * d ^ θ ≤ max C 0 * d ^ θ := mul_le_mul_of_nonneg_right (le_max_left _ _) hdθ0
          _ ≤ max C 0 * r ^ θ := mul_le_mul_of_nonneg_left hdθ (le_max_right _ _)

/-- The literature statement `WholePlaneLQGBallMassBoundsLP` (Ding and Gwynne 2020, Lemma 3.8, whole-plane case)
from the dyadic single-ball upper and lower tail estimates for every γ-LQG measure of the whole-plane Gaussian
free field. -/
theorem wholePlaneLQGBallMassBoundsLP_of_dyadic {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → ∀ μ : Ω → Measure ℂ,
      IsLQGMeasureOfField P γ 0 hcirc μ →
        (∀ b : ℝ, b < (2 - γ) ^ 2 / 2 → ∃ θ : ℝ, 2 < θ ∧ ∃ C : ℝ, ∃ j₀ : ℕ,
          ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ j : ℕ, j₀ ≤ j →
            P {ω | ENNReal.ofReal (dyadicScale j ^ b) < μ ω (ball z (dyadicScale j))} ≤
              ENNReal.ofReal (C * dyadicScale j ^ θ)) ∧
        (∀ c : ℝ, (2 + γ) ^ 2 / 2 < c → ∃ θ : ℝ, 2 < θ ∧ ∃ C : ℝ, ∃ j₀ : ℕ,
          ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ j : ℕ, j₀ ≤ j →
            P {ω | μ ω (ball z (dyadicScale j)) < ENNReal.ofReal (dyadicScale j ^ c)} ≤
              ENNReal.ofReal (C * dyadicScale j ^ θ))) :
    WholePlaneLQGBallMassBoundsLP P γ hC hcirc :=
  wholePlaneLQGBallMassBoundsLP_of_single fun hh hγ0 hγ2 μ hμ =>
    ⟨ballMassUpperTail_of_dyadic (h hh hγ0 hγ2 μ hμ).1, ballMassLowerTail_of_dyadic (h hh hγ0 hγ2 μ hμ).2⟩

end LatticeProb.LQG
