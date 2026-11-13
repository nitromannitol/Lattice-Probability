import LatticeProb.Prob.BrownianStepTimeTails
import LatticeProb.Prob.MulExpNegRpow

/-!
# Superpolynomial tails for the displacement times of Brownian motion

Let `B` be a Brownian motion on `ℝ ^ d` started at `0`, let `σ_k(r)` be its successive times of
displacement by `r` (`stepTime`), and let `ζ ∈ (0, 1)`.

* `measure_exit_by_stepTime_superpoly`: the probability that `‖B t‖ ≥ 1` for some `t ≤ σ_K(r)`, with
  `K = ⌊r ^ -(2 - ζ)⌋`, is at most `C r ^ p` for every `p : ℕ`: with superpolynomially high
  probability `B` has not left the unit ball before time `σ_K(r)`.
* `measure_stays_in_ball_superpoly`: the probability that `‖B t‖ < 1` for all `t < σ_K(r)`, with
  `K = ⌊r ^ -(2 + ζ)⌋`, is at most `C r ^ p` for every `p : ℕ`: with superpolynomially high
  probability `B` has left the unit ball by time `σ_K(r)`.

The constants depend on `d`, `ζ` and `p` only.  The events do not depend on the time parametrization
of `B`, so the statements hold for Brownian motion with any constant diffusivity.
-/

open MeasureTheory ProbabilityTheory Set

open scoped NNReal ENNReal

universe u

namespace LatticeProb

/-- **The motion stays in the unit ball up to `σ_K(r)`, `K ≈ r ^ -(2 - ζ)`, with superpolynomially
high probability** (no exit before `σ_K(r)` fails with probability at most `C r ^ p`). -/
theorem measure_exit_by_stepTime_superpoly (d : ℕ) (hd : 0 < d) {ζ : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)), IsBrownianSpace d 0 B P →
      ∀ r : ℝ≥0, 0 < r → r < 1 →
      P {ω | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ stepTime (fun t => B t ω) (r : ℝ)
            ⌊(r : ℝ) ^ (-(2 - ζ))⌋₊ ∧ 1 ≤ ‖B t ω‖}
        ≤ ENNReal.ofReal (C * (r : ℝ) ^ p) := by
  obtain ⟨C1, c1, hC1, hc1, hmain⟩ := measure_exit_by_stepTime_le.{u} d
  set q := gaussTail (2 * Real.sqrt d) with hq
  have hq0 : 0 < q := gaussTail_pos _
  obtain ⟨Ca, hCa0, hCa⟩ := exists_mul_exp_neg_rpow_le (a := 0) (κ := 2 - ζ) (c := q / 8)
    (by linarith) (by positivity) p
  obtain ⟨Cb, hCb0, hCb⟩ := exists_mul_exp_neg_rpow_le (a := 0) (κ := ζ) (c := c1 / (2 / q + 2))
    hζ0 (by positivity) p
  refine ⟨2 * Ca + C1 * Cb, ?_⟩
  intro Ω _ P _ B hB r hr hr1
  have hr0 : (0 : ℝ) < r := hr
  have hr1' : (r : ℝ) < 1 := hr1
  set x : ℝ := (r : ℝ) ^ (-(2 - ζ)) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1'.le (by linarith)
  set K : ℕ := ⌊x⌋₊ with hK
  have hK1 : 1 ≤ K := Nat.le_floor (by simpa using hx1)
  have hKx : (K : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxK : x ≤ 2 * K := by
    have := Nat.lt_floor_add_one x
    have h1 : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    linarith
  set m : ℕ := ⌈2 * K / q⌉₊ with hm
  have hm0 : 0 < m := Nat.ceil_pos.2 (by positivity)
  have hmK : 2 * K / q ≤ m := Nat.le_ceil _
  have hmK' : (m : ℝ) ≤ 2 * K / q + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hKm : (K : ℝ) ≤ m * q / 2 := by
    have := (div_le_iff₀ hq0).1 hmK
    linarith
  have hrζ : 0 < (r : ℝ) ^ ζ := by positivity
  have hxr : x * (r : ℝ) ^ 2 = (r : ℝ) ^ ζ := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_add hr0]
    congr 1
    push_cast
    ring
  have hr2 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ ζ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1'.le (by push_cast; linarith)
  set T : ℝ := (2 / q + 2) * (r : ℝ) ^ ζ with hT
  have hmT : (m : ℝ) * (r : ℝ) ^ 2 < T := by
    calc (m : ℝ) * (r : ℝ) ^ 2 ≤ (2 * K / q + 1) * (r : ℝ) ^ 2 := by gcongr
      _ ≤ (2 * x / q + 1) * (r : ℝ) ^ 2 := by gcongr
      _ = (2 / q) * (x * (r : ℝ) ^ 2) + (r : ℝ) ^ 2 := by field_simp
      _ ≤ (2 / q) * (r : ℝ) ^ ζ + (r : ℝ) ^ ζ := by rw [hxr]; linarith
      _ < T := by rw [hT]; nlinarith
  have h := hmain Ω P B hB hd r hr K m hm0 hKm T hmT
  have h3 : x ≤ m * q := (div_le_iff₀ hq0).1 (le_trans (div_le_div_of_nonneg_right hxK hq0.le) hmK)
  have e1 : Real.exp (-(m * q ^ 2 / 8)) ≤ Real.exp (-((q / 8) * x)) := by
    apply Real.exp_le_exp.2
    nlinarith
  have e2 : Real.exp (-(c1 * 1 ^ 2 / T))
      = Real.exp (-((c1 / (2 / q + 2)) * (r : ℝ) ^ (-ζ))) := by
    congr 2
    rw [Real.rpow_neg hr0.le, hT]
    field_simp
  have hA : Real.exp (-((q / 8) * x)) ≤ Ca * (r : ℝ) ^ p := by
    have := hCa r hr0 hr1'
    simpa [hx] using this
  have hB' : Real.exp (-((c1 / (2 / q + 2)) * (r : ℝ) ^ (-ζ))) ≤ Cb * (r : ℝ) ^ p := by
    have := hCb r hr0 hr1'
    simpa using this
  calc _ ≤ ENNReal.ofReal (2 * Real.exp (-(m * q ^ 2 / 8)))
          + ENNReal.ofReal (C1 * Real.exp (-(c1 * 1 ^ 2 / T))) := h
    _ = ENNReal.ofReal (2 * Real.exp (-(m * q ^ 2 / 8)) + C1 * Real.exp (-(c1 * 1 ^ 2 / T))) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((2 * Ca + C1 * Cb) * (r : ℝ) ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        rw [e2]
        have h4 : C1 * Real.exp (-((c1 / (2 / q + 2)) * (r : ℝ) ^ (-ζ))) ≤ C1 * (Cb * (r : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left hB' hC1.le
        nlinarith

/-- **The motion leaves the unit ball by `σ_K(r)`, `K ≈ r ^ -(2 + ζ)`, with superpolynomially high
probability** (staying in the ball up to `σ_K(r)` has probability at most `C r ^ p`). -/
theorem measure_stays_in_ball_superpoly (d : ℕ) (hd : 0 < d) {ζ : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)), IsBrownianSpace d 0 B P →
      ∀ r : ℝ≥0, 0 < r → r < 1 →
      P {ω | ∀ t : ℝ≥0, (t : ℝ≥0∞) < stepTime (fun t => B t ω) (r : ℝ)
            ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊ → ‖B t ω‖ < 1}
        ≤ ENNReal.ofReal (C * (r : ℝ) ^ p) := by
  obtain ⟨C1, c1, hC1, hc1, hmain⟩ := measure_stays_in_ball_le.{u} d
  set q := gaussTail (2 * Real.sqrt d) with hq
  have hq0 : 0 < q := gaussTail_pos _
  set M0 : ℕ := ⌈2 / q⌉₊ with hM0
  have hM0q : 2 / q ≤ M0 := Nat.le_ceil _
  set c3 : ℝ := (M0 + 1) * q ^ 2 / 8 with hc3
  set c4 : ℝ := c1 / (48 * (M0 + 1)) with hc4
  have hc3pos : 0 < c3 := by positivity
  have hc4pos : 0 < c4 := by positivity
  obtain ⟨Ca, hCa0, hCa⟩ := exists_mul_exp_neg_rpow_le (a := 0) (κ := ζ / 2) (c := c3)
    (by linarith) hc3pos p
  obtain ⟨Cb, hCb0, hCb⟩ := exists_mul_exp_neg_rpow_le (a := 2 + ζ) (κ := ζ / 2) (c := c4)
    (by linarith) hc4pos p
  refine ⟨2 * Ca + 2 * C1 * Cb, ?_⟩
  intro Ω _ P _ B hB r hr hr1
  have hr0 : (0 : ℝ) < r := hr
  have hr1' : (r : ℝ) < 1 := hr1
  set x : ℝ := (r : ℝ) ^ (-(2 + ζ)) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1'.le (by linarith)
  set K : ℕ := ⌊x⌋₊ with hK
  have hK1 : 1 ≤ K := Nat.le_floor (by simpa using hx1)
  have hKx : (K : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxK : x ≤ 2 * K := by
    have := Nat.lt_floor_add_one x
    have h1 : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    linarith
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.2 hK1
  set y : ℝ := (r : ℝ) ^ (-(ζ / 2)) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1'.le (by linarith)
  have hM0nn : (0 : ℝ) ≤ M0 := Nat.cast_nonneg M0
  have hMy : (M0 : ℝ) + 1 ≤ ((M0 : ℝ) + 1) * y := le_mul_of_one_le_right (by positivity) hy1
  set t0 : ℝ := 2 * (M0 + 1) * y with ht0
  have ht0pos : 0 < t0 := by positivity
  have ht02 : 2 ≤ t0 := by rw [ht0]; linarith
  set T : ℝ≥0 := Real.toNNReal t0 with hT
  have hTc : (T : ℝ) = t0 := Real.coe_toNNReal _ ht0pos.le
  set s : ℝ≥0 := Real.toNNReal (t0 / K) with hs
  have hsc : (s : ℝ) = t0 / K := Real.coe_toNNReal _ (by positivity)
  have hs0 : 0 < s := by rw [← NNReal.coe_pos, hsc]; positivity
  have hTK : T ≤ (K : ℝ≥0) * s := by
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast, hsc, hTc]
    exact le_of_eq (by field_simp)
  set m : ℕ := ⌈t0 / 2⌉₊ with hm
  have hm0 : 0 < m := Nat.ceil_pos.2 (by positivity)
  have hmt : t0 / 2 ≤ m := Nat.le_ceil _
  have hmt' : (m : ℝ) < t0 / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hq1 : 1 ≤ (m : ℝ) * q / 2 := by
    have h1 : 2 / q ≤ m := by
      calc 2 / q ≤ M0 := hM0q
        _ ≤ t0 / 2 := by rw [ht0]; linarith
        _ ≤ m := hmt
    have := (div_le_iff₀ hq0).1 h1
    linarith
  have hmT : (m : ℝ) < (T : ℝ) := by rw [hTc]; linarith
  have h := hmain Ω P B hB hd r hr K s T hs0 hTK m hm0 hq1 hmT
  have hfl : ⌊(T : ℝ) / s⌋₊ = K := by
    have : (T : ℝ) / s = K := by rw [hTc, hsc]; field_simp
    rw [this, Nat.floor_natCast]
  rw [hfl] at h
  have e1 : Real.exp (-(m * q ^ 2 / 8)) ≤ Real.exp (-(c3 * y)) := by
    apply Real.exp_le_exp.2
    have : (t0 / 2) * q ^ 2 ≤ m * q ^ 2 := mul_le_mul_of_nonneg_right hmt (sq_nonneg q)
    rw [hc3]
    rw [ht0] at this
    linarith
  have h1 : x * (r : ℝ) ^ 2 = (r : ℝ) ^ (-ζ) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_add hr0]
    congr 1
    push_cast
    ring
  have h2 : y * y = (r : ℝ) ^ (-ζ) := by
    rw [hy, ← Real.rpow_add hr0]
    congr 1
    ring
  have hyy : y * y ≤ 2 * ((r : ℝ) ^ 2 * K) := by
    rw [h2, ← h1]
    linarith [mul_le_mul_of_nonneg_right hxK (sq_nonneg (r : ℝ))]
  have hexp : c1 * ((r : ℝ) / 2) ^ 2 / (3 * (s : ℝ)) = c1 * ((r : ℝ) ^ 2 * K) / (12 * t0) := by
    rw [hsc]
    field_simp
    ring
  have hkey : c4 * y ≤ c1 * ((r : ℝ) ^ 2 * K) / (12 * t0) := by
    rw [le_div_iff₀ (by positivity)]
    have e : c4 * y * (12 * t0) = c1 * (y * y) / 2 := by
      rw [hc4, ht0]
      field_simp
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hyy hc1.le
    linarith
  have f2 : Real.exp (-(c1 * ((r : ℝ) / 2) ^ 2 / (3 * (s : ℝ)))) ≤ Real.exp (-(c4 * y)) := by
    apply Real.exp_le_exp.2
    rw [hexp]
    exact neg_le_neg hkey
  have f1 : ((K + 1 : ℕ) : ℝ) ≤ 2 * x := by
    push_cast
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    linarith
  have hA : Real.exp (-(c3 * y)) ≤ Ca * (r : ℝ) ^ p := by
    have := hCa r hr0 hr1'
    simpa [hy] using this
  have hB' : x * Real.exp (-(c4 * y)) ≤ Cb * (r : ℝ) ^ p := hCb r hr0 hr1'
  have hconv : ((K + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (C1 * Real.exp (-(c1 * ((r : ℝ) / 2) ^ 2
      / (3 * (s : ℝ))))) = ENNReal.ofReal (((K + 1 : ℕ) : ℝ) * (C1 * Real.exp (-(c1 *
        ((r : ℝ) / 2) ^ 2 / (3 * (s : ℝ)))))) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hbound : 2 * Real.exp (-(m * q ^ 2 / 8)) + ((K + 1 : ℕ) : ℝ) * (C1 * Real.exp (-(c1 *
      ((r : ℝ) / 2) ^ 2 / (3 * (s : ℝ))))) ≤ (2 * Ca + 2 * C1 * Cb) * (r : ℝ) ^ p := by
    have g1 : ((K + 1 : ℕ) : ℝ) * (C1 * Real.exp (-(c1 * ((r : ℝ) / 2) ^ 2 / (3 * (s : ℝ)))))
        ≤ (2 * x) * (C1 * Real.exp (-(c4 * y))) :=
      mul_le_mul f1 (mul_le_mul_of_nonneg_left f2 hC1.le) (by positivity) (by positivity)
    have g2 : (2 * x) * (C1 * Real.exp (-(c4 * y))) ≤ 2 * C1 * (Cb * (r : ℝ) ^ p) := by
      calc (2 * x) * (C1 * Real.exp (-(c4 * y))) = 2 * C1 * (x * Real.exp (-(c4 * y))) := by ring
        _ ≤ _ := by gcongr
    linarith [e1.trans hA, g1, g2]
  calc _ ≤ ENNReal.ofReal (2 * Real.exp (-(m * q ^ 2 / 8))) + ((K + 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (C1 * Real.exp (-(c1 * ((r : ℝ) / 2) ^ 2 / (3 * (s : ℝ))))) := h
    _ = ENNReal.ofReal (2 * Real.exp (-(m * q ^ 2 / 8)) + ((K + 1 : ℕ) : ℝ) *
        (C1 * Real.exp (-(c1 * ((r : ℝ) / 2) ^ 2 / (3 * (s : ℝ)))))) := by
        rw [hconv, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

end LatticeProb
