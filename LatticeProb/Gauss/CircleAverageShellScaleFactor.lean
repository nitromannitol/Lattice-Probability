import LatticeProb.Gauss.CircleAverageDyadicSum

/-!
# One-point tails of circle averages along shrinking circles near a given point

For a whole-plane Gaussian free field `h`, the circle average `h_r(z)` with `r ≤ 1` and
`‖z‖ ≤ R` is a centred Gaussian variable (once the additive constant is fixed by `h_1(0) = 0`)
of variance at most `-log r + 2 log (1 + R)`, hence has a Gaussian upper tail.  Summing along the
dyadic radii `s / 2ᵏ` with centres `c k`, `‖c k‖ ≤ M s / 2ᵏ`, gives a finite total tail.

* `IsWholePlaneGFF.measure_ge_circle_le_of_norm_le`: the one-point Gaussian tail.
* `exists_pos_eventually_quadratic_single`: an elementary growth estimate.
* `tsum_ofReal_mul_exp_ne_top`: geometric sums of `M e^{-κ k}` are finite.
* `IsWholePlaneGFF.tsum_measure_shell_scaleFactor_ne_top`: the finiteness of the sum over the
  dyadic shells.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace LatticeProb.Gauss

/-- For `m, c > 0` and all `K, L`, there are `κ > 0` and `n₀` such that for `n ≥ n₀`:
`0 < m n + L`, `0 ≤ c n - K` and `2 κ n (m n + L) ≤ (c n - K)²`. -/
theorem exists_pos_eventually_quadratic_single {m c K L : ℝ} (hm : 0 < m) (hc : 0 < c) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < m * n + L ∧ 0 ≤ c * n - K ∧ 2 * κ * n * (m * n + L) ≤ (c * n - K) ^ 2 := by
  refine ⟨c ^ 2 / (4 * m), by positivity, ⌈8 * (|L| / m) + 4 * (|K| / c) + 1⌉₊, fun n hn => ?_⟩
  have hn' : 8 * (|L| / m) + 4 * (|K| / c) + 1 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.2 hn)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |L| / m := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |K| / c := ⟨_, rfl⟩
  rw [← hA, ← hB] at hn'
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hLA : |L| = m * A := by rw [hA]; field_simp
  have hKB : |K| = c * B := by rw [hB]; field_simp
  have hL1 : L ≤ m * A := hLA ▸ le_abs_self L
  have hL2 : -(m * A) ≤ L := hLA ▸ neg_abs_le L
  have hK1 : K ≤ c * B := hKB ▸ le_abs_self K
  have hK2 : -(c * B) ≤ K := hKB ▸ neg_abs_le K
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hmn := mul_le_mul_of_nonneg_left hn' hm.le
  have hcn := mul_le_mul_of_nonneg_left hn' hc.le
  have hmA := mul_nonneg hm.le hA0
  have hmB := mul_nonneg hm.le hB0
  have hcA := mul_nonneg hc.le hA0
  have hcB := mul_nonneg hc.le hB0
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have h1 : m * n + L ≤ m * (n + A) := by nlinarith
    have h2 : c * (n - B) ≤ c * n - K := by nlinarith
    have h3 : 0 ≤ c * (n - B) := mul_nonneg hc.le (by linarith)
    have h4 : (c * (n - B)) ^ 2 ≤ (c * n - K) ^ 2 := pow_le_pow_left₀ h3 h2 2
    have h5 : 2 * (c ^ 2 / (4 * m)) * n * (m * n + L) ≤
        2 * (c ^ 2 / (4 * m)) * n * (m * (n + A)) := by
      apply mul_le_mul_of_nonneg_left h1
      positivity
    have h6 : 2 * (c ^ 2 / (4 * m)) * n * (m * (n + A)) = c ^ 2 / 2 * (n * (n + A)) := by
      field_simp
      ring
    have h7 : n * (n + A) ≤ 2 * (n - B) ^ 2 := by nlinarith
    have h8 : c ^ 2 / 2 * (n * (n + A)) ≤ (c * (n - B)) ^ 2 := by
      calc c ^ 2 / 2 * (n * (n + A)) ≤ c ^ 2 / 2 * (2 * (n - B) ^ 2) :=
            mul_le_mul_of_nonneg_left h7 (by positivity)
        _ = (c * (n - B)) ^ 2 := by ring
    linarith

/-- Geometric sums of `M e^{-κ k}` are finite. -/
theorem tsum_ofReal_mul_exp_ne_top {M κ : ℝ} (hM : 0 ≤ M) (hκ : 0 < κ) :
    ∑' k : ℕ, ENNReal.ofReal (M * Real.exp (-(κ * k))) ≠ ⊤ := by
  have hg : Summable fun k : ℕ => M * (Real.exp (-κ)) ^ k :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (by linarith))).mul_left M
  have hterm : ∀ k : ℕ, M * Real.exp (-(κ * k)) = M * (Real.exp (-κ)) ^ k := fun k => by
    rw [← Real.exp_nat_mul]; congr 2; ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hg]
  exact ENNReal.ofReal_ne_top

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **One-point Gaussian tail.** For `0 < r ≤ 1`, `‖z‖ ≤ R` and `t ≥ 0`,
`P{t ≤ h_r(z)} ≤ 2 exp (-t² / (2 (-log r + 2 log (1 + R))))`, provided the denominator is
positive. -/
theorem measure_ge_circle_le_of_norm_le (hh : IsWholePlaneGFF P hC hcirc) {r R t : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R)
    (hV : 0 < -Real.log r + 2 * Real.log (1 + R)) (ht : 0 ≤ t) :
    P {ω | t ≤ hcirc ω r z} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (2 * (-Real.log r + 2 * Real.log (1 + R)))))) := by
  have hvar := hh.variance_circle_sub_start_le hr hr1 one_pos hR (w := z) (by rw [mul_one]; exact hz)
  rw [mul_one] at hvar
  have htail := hh.measure_circle_sub_ge_le hr one_pos z 0 hV hvar ht
  have hone := hh.ae_circleAverage_one_zero
  have hsub : {ω | t ≤ hcirc ω r z} ≤ᵐ[P] {ω | t ≤ |hcirc ω r z - hcirc ω 1 0|} :=
    hone.mono fun ω h0 hω => by
      simp only [mem_ofPred_eq] at hω ⊢
      rw [h0, sub_zero]
      exact hω.trans (le_abs_self _)
  exact (measure_mono_ae hsub).trans htail

/-- **Finite total tail over dyadic shells.** For `s > 0`, `ξ > 0` and `η < ξ (Q - α) log 2`,
and centres `c k` with `‖c k‖ ≤ M s / 2ᵏ`,
`∑ₖ P{e^{-η k} < e^{ξ (h_{s/2ᵏ}(c k) + (Q - α) log (s/2ᵏ))}} < ∞`. -/
theorem tsum_measure_shell_scaleFactor_ne_top (hG : IsWholePlaneGFF P hC hcirc)
    {ξ Q α η s M : ℝ} (hξ : 0 < ξ) (hs : 0 < s) (hη : η < ξ * (Q - α) * Real.log 2)
    {c : ℕ → ℂ} (hc : ∀ k : ℕ, ‖c k‖ ≤ M * (s / 2 ^ k)) :
    ∑' k : ℕ, P {ω | Real.exp (-(η * k)) <
      Real.exp (ξ * (hcirc ω (s / 2 ^ k) (c k) + (Q - α) * Real.log (s / 2 ^ k)))} ≠ ⊤ := by
  have hP := hG.isProbabilityMeasure
  have hm : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = Real.log 2 := ⟨_, rfl⟩
  rw [← hmdef] at hm hη
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Q - α := ⟨_, rfl⟩
  rw [← hq] at hη ⊢
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |M| * s := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * Real.log (1 + R) - Real.log s := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = q * m - η / ξ := ⟨_, rfl⟩
  have hξc' : ξ * c' = ξ * q * m - η := by rw [hc']; field_simp
  have hc'pos : 0 < c' := by
    have : η / ξ < q * m := by rw [div_lt_iff₀ hξ]; linarith
    linarith
  obtain ⟨κ, hκ, n₀, hn₀⟩ :=
    exists_pos_eventually_quadratic_single (K := q * Real.log s) (L := L) hm hc'pos
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₁ = max n₀ ⌈s⌉₊ := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = 2 + Real.exp (κ * n₁) := ⟨_, rfl⟩
  have hM'2 : 2 ≤ M' := by rw [hM']; linarith [Real.exp_pos (κ * n₁)]
  have hbound : ∀ k : ℕ, P {ω | Real.exp (-(η * k)) <
      Real.exp (ξ * (hcirc ω (s / 2 ^ k) (c k) + q * Real.log (s / 2 ^ k)))} ≤
      ENNReal.ofReal (M' * Real.exp (-(κ * k))) := by
    intro k
    by_cases hk : k < n₁
    · refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have hkr : (k : ℝ) ≤ n₁ := Nat.cast_le.2 hk.le
      have h1 : Real.exp (κ * k) ≤ Real.exp (κ * n₁) := Real.exp_le_exp.2 (by nlinarith)
      have hmul : Real.exp (κ * k) * Real.exp (-(κ * k)) = 1 := by
        rw [← Real.exp_add]; simp
      calc (1 : ℝ) = Real.exp (κ * k) * Real.exp (-(κ * k)) := hmul.symm
        _ ≤ M' * Real.exp (-(κ * k)) :=
          mul_le_mul_of_nonneg_right (by rw [hM']; linarith) (Real.exp_pos _).le
    · have hk' : n₁ ≤ k := not_lt.1 hk
      obtain ⟨hV, hapos, hq2⟩ := hn₀ k (by rw [hn₁] at hk'; exact (le_max_left _ _).trans hk')
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      have hr0 : 0 < s / 2 ^ k := div_pos hs h2k
      have hsk : s ≤ k := by
        rw [hn₁] at hk'
        exact (Nat.le_ceil s).trans (Nat.cast_le.2 ((le_max_right _ _).trans hk'))
      have hk2 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
      have hr1 : s / 2 ^ k ≤ 1 := (div_le_one h2k).2 (hsk.trans hk2.le)
      have hz : ‖c k‖ ≤ R := by
        calc ‖c k‖ ≤ M * (s / 2 ^ k) := hc k
          _ ≤ |M| * (s / 2 ^ k) := mul_le_mul_of_nonneg_right (le_abs_self M) hr0.le
          _ ≤ |M| * s := mul_le_mul_of_nonneg_left
              (div_le_self hs.le (one_le_pow₀ (by norm_num))) (abs_nonneg M)
          _ = R := hR.symm
      have hlr : Real.log (s / 2 ^ k) = Real.log s - k * m := by
        rw [Real.log_div hs.ne' h2k.ne', Real.log_pow, hmdef]
      have hlogr : -Real.log (s / 2 ^ k) + 2 * Real.log (1 + R) = m * k + L := by
        rw [hlr, hL]; ring
      have hsub : {ω | Real.exp (-(η * k)) <
          Real.exp (ξ * (hcirc ω (s / 2 ^ k) (c k) + q * Real.log (s / 2 ^ k)))} ⊆
          {ω | c' * k - q * Real.log s ≤ hcirc ω (s / 2 ^ k) (c k)} := by
        intro ω hω
        have h1 := Real.exp_lt_exp.1 hω
        by_contra hlt
        have hlt' : hcirc ω (s / 2 ^ k) (c k) < c' * k - q * Real.log s := not_le.1 hlt
        have h2 := mul_lt_mul_of_pos_left hlt' hξ
        rw [hlr] at h1
        have h3 : ξ * c' * k = (ξ * q * m - η) * k := by rw [hξc']
        nlinarith
      have htail := hG.measure_ge_circle_le_of_norm_le hr0 hr1 hR0 hz
        (by rw [hlogr]; exact hV) hapos
      rw [hlogr] at htail
      refine (measure_mono hsub).trans (htail.trans ?_)
      apply ENNReal.ofReal_le_ofReal
      have hκk : κ * k ≤ (c' * k - q * Real.log s) ^ 2 / (2 * (m * k + L)) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith [hq2]
      exact mul_le_mul hM'2 (Real.exp_le_exp.2 (neg_le_neg hκk)) (Real.exp_pos _).le
        (by linarith)
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  exact tsum_ofReal_mul_exp_ne_top (by linarith) hκ

end IsWholePlaneGFF

end LatticeProb.Gauss
