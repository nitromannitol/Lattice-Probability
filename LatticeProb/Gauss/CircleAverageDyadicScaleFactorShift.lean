import LatticeProb.Gauss.CircleAverageShellScaleFactor

/-!
# Shifted double sum of dyadic one-point tails

For a whole-plane Gaussian free field `h`, consider the dyadic lattice of mesh `s / 2ⁿ` in the
square `[a, a + s] × [b, b + s]`.  We show that the double sum, over the shift index `k` and the
dyadic level `n`, of the one-point probabilities that `h_{s/2ⁿ}(z)` exceeds the level
`c n + d k - K` (with `c > 2 log 2`, `d > 0`) is finite, and the same for the exponential form
`e^{-θ n + ε k} < e^{ξ (h_r(z) + Q log r)}`.

* `IsWholePlaneGFF.tsum_measure_circle_ge_linear_ne_top`: along one circle the Gaussian upper tails
  at the levels `e + d k` are summable in `k`.
* `IsWholePlaneGFF.tsum_tsum_dyadic_measure_circle_ge_linear_ne_top`: the linear form.
* `IsWholePlaneGFF.tsum_tsum_dyadic_measure_scaleFactor_shift_ne_top`: the exponential form.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace LatticeProb.Gauss

/-- For `m, c > 0` and all `K, L`, eventually `c (m n + L) ≤ 2 m (c n - K)`. -/
theorem exists_eventually_ratio_ge {m c K L : ℝ} (hm : 0 < m) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → c * (m * n + L) ≤ 2 * m * (c * n - K) := by
  refine ⟨⌈(2 * m * |K| + c * |L|) / (m * c)⌉₊, fun n hn => ?_⟩
  have hn' : (2 * m * |K| + c * |L|) / (m * c) ≤ n := (Nat.le_ceil _).trans (Nat.cast_le.2 hn)
  have h1 : 2 * m * |K| + c * |L| ≤ n * (m * c) := (div_le_iff₀ (mul_pos hm hc)).1 hn'
  have h2 : m * K ≤ m * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) hm.le
  have h3 : c * L ≤ c * |L| := mul_le_mul_of_nonneg_left (le_abs_self L) hc.le
  nlinarith

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Summable Gaussian tails at linearly growing levels.** For a fixed circle `(r, z)`, any
`d > 0` and `e`, the series `∑ₖ P{e + d k ≤ h_r(z)}` is finite. -/
theorem tsum_measure_circle_ge_linear_ne_top (hh : IsWholePlaneGFF P hC hcirc) {r d e : ℝ}
    (hr : 0 < r) (z : ℂ) (hd : 0 < d) :
    ∑' k : ℕ, P {ω | e + d * k ≤ hcirc ω r z} ≠ ⊤ := by
  have hP := hh.isProbabilityMeasure
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = Var[fun ω => hcirc ω r z - hcirc ω 1 0; P] + 1 := ⟨_, rfl⟩
  have hvar0 : 0 ≤ Var[fun ω => hcirc ω r z - hcirc ω 1 0; P] := variance_nonneg _ _
  have hV : 0 < V := by rw [hVdef]; linarith
  have hvar : Var[fun ω => hcirc ω r z - hcirc ω 1 0; P] ≤ V := by rw [hVdef]; linarith
  have htail : ∀ t : ℝ, 0 ≤ t →
      P {ω | t ≤ hcirc ω r z} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (2 * V)))) := by
    intro t ht
    have h1 := hh.measure_circle_sub_ge_le hr one_pos z 0 hV hvar ht
    have hone := hh.ae_circleAverage_one_zero
    have hsub : {ω | t ≤ hcirc ω r z} ≤ᵐ[P] {ω | t ≤ |hcirc ω r z - hcirc ω 1 0|} :=
      hone.mono fun ω h0 hω => by
        simp only [mem_ofPred_eq] at hω ⊢
        rw [h0, sub_zero]
        exact hω.trans (le_abs_self _)
    exact (measure_mono_ae hsub).trans h1
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (2 * |e| / d)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = d ^ 2 / (8 * V) := ⟨_, rfl⟩
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hκV : κ * (2 * V) = d ^ 2 / 4 := by rw [hκ]; field_simp; ring
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 + Real.exp (κ * k₀) := ⟨_, rfl⟩
  have hM2 : 2 ≤ M := by rw [hM]; linarith [Real.exp_pos (κ * k₀)]
  have hbound : ∀ k : ℕ, P {ω | e + d * k ≤ hcirc ω r z} ≤
      ENNReal.ofReal (M * Real.exp (-(κ * k))) := by
    intro k
    by_cases hk : k < k₀
    · refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have hkr : (k : ℝ) ≤ k₀ := Nat.cast_le.2 hk.le
      have h1 : Real.exp (κ * k) ≤ Real.exp (κ * k₀) := Real.exp_le_exp.2 (by nlinarith)
      have hmul : Real.exp (κ * k) * Real.exp (-(κ * k)) = 1 := by
        rw [← Real.exp_add]; simp
      calc (1 : ℝ) = Real.exp (κ * k) * Real.exp (-(κ * k)) := hmul.symm
        _ ≤ M * Real.exp (-(κ * k)) :=
          mul_le_mul_of_nonneg_right (by rw [hM]; linarith) (Real.exp_pos _).le
    · have hk' : k₀ ≤ k := not_lt.1 hk
      have hkr : (k₀ : ℝ) ≤ k := Nat.cast_le.2 hk'
      have hdk : 2 * |e| ≤ d * k := by
        have h1 : 2 * |e| / d ≤ k := hk₀.trans hkr
        rw [div_le_iff₀ hd] at h1
        linarith
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero k
      have habs : -|e| ≤ e := neg_abs_le e
      have ht1 : d * k / 2 ≤ e + d * k := by linarith
      have ht0 : 0 ≤ d * k / 2 := by positivity
      have ht : 0 ≤ e + d * k := ht0.trans ht1
      have ht2 : (d * k / 2) ^ 2 ≤ (e + d * k) ^ 2 := pow_le_pow_left₀ ht0 ht1 2
      refine (htail _ ht).trans (ENNReal.ofReal_le_ofReal ?_)
      have hκk : κ * k ≤ (e + d * k) ^ 2 / (2 * V) := by
        rw [le_div_iff₀ (by linarith)]
        have h5 : κ * k * (2 * V) = d ^ 2 / 4 * k := by rw [← hκV]; ring
        rw [h5]
        have h6 : d ^ 2 / 4 * k ≤ d ^ 2 / 4 * k ^ 2 :=
          mul_le_mul_of_nonneg_left hkk (by positivity)
        nlinarith
      exact mul_le_mul hM2 (Real.exp_le_exp.2 (neg_le_neg hκk)) (Real.exp_pos _).le
        (by linarith)
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  exact tsum_ofReal_mul_exp_ne_top (by linarith) hκpos

/-- **Shifted double sum, linear form.** Let `h` be a whole-plane Gaussian free field, `s > 0`,
`c > 2 log 2` and `d > 0`.  Then
`∑ₖ ∑ₙ ∑_{i,j < 2ⁿ} P{c n + d k - K ≤ h_{s/2ⁿ}((a + i s/2ⁿ) + (b + j s/2ⁿ) i)} < ∞`. -/
theorem tsum_tsum_dyadic_measure_circle_ge_linear_ne_top (hG : IsWholePlaneGFF P hC hcirc)
    {a b s c d K : ℝ} (hs : 0 < s) (hc : 2 * Real.log 2 < c) (hd : 0 < d) :
    ∑' k : ℕ, ∑' n : ℕ, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
      P {ω | c * n + d * k - K ≤
        hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩} ≠ ⊤ := by
  have hP := hG.isProbabilityMeasure
  have hm : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = Real.log 2 := ⟨_, rfl⟩
  rw [← hmdef] at hm hc
  have hcpos : 0 < c := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |a| + |b| + 2 * s := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * Real.log (1 + R) - Real.log s := ⟨_, rfl⟩
  obtain ⟨κ, hκ, n₀, hn₀⟩ := exists_pos_eventually_quadratic (K := K) (L := L) hm hc
  obtain ⟨n₂, hn₂⟩ := exists_eventually_ratio_ge (K := K) (L := L) hm hcpos
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₁ = max (max n₀ n₂) ⌈s⌉₊ := ⟨_, rfl⟩
  obtain ⟨κ₂, hκ₂def⟩ : ∃ κ₂ : ℝ, κ₂ = d * c / (2 * m) := ⟨_, rfl⟩
  have hκ₂pos : 0 < κ₂ := by rw [hκ₂def]; positivity
  have hκ₂ : κ₂ * (2 * m) = d * c := by rw [hκ₂def]; field_simp
  have h2pow : ∀ n : ℕ, (2 : ℝ) ^ n = Real.exp (m * n) := fun n => by
    rw [mul_comm, Real.exp_nat_mul, hmdef, Real.exp_log two_pos]
  -- the levels `n ≥ n₁`: uniform Gaussian tail
  have hlarge : ∀ n : ℕ, n₁ ≤ n → ∀ k : ℕ,
      ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
        P {ω | c * n + d * k - K ≤
          hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩} ≤
        ENNReal.ofReal (Real.exp (-(κ * n)) * (2 * Real.exp (-(κ₂ * k)))) := by
    intro n hn k
    have hn0 : n₀ ≤ n := by
      rw [hn₁] at hn; exact ((le_max_left _ _).trans (le_max_left _ _)).trans hn
    have hn2 : n₂ ≤ n := by
      rw [hn₁] at hn; exact ((le_max_right _ _).trans (le_max_left _ _)).trans hn
    have hns : s ≤ n := by
      rw [hn₁] at hn
      exact (Nat.le_ceil s).trans (Nat.cast_le.2 ((le_max_right _ _).trans hn))
    obtain ⟨hV, hapos, hq⟩ := hn₀ n hn0
    have hx := hn₂ n hn2
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hr0 : 0 < s / 2 ^ n := div_pos hs h2n
    have hnn : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    have hr1 : s / 2 ^ n ≤ 1 := (div_le_one h2n).2 (hns.trans hnn.le)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hlogr : -Real.log (s / 2 ^ n) + 2 * Real.log (1 + R) = m * n + L := by
      rw [Real.log_div hs.ne' h2n.ne', Real.log_pow, hL, hmdef]; ring
    have ht : 0 ≤ c * n + d * k - K := by
      have : 0 ≤ d * k := by positivity
      linarith
    have hineq : ((2 * m + κ) * n + κ₂ * k) ≤
        (c * n + d * k - K) ^ 2 / (2 * (m * n + L)) := by
      rw [le_div_iff₀ (by linarith)]
      have h4 := mul_le_mul_of_nonneg_left hx (mul_nonneg hd.le hk0)
      have h3' : m * (κ₂ * k * (2 * (m * n + L))) ≤ m * (2 * d * k * (c * n - K)) := by
        have e1 : m * (κ₂ * k * (2 * (m * n + L))) = k * (m * n + L) * (κ₂ * (2 * m)) := by ring
        rw [e1, hκ₂]
        nlinarith [h4]
      have h3 : κ₂ * k * (2 * (m * n + L)) ≤ 2 * d * k * (c * n - K) :=
        le_of_mul_le_mul_left h3' hm
      nlinarith [sq_nonneg (d * k), hq, h3]
    have hterm : ∀ i ∈ Finset.range (2 ^ n), ∀ j ∈ Finset.range (2 ^ n),
        P {ω | c * n + d * k - K ≤
          hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩} ≤
        ENNReal.ofReal (2 * Real.exp (-((2 * m + κ) * n + κ₂ * k))) := by
      intro i hi j hj
      have hi' : i < 2 ^ n := Finset.mem_range.1 hi
      have hj' : j < 2 ^ n := Finset.mem_range.1 hj
      have hir : ∀ l : ℕ, l < 2 ^ n → (l : ℝ) * (s / 2 ^ n) ≤ s := fun l hl => by
        have : (l : ℝ) ≤ 2 ^ n := by exact_mod_cast hl.le
        calc (l : ℝ) * (s / 2 ^ n) ≤ 2 ^ n * (s / 2 ^ n) :=
              mul_le_mul_of_nonneg_right this hr0.le
          _ = s := by field_simp
      have hl0 : ∀ l : ℕ, 0 ≤ (l : ℝ) * (s / 2 ^ n) := fun l => by positivity
      have hzn : ‖(⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ : ℂ)‖ ≤ R := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        have e1 : |a + i * (s / 2 ^ n)| ≤ |a| + s :=
          (abs_add_le _ _).trans (by rw [abs_of_nonneg (hl0 i)]; linarith [hir i hi'])
        have e2 : |b + j * (s / 2 ^ n)| ≤ |b| + s :=
          (abs_add_le _ _).trans (by rw [abs_of_nonneg (hl0 j)]; linarith [hir j hj'])
        simp only []
        rw [hR]
        linarith
      have htail := hG.measure_ge_circle_le_of_norm_le hr0 hr1 hR0 hzn
        (by rw [hlogr]; exact hV) ht
      rw [hlogr] at htail
      refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg hineq)) two_pos.le
    calc ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
          P {ω | c * n + d * k - K ≤
            hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩}
        ≤ ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
            ENNReal.ofReal (2 * Real.exp (-((2 * m + κ) * n + κ₂ * k))) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
      _ = ((2 ^ n : ℕ) : ℝ≥0∞) * (((2 ^ n : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (2 * Real.exp (-((2 * m + κ) * n + κ₂ * k)))) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ENNReal.ofReal (((2 ^ n : ℕ) : ℝ) * (((2 ^ n : ℕ) : ℝ) *
            (2 * Real.exp (-((2 * m + κ) * n + κ₂ * k))))) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (Real.exp (-(κ * n)) * (2 * Real.exp (-(κ₂ * k)))) := by
          congr 1
          have e : Real.exp (m * n) * (Real.exp (m * n) * Real.exp (-((2 * m + κ) * n + κ₂ * k))) =
              Real.exp (-(κ * n)) * Real.exp (-(κ₂ * k)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
          push_cast
          rw [h2pow n]
          linear_combination 2 * e
  -- the levels `n < n₁`: finitely many circles, each with summable linear tails
  have hfin : ∀ n : ℕ, ∑' k : ℕ, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
      P {ω | c * n + d * k - K ≤
        hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩} ≠ ⊤ := by
    intro n
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine ENNReal.sum_ne_top.2 fun i _ => ?_
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine ENNReal.sum_ne_top.2 fun j _ => ?_
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have := hG.tsum_measure_circle_ge_linear_ne_top (e := c * n - K) (div_pos hs h2n)
      (⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ : ℂ) hd
    refine ne_top_of_le_ne_top this (ENNReal.tsum_le_tsum fun k => measure_mono ?_)
    intro ω hω
    have hω' : c * n + d * k - K ≤
        hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ := hω
    show c * n - K + d * k ≤ _
    linarith
  -- assembly
  let T : ℕ → ℕ → ℝ≥0∞ := fun k n => ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
    P {ω | c * n + d * k - K ≤
      hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩}
  show ∑' k : ℕ, ∑' n : ℕ, T k n ≠ ⊤
  have hpt : ∀ k n : ℕ, T k n ≤ (if n < n₁ then T k n else 0) +
      ENNReal.ofReal (Real.exp (-(κ * n)) * (2 * Real.exp (-(κ₂ * k)))) := by
    intro k n
    by_cases hn : n < n₁
    · simp only [hn, ↓reduceIte]
      exact le_self_add
    · simp only [hn, ↓reduceIte, zero_add]
      exact hlarge n (not_lt.1 hn) k
  have hsplit : ∀ k : ℕ, ∑' n : ℕ, T k n ≤ (∑ n ∈ Finset.range n₁, T k n) +
      ENNReal.ofReal (2 * Real.exp (-(κ₂ * k))) *
        ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(κ * n))) := by
    intro k
    calc ∑' n : ℕ, T k n ≤ ∑' n : ℕ, ((if n < n₁ then T k n else 0) +
            ENNReal.ofReal (Real.exp (-(κ * n)) * (2 * Real.exp (-(κ₂ * k))))) :=
          ENNReal.tsum_le_tsum (hpt k)
      _ = ∑' n : ℕ, (if n < n₁ then T k n else 0) +
            ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(κ * n)) * (2 * Real.exp (-(κ₂ * k)))) :=
          ENNReal.tsum_add
      _ = (∑ n ∈ Finset.range n₁, T k n) + ENNReal.ofReal (2 * Real.exp (-(κ₂ * k))) *
            ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(κ * n))) := by
          congr 1
          · rw [tsum_eq_sum (s := Finset.range n₁)]
            · apply Finset.sum_congr rfl
              intro n hn
              simp only [Finset.mem_range.1 hn, ↓reduceIte]
            · intro n hn
              have : ¬ n < n₁ := fun h => hn (Finset.mem_range.2 h)
              simp only [this, ↓reduceIte]
          · rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun n => ?_
            rw [mul_comm (Real.exp _) _, ENNReal.ofReal_mul (by positivity)]
  have hA : ∑' k : ℕ, ∑ n ∈ Finset.range n₁, T k n ≠ ⊤ := by
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    exact ENNReal.sum_ne_top.2 fun n _ => hfin n
  have hC : ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(κ * n))) ≠ ⊤ := by
    have := tsum_ofReal_mul_exp_ne_top (M := 1) zero_le_one hκ
    simpa only [one_mul] using this
  have hB : ∑' k : ℕ, ENNReal.ofReal (2 * Real.exp (-(κ₂ * k))) ≠ ⊤ :=
    tsum_ofReal_mul_exp_ne_top (by norm_num) hκ₂pos
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hsplit)
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
  exact ENNReal.add_ne_top.2 ⟨hA, ENNReal.mul_ne_top hB hC⟩

/-- **Shifted double sum, exponential form.** Let `h` be a whole-plane Gaussian free field,
`s, ξ, ε > 0`, `Q ∈ ℝ` and `θ < ξ (Q - 2) log 2`.  Then the series over the shift index `k` and the
dyadic level `n`, of the probabilities of the events `e^{-θ n + ε k} < e^{ξ (h_r(z) + Q log r)}`
over the dyadic centres `z` of mesh `r = s / 2ⁿ`, is finite. -/
theorem tsum_tsum_dyadic_measure_scaleFactor_shift_ne_top (hG : IsWholePlaneGFF P hC hcirc)
    {a b s ξ Q θ ε : ℝ} (hs : 0 < s) (hξ : 0 < ξ) (hε : 0 < ε)
    (hθ : θ < ξ * (Q - 2) * Real.log 2) :
    ∑' k : ℕ, ∑' n : ℕ, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
      P {ω | Real.exp (-(θ * n) + ε * k) <
        Real.exp (ξ * (hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ +
          Q * Real.log (s / 2 ^ n)))} ≠ ⊤ := by
  have hc : 2 * Real.log 2 < Q * Real.log 2 - θ / ξ := by
    have : θ / ξ < (Q - 2) * Real.log 2 := by
      rw [div_lt_iff₀ hξ]; linarith
    linarith
  have hd : 0 < ε / ξ := div_pos hε hξ
  refine ne_top_of_le_ne_top (hG.tsum_tsum_dyadic_measure_circle_ge_linear_ne_top
    (a := a) (b := b) (K := Q * Real.log s) hs hc hd) ?_
  refine ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun n =>
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => measure_mono ?_
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  have h1 := Real.exp_lt_exp.1 hω
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [Real.log_div hs.ne' h2n.ne', Real.log_pow] at h1
  have e : ξ * ((Q * Real.log 2 - θ / ξ) * n + ε / ξ * k - Q * Real.log s) =
      ξ * Q * Real.log 2 * n - θ * n + ε * k - ξ * Q * Real.log s := by
    field_simp
  refine le_of_lt (lt_of_mul_lt_mul_left ?_ hξ.le)
  rw [e]
  nlinarith [h1]

end IsWholePlaneGFF

end LatticeProb.Gauss
