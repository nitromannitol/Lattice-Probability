import LatticeProb.Gauss.CircleAverageTailUniform
import LatticeProb.Gauss.GFFAffineInvariance

/-!
# Summable one-point tails of circle averages on dyadic grids

For a whole-plane Gaussian free field `h`, a square `[a, a + s] × [b, b + s]` and `n ∈ ℕ`, put
`r = s / 2ⁿ` and let `zⁿ_{ij} = (a + i r) + (b + j r) i` for `0 ≤ i, j < 2ⁿ` be the lower-left
corners of the closed dyadic subsquares of level `n`.  If `c > 2 log 2`, the probabilities
`P{h_r(zⁿ_{ij}) ≥ c n - K}` are bounded, uniformly in `i, j < 2ⁿ`, by a sequence `pₙ` with
`∑ₙ 4ⁿ pₙ < ∞`: indeed `Var h_r(z) ≤ n log 2 + const` and the Gaussian tail gives
`pₙ ≲ exp (-(c n - K)² / (2 (n log 2 + const))) ≈ exp (-(c² / (2 log 2)) n)`, while
`c² / (2 log 2) > 2 log 2` exactly when `c > 2 log 2`.  This is the shape needed to feed a
Borel-Cantelli argument over the `4ⁿ` dyadic squares of level `n`.

* `LatticeProb.Gauss.exists_pos_eventually_quadratic`: the elementary asymptotic inequality;
* `IsWholePlaneGFF.exists_tsum_dyadic_circle_ge_le`: the summable tail, event `c n - K ≤ h_r(z)`;
* `IsWholePlaneGFF.exists_tsum_dyadic_circle_exp_le`: the same for the event
  `-θ n < ξ (h_r(z) + Q log r)`, when `ξ > 0` and `θ < ξ (Q - 2) log 2`.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.Gauss

/-- **Elementary asymptotics.** If `c > 2 m > 0` there are `κ > 0` and `n₀` such that for all
`n ≥ n₀`: `m n + L > 0`, `c n - K ≥ 0` and `2 (2 m + κ) n (m n + L) ≤ (c n - K)²`. -/
theorem exists_pos_eventually_quadratic {m c K L : ℝ} (hm : 0 < m) (hc : 2 * m < c) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < m * n + L ∧ 0 ≤ c * n - K ∧ 2 * (2 * m + κ) * n * (m * n + L) ≤ (c * n - K) ^ 2 := by
  have hcpos : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 - 4 * m ^ 2 := by nlinarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (c ^ 2 - 4 * m ^ 2) / (4 * m) := ⟨_, rfl⟩
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hκm : 4 * m * κ = c ^ 2 - 4 * m ^ 2 := by rw [hκ]; field_simp
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (c ^ 2 - 4 * m ^ 2) / 2 := ⟨_, rfl⟩
  have hApos : 0 < A := by rw [hA]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = -2 * c * K - 2 * (2 * m + κ) * L := ⟨_, rfl⟩
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (max (max (-L / m + 1) (K / c)) (|B| / A))
  refine ⟨κ, hκpos, n₀, fun n hn => ?_⟩
  have hnr : (n₀ : ℝ) ≤ n := Nat.cast_le.2 hn
  have h1 : -L / m + 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hn₀.trans hnr)
  have h2 : K / c ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hn₀.trans hnr)
  have h3 : |B| / A ≤ n := le_trans (le_max_right _ _) (hn₀.trans hnr)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1' : -L < n * m := (div_lt_iff₀ hm).1 (by linarith)
  have h2' : K ≤ n * c := (div_le_iff₀ hcpos).1 h2
  have h3' : |B| ≤ n * A := (div_le_iff₀ hApos).1 h3
  have key : (c * n - K) ^ 2 - 2 * (2 * m + κ) * n * (m * n + L) = A * n ^ 2 + B * n + K ^ 2 := by
    rw [hA, hB]
    linear_combination (-(n : ℝ) ^ 2 / 2) * hκm
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hBn : -|B| ≤ B := neg_abs_le B
  nlinarith [mul_nonneg hn0 (sub_nonneg.2 h3'), sq_nonneg K, mul_nonneg hn0 hApos.le,
    mul_nonneg hn0 (mul_nonneg hn0 hApos.le), mul_le_mul_of_nonneg_left hBn hn0]

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Summable dyadic one-point tails.** Let `h` be a whole-plane Gaussian free field, `s > 0`,
`a, b, K ∈ ℝ` and `c > 2 log 2`.  There are `pₙ ∈ [0, ∞]` with `∑ₙ 4ⁿ pₙ < ∞` such that for all
`n` and all `i, j < 2ⁿ`, the circle average `h_{s/2ⁿ}` at the point `(a + i s/2ⁿ) + (b + j s/2ⁿ) i`
is at least `c n - K` with probability at most `pₙ`. -/
theorem exists_tsum_dyadic_circle_ge_le (hh : IsWholePlaneGFF P hC hcirc) {a b s c K : ℝ}
    (hs : 0 < s) (hc : 2 * Real.log 2 < c) :
    ∃ p : ℕ → ℝ≥0∞, (∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      P {ω | c * n - K ≤ hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩} ≤ p n) ∧
      ∑' n, 4 ^ n * p n ≠ ⊤ := by
  have hP := hh.isProbabilityMeasure
  have hm : 0 < Real.log 2 := Real.log_pos one_lt_two
  set m := Real.log 2 with hmdef
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |a| + |b| + 2 * s := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * Real.log (1 + R) - Real.log s := ⟨_, rfl⟩
  obtain ⟨κ, hκ, n₀, hn₀⟩ := exists_pos_eventually_quadratic (K := K) (L := L) hm hc
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₀ ≤ n₁ ∧ s ≤ n₁ :=
    ⟨max n₀ ⌈s⌉₊, le_max_left _ _, (Nat.le_ceil s).trans (Nat.cast_le.2 (le_max_right _ _))⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 + Real.exp ((2 * m + κ) * n₁) := ⟨_, rfl⟩
  have hM2 : 2 ≤ M := by rw [hM]; linarith [Real.exp_pos ((2 * m + κ) * n₁)]
  have h4 : ∀ n : ℕ, (4 : ℝ) ^ n = Real.exp (2 * m * n) := fun n => by
    have : Real.exp (2 * m) = 4 := by
      rw [show 2 * m = m + m by ring, Real.exp_add, hmdef, Real.exp_log two_pos]; norm_num
    rw [mul_comm, Real.exp_nat_mul, this]
  refine ⟨fun n => ENNReal.ofReal (M * Real.exp (-((2 * m + κ) * n))), ?_, ?_⟩
  · intro n i j hi hj
    by_cases hn : n < n₁
    · -- small levels: the probability is at most one
      refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hnr : (n : ℝ) ≤ n₁ := Nat.cast_le.2 hn.le
      have hexp : Real.exp ((2 * m + κ) * n) ≤ Real.exp ((2 * m + κ) * n₁) :=
        Real.exp_le_exp.2 (by nlinarith)
      have : 1 ≤ M * Real.exp (-((2 * m + κ) * n)) := by
        have hpos := Real.exp_pos ((2 * m + κ) * n)
        have hmul : Real.exp ((2 * m + κ) * n) * Real.exp (-((2 * m + κ) * n)) = 1 := by
          rw [← Real.exp_add]; simp
        have hle : Real.exp ((2 * m + κ) * n) ≤ M := by rw [hM]; linarith
        calc (1 : ℝ) = Real.exp ((2 * m + κ) * n) * Real.exp (-((2 * m + κ) * n)) := hmul.symm
          _ ≤ M * Real.exp (-((2 * m + κ) * n)) :=
            mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      exact this
    · -- large levels: Gaussian tail
      have hn' : n₁ ≤ n := not_lt.1 hn
      obtain ⟨hV, hapos, hq⟩ := hn₀ n (hn₁.1.trans hn')
      set r := s / 2 ^ n with hr
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      have hr0 : 0 < r := div_pos hs h2n
      have hsn : s ≤ n := hn₁.2.trans (Nat.cast_le.2 hn')
      have hn2 : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
      have hr1 : r ≤ 1 := (div_le_one h2n).2 (hsn.trans hn2.le)
      have hir : ∀ k : ℕ, k < 2 ^ n → (k : ℝ) * r ≤ s := fun k hk => by
        have : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk.le
        calc (k : ℝ) * r ≤ 2 ^ n * r := mul_le_mul_of_nonneg_right this hr0.le
          _ = s := by rw [hr]; field_simp
      have hk0 : ∀ k : ℕ, 0 ≤ (k : ℝ) * r := fun k => by positivity
      set z : ℂ := ⟨a + i * r, b + j * r⟩ with hz
      have hzn : ‖z‖ ≤ R * 1 := by
        refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
        have e1 : |a + i * r| ≤ |a| + s :=
          (abs_add_le _ _).trans (by rw [abs_of_nonneg (hk0 i)]; linarith [hir i hi])
        have e2 : |b + j * r| ≤ |b| + s :=
          (abs_add_le _ _).trans (by rw [abs_of_nonneg (hk0 j)]; linarith [hir j hj])
        simp only [hz]
        rw [hR]
        linarith
      have hvar := hh.variance_circle_sub_start_le hr0 hr1 one_pos hR0 hzn
      rw [mul_one] at hvar
      have hlogr : -Real.log r + 2 * Real.log (1 + R) = m * n + L := by
        rw [hr, Real.log_div hs.ne' h2n.ne', Real.log_pow, hL, hmdef]; ring
      rw [hlogr] at hvar
      have htail := hh.measure_circle_sub_ge_le hr0 one_pos z 0 hV hvar hapos
      have hone := hh.ae_circleAverage_one_zero
      have hsub : {ω | c * n - K ≤ hcirc ω r z} ≤ᵐ[P] {ω | c * n - K ≤ |hcirc ω r z - hcirc ω 1 0|} :=
        hone.mono fun ω h0 hω => by
          simp only [mem_ofPred_eq] at hω ⊢
          rw [h0, sub_zero]
          exact hω.trans (le_abs_self _)
      refine (measure_mono_ae hsub).trans (htail.trans ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      have hq' : (2 * m + κ) * n ≤ (c * n - K) ^ 2 / (2 * (m * n + L)) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith [hq]
      exact mul_le_mul hM2 (Real.exp_le_exp.2 (neg_le_neg hq')) (Real.exp_pos _).le (by linarith)
  · -- summability
    have hterm : ∀ n : ℕ, (4 : ℝ≥0∞) ^ n * ENNReal.ofReal (M * Real.exp (-((2 * m + κ) * n))) =
        ENNReal.ofReal (M * (Real.exp (-κ)) ^ n) := fun n => by
      have e4 : (4 : ℝ≥0∞) ^ n = ENNReal.ofReal ((4 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]; simp
      rw [e4, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [h4 n, ← Real.exp_nat_mul,
        show (n : ℝ) * -κ = 2 * m * n + -((2 * m + κ) * n) by ring, Real.exp_add]
      ring
    have hsum : Summable fun n : ℕ => M * (Real.exp (-κ)) ^ n :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.2 (by linarith))).mul_left M
    beta_reduce
    rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact ENNReal.ofReal_ne_top

/-- **Summable dyadic one-point tails, exponential form.** Let `h` be a whole-plane Gaussian free
field, `s > 0`, `ξ > 0`, `Q ∈ ℝ` and `θ < ξ (Q - 2) log 2`.  There are `pₙ ∈ [0, ∞]` with
`∑ₙ 4ⁿ pₙ < ∞` such that for all `n` and all `i, j < 2ⁿ`, with `r = s / 2ⁿ` and
`z = (a + i r) + (b + j r) i`, the event `e^{-θ n} < e^{ξ (h_r(z) + Q log r)}` (that is,
`-θ n < ξ (h_r(z) + Q log r)`) has probability at most `pₙ`. -/
theorem exists_tsum_dyadic_circle_exp_le (hh : IsWholePlaneGFF P hC hcirc) {a b s ξ Q θ : ℝ}
    (hs : 0 < s) (hξ : 0 < ξ) (hθ : θ < ξ * (Q - 2) * Real.log 2) :
    ∃ p : ℕ → ℝ≥0∞, (∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      P {ω | -θ * n < ξ * (hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ +
        Q * Real.log (s / 2 ^ n))} ≤ p n) ∧ ∑' n, 4 ^ n * p n ≠ ⊤ := by
  have hc : 2 * Real.log 2 < Q * Real.log 2 - θ / ξ := by
    have : θ / ξ < (Q - 2) * Real.log 2 := by
      rw [div_lt_iff₀ hξ]; linarith
    linarith
  obtain ⟨p, hp, hsum⟩ :=
    hh.exists_tsum_dyadic_circle_ge_le (a := a) (b := b) (K := Q * Real.log s) hs hc
  refine ⟨p, fun n i j hi hj => (measure_mono ?_).trans (hp n i j hi hj), hsum⟩
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [Real.log_div hs.ne' h2n.ne', Real.log_pow] at hω
  have e : ξ * ((Q * Real.log 2 - θ / ξ) * n - Q * Real.log s) =
      ξ * Q * Real.log 2 * n - θ * n - ξ * Q * Real.log s := by
    field_simp
  refine le_of_lt (lt_of_mul_lt_mul_left ?_ hξ.le)
  rw [e]
  linarith

end IsWholePlaneGFF

end LatticeProb.Gauss
