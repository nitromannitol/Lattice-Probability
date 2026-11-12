import Mathlib

/-!
# Super-exponential decay of a sequence satisfying a power recursion

Let `N ≥ 2`, and let `u : ℕ → ℝ` take values in `[0, ρ]` with `ρ < 1`. Suppose
`u (j+1) ≤ E j + (u j)^N` where `E j ≤ K exp(-c j²)` with `K, c > 0`. Then `u j ≤ M exp(-a j²)` for
some `M, a > 0`.

The proof has two phases.

* `LatticeProb.eventually_le_of_contraction_recursion`: since `(u j)^N ≤ ρ^(N-1) u j`, the
  sequence satisfies `u (j+1) ≤ E j + θ u j` with `θ = ρ^(N-1) < 1` and `E j → 0`, hence `u j → 0`.
* a closing induction: once `u J ≤ 1/4`, the choice `a = 2 log 2 / J²` with `J` large gives
  `u j ≤ exp(-a j²)` for every `j ≥ J`, because `exp(-a j²)^N ≤ exp(-a (j+1)²)/2` and
  `K exp(-c j²) ≤ exp(-a (j+1)²)/2` for `j ≥ J`.

* `LatticeProb.exists_superexp_decay_of_recursion`: the conclusion (with `M = 4`).
-/

open Filter Topology

namespace LatticeProb

/-- A contractive recursion `u (j+1) ≤ e j + θ u j` with `θ < 1`, `e j → 0` and `u` bounded
forces `u j ≤ ε` eventually, for every `ε > 0`. -/
theorem eventually_le_of_contraction_recursion {u e : ℕ → ℝ} {θ B : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hB : ∀ j, u j ≤ B) (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ j, u (j + 1) ≤ e j + θ * u j) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, u j ≤ ε := by
  have hδpos : 0 < ε * (1 - θ) / 2 := by
    have : 0 < 1 - θ := by linarith
    positivity
  obtain ⟨J1, hJ1⟩ := eventually_atTop.1 (he.eventually (gt_mem_nhds hδpos))
  have key : ∀ k : ℕ, u (J1 + k) - ε / 2 ≤ θ ^ k * B := by
    intro k
    induction k with
    | zero => simpa using (by linarith [hB J1] : u J1 - ε / 2 ≤ B)
    | succ k ih =>
      have h1 := hrec (J1 + k)
      have h2 := hJ1 (J1 + k) (by omega)
      have h4 := mul_le_mul_of_nonneg_left ih hθ0
      have h3 : θ ^ (k + 1) * B = θ * (θ ^ k * B) := by ring
      rw [show J1 + (k + 1) = J1 + k + 1 from rfl, h3]
      nlinarith
  have ht : Tendsto (fun k : ℕ => θ ^ k * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const B
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (half_pos hε)))
  rw [eventually_atTop]
  refine ⟨J1 + k0, fun j hj => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show J1 ≤ j by omega)
  have h5 := key k
  have h6 := hk0 k (by omega)
  linarith

/-- `exp(-a (j+1)²) ≥ 2 exp(-a j²)²` once `a j² ≥ log 2` and `j ≥ 5`. -/
private lemma sq_exp_le_half {a r : ℝ} (ha : 0 ≤ a) (hr : 5 ≤ r)
    (h : Real.log 2 ≤ a * r ^ 2 / 2) :
    Real.exp (-(a * r ^ 2)) ^ 2 ≤ Real.exp (-(a * (r + 1) ^ 2)) / 2 := by
  have h2 : (r + 1) ^ 2 ≤ 3 / 2 * r ^ 2 := by nlinarith
  have h3 : a * (r + 1) ^ 2 ≤ a * (3 / 2 * r ^ 2) := mul_le_mul_of_nonneg_left h2 ha
  have h4 : Real.exp (-(a * r ^ 2)) ^ 2 * 2 ≤ Real.exp (-(a * (r + 1) ^ 2)) := by
    have : Real.exp (-(a * r ^ 2)) ^ 2 * 2 = Real.exp (-(a * r ^ 2) + -(a * r ^ 2) + Real.log 2) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), sq]
    rw [this]
    apply Real.exp_le_exp.2
    nlinarith
  linarith

/-- If `u (j+1) ≤ E j + (u j)^N` with `N ≥ 2`, `0 ≤ u j ≤ ρ < 1` and `E j ≤ K exp(-c j²)`
(`K, c > 0`), then `u j ≤ 4 exp(-a j²)` for all `j`, for some `a > 0`. -/
theorem exists_superexp_decay_of_recursion {N : ℕ} (hN : 2 ≤ N) {ρ K c : ℝ} (hρ : ρ < 1)
    (hK : 0 < K) (hc : 0 < c) {u E : ℕ → ℝ} (hu0 : ∀ j, 0 ≤ u j) (hu1 : ∀ j, u j ≤ ρ)
    (hE : ∀ j, E j ≤ K * Real.exp (-(c * (j : ℝ) ^ 2)))
    (hrec : ∀ j, u (j + 1) ≤ E j + u j ^ N) :
    ∃ a : ℝ, 0 < a ∧ ∀ j : ℕ, u j ≤ 4 * Real.exp (-(a * (j : ℝ) ^ 2)) := by
  have hρ0 : 0 ≤ ρ := le_trans (hu0 0) (hu1 0)
  obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hm1 : m ≠ 0 := by omega
  -- Phase A: the contraction `u j ^ N ≤ ρ^m u j`
  have hθ1 : ρ ^ m < 1 := pow_lt_one₀ hρ0 hρ hm1
  have hpow : ∀ j, u j ^ N ≤ ρ ^ m * u j := by
    intro j
    rw [hm, pow_succ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hu0 j) (hu1 j) m) (hu0 j)
  have hexp : Tendsto (fun j : ℕ => K * Real.exp (-(c * (j : ℝ) ^ 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => c * (j : ℝ) ^ 2) atTop atTop :=
      (Tendsto.const_mul_atTop hc (tendsto_pow_atTop (two_ne_zero))).comp tendsto_natCast_atTop_atTop
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul K
  have hA := eventually_le_of_contraction_recursion (u := u)
    (e := fun j => K * Real.exp (-(c * (j : ℝ) ^ 2))) (pow_nonneg hρ0 m) hθ1 hu1 hexp
    (fun j => by linarith [hrec j, hE j, hpow j]) (ε := 1 / 4) (by norm_num)
  obtain ⟨J0, hJ0⟩ := eventually_atTop.1 hA
  -- choice of `J`
  obtain ⟨J1, hJ1⟩ := exists_nat_ge ((16 + 4 * K) / c)
  set J : ℕ := max J0 (max 5 J1) with hJdef
  have hJ0' : J0 ≤ J := le_max_left _ _
  have hJ5 : (5 : ℝ) ≤ (J : ℝ) := by
    have : 5 ≤ J := le_trans (le_max_left _ _) (le_max_right _ _)
    exact_mod_cast this
  have hJc : 16 + 4 * K ≤ c * (J : ℝ) := by
    have : J1 ≤ J := le_trans (le_max_right _ _) (le_max_right _ _)
    have h' : (J1 : ℝ) ≤ J := by exact_mod_cast this
    have := (div_le_iff₀ hc).1 (hJ1.trans h')
    linarith
  have hJpos : 0 < (J : ℝ) := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  set a : ℝ := 2 * Real.log 2 / (J : ℝ) ^ 2 with hadef
  have ha : 0 < a := by positivity
  have haJ : a * (J : ℝ) ^ 2 = 2 * Real.log 2 := by
    rw [hadef]; field_simp
  have hcJ : 16 + 4 * K ≤ c * (J : ℝ) ^ 2 := by nlinarith
  have hac : a ≤ c / 8 := by
    have : a * (J : ℝ) ^ 2 ≤ c / 8 * (J : ℝ) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  have hexp4 : Real.exp (-(a * (J : ℝ) ^ 2)) = 1 / 4 := by
    rw [haJ, Real.exp_neg, two_mul, Real.exp_add, Real.exp_log (by norm_num)]
    norm_num
  -- Phase B: closing induction
  have hB : ∀ j : ℕ, J ≤ j → u j ≤ Real.exp (-(a * (j : ℝ) ^ 2)) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      rw [hexp4]; exact hJ0 J hJ0'
    | succ j hj ih =>
      have hjr : (J : ℝ) ≤ j := by exact_mod_cast hj
      have hj5 : (5 : ℝ) ≤ j := le_trans hJ5 hjr
      have hj2 : (J : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 := by nlinarith
      have hx1 : Real.exp (-(a * (j : ℝ) ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith)
      have hxN : u j ^ N ≤ Real.exp (-(a * (j : ℝ) ^ 2)) ^ 2 :=
        (pow_le_pow_left₀ (hu0 j) ih N).trans (pow_le_pow_of_le_one (Real.exp_pos _).le hx1 hN)
      have hA : Real.exp (-(a * (j : ℝ) ^ 2)) ^ 2 ≤
          Real.exp (-(a * ((j : ℝ) + 1) ^ 2)) / 2 := by
        apply sq_exp_le_half ha.le hj5
        nlinarith
      have hKb : K * Real.exp (-(c * (j : ℝ) ^ 2)) ≤ Real.exp (-(a * ((j : ℝ) + 1) ^ 2)) / 2 := by
        have h2 : ((j : ℝ) + 1) ^ 2 ≤ 3 / 2 * (j : ℝ) ^ 2 := by nlinarith
        have h3 : a * ((j : ℝ) + 1) ^ 2 ≤ a * (3 / 2 * (j : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 ha.le
        have h5 : a * (3 / 2 * (j : ℝ) ^ 2) ≤ c / 8 * (3 / 2 * (j : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hac (by positivity)
        have hcj : 16 + 4 * K ≤ c * (j : ℝ) ^ 2 := by nlinarith
        have h6 : c * (j : ℝ) ^ 2 / 2 ≤ c * (j : ℝ) ^ 2 - a * ((j : ℝ) + 1) ^ 2 := by nlinarith
        have h7 : Real.exp (-(a * ((j : ℝ) + 1) ^ 2)) =
            Real.exp (-(c * (j : ℝ) ^ 2)) *
              Real.exp (c * (j : ℝ) ^ 2 - a * ((j : ℝ) + 1) ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
        have h8 := Real.add_one_le_exp (c * (j : ℝ) ^ 2 - a * ((j : ℝ) + 1) ^ 2)
        have h9 : 2 * K ≤ Real.exp (c * (j : ℝ) ^ 2 - a * ((j : ℝ) + 1) ^ 2) := by linarith
        have h10 := mul_le_mul_of_nonneg_left h9 (Real.exp_pos (-(c * (j : ℝ) ^ 2))).le
        rw [h7]
        linarith
      have := hrec j
      have hE' := hE j
      push_cast
      linarith
  refine ⟨a, ha, fun j => ?_⟩
  by_cases hj : J ≤ j
  · calc u j ≤ Real.exp (-(a * (j : ℝ) ^ 2)) := hB j hj
      _ ≤ 4 * Real.exp (-(a * (j : ℝ) ^ 2)) := by
        have := (Real.exp_pos (-(a * (j : ℝ) ^ 2))).le
        linarith
  · have hj' : (j : ℝ) ≤ J := by exact_mod_cast (not_le.1 hj).le
    have hj2 : (j : ℝ) ^ 2 ≤ (J : ℝ) ^ 2 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    have h1 : Real.exp (-(a * (J : ℝ) ^ 2)) ≤ Real.exp (-(a * (j : ℝ) ^ 2)) :=
      Real.exp_le_exp.2 (by nlinarith)
    rw [hexp4] at h1
    linarith [hu1 j]

end LatticeProb
