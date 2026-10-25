module

public import Mathlib

@[expose] public section

/-!
# Power-sum and tail estimates

Comparison of the partial sums `∑_{n=1}^N n^β` with integrals (for `β > -1`), the bound for
`β < -1` through the full series, the harmonic bound for `β = -1`, and the telescoped tail
bound `∑_{n ∈ S} n^(-m-1) ≤ (N-1)^(-m) / m` for finite sets `S` of integers at least `N ≥ 2`.
These one-dimensional facts are used after lattice points are grouped by the integer part of
their radius.
-/

noncomputable section

open scoped BigOperators

namespace LatticeProb.Euclidean.Series

/-- Partial sums of `n^β` for `β > -1`, with `β + 1 ≤ 1`: the integral comparison
`∑_{n=1}^N n^β ≤ N^{β+1}/(β+1)`, by induction through the concavity inequality
`γ n^{γ-1} ≤ n^γ - (n-1)^γ` (`γ = β+1 ∈ (0,1]`, `n ≥ 1`). -/
lemma rpow_sub_ge_of_unit {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {n : ℝ} (hn : 1 ≤ n) :
    γ * n ^ (γ - 1) ≤ n ^ γ - (n - 1) ^ γ := by
  rcases eq_or_lt_of_le hn with h1 | h1
  · subst h1
    have h0 : ((1 : ℝ) - 1) ^ γ = 0 := by
      rw [sub_self, Real.zero_rpow hγ0.ne']
    rw [h0, Real.one_rpow, Real.one_rpow]
    linarith
  · have hnpos : (0 : ℝ) < n := by linarith
    have hne : n ≠ 0 := ne_of_gt hnpos
    have hinv : 1 / n ≤ 1 := by rw [div_le_one hnpos]; exact hn
    have hs : -1 ≤ -(1 / n) := by linarith
    have hnn : 0 ≤ 1 + -(1 / n) := by linarith
    have hb := rpow_one_add_le_one_add_mul_self hs hγ0.le hγ1
    have hprod : n * (1 + -(1 / n)) = n - 1 := by
      rw [mul_add, mul_one, mul_neg, mul_one_div_cancel hne]
      ring
    have hfac : (n - 1) ^ γ = n ^ γ * (1 + -(1 / n)) ^ γ := by
      rw [← Real.mul_rpow hnpos.le hnn, hprod]
    have hsub : n ^ (γ - 1) = n ^ γ / n := by
      rw [Real.rpow_sub_one hne]
    rw [hfac, hsub]
    have hpow : 0 ≤ n ^ γ := Real.rpow_nonneg hnpos.le _
    have key : n ^ γ * (1 + -(1 / n)) ^ γ ≤ n ^ γ * (1 + γ * -(1 / n)) :=
      mul_le_mul_of_nonneg_left hb hpow
    have hexp : n ^ γ * (1 + γ * -(1 / n)) = n ^ γ - γ * (n ^ γ / n) := by
      ring
    linarith

/-- For `β ∈ (-1, 0]`, the partial sums satisfy `∑_{n=1}^N n^β ≤ N^(β+1)/(β+1)`. -/
lemma sum_rpow_Icc_le_of_gt_neg_one {β : ℝ} (hβ : -1 < β) (hβ0 : β ≤ 0) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ β ≤ (N : ℝ) ^ (β + 1) / (β + 1) := by
  have hγ0 : 0 < β + 1 := by linarith
  have hγ1 : β + 1 ≤ 1 := by linarith
  induction N with
  | zero =>
      simp [Real.zero_rpow hγ0.ne']
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      have hn : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ N + 1)
      have hk := rpow_sub_ge_of_unit hγ0 hγ1 hn
      have hcast : ((N + 1 : ℕ) : ℝ) - 1 = (N : ℝ) := by push_cast; ring
      rw [hcast] at hk
      have hbeta : ((N + 1 : ℕ) : ℝ) ^ (β + 1 - 1) = ((N + 1 : ℕ) : ℝ) ^ β := by
        rw [add_sub_cancel_right]
      rw [hbeta] at hk
      have hdiv : ((N + 1 : ℕ) : ℝ) ^ β ≤
          (((N + 1 : ℕ) : ℝ) ^ (β + 1) - (N : ℝ) ^ (β + 1)) / (β + 1) := by
        rw [le_div_iff₀ hγ0]
        linarith
      have hstep : (N : ℝ) ^ (β + 1) / (β + 1) + ((N + 1 : ℕ) : ℝ) ^ β
          ≤ ((N + 1 : ℕ) : ℝ) ^ (β + 1) / (β + 1) := by
        have : (N : ℝ) ^ (β + 1) / (β + 1) +
            (((N + 1 : ℕ) : ℝ) ^ (β + 1) - (N : ℝ) ^ (β + 1)) / (β + 1)
            = ((N + 1 : ℕ) : ℝ) ^ (β + 1) / (β + 1) := by ring
        linarith
      linarith

/-- The exponent-`(−1)` case: `∑_{n=1}^N n^{-1} ≤ 1 + log N`. -/
lemma sum_inv_Icc_le_one_add_log (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-1 : ℝ) ≤ 1 + Real.log N := by
  have h : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-1 : ℝ) = ((harmonic N : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    rw [Real.rpow_neg_one]
  rw [h]
  exact harmonic_le_one_add_log N

/-- The exponent `β < -1` case: the partial sums are bounded by the full series. -/
lemma sum_rpow_Icc_le_tsum {β : ℝ} (hβ : β < -1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ β ≤ ∑' n : ℕ, (n : ℝ) ^ β := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ β) := Real.summable_nat_rpow.mpr hβ
  have hsub : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ β ≤ ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ β := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    · intro n _ _
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  exact hsub.trans (Summable.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) hs)

/-- For `p > 0`, `1 - p ≤ p⁻¹ - 1`: the difference `p⁻¹ - 1 - (1 - p)` equals `(1 - p)² p⁻¹ ≥ 0`. -/
private lemma one_sub_le_inv_sub_one {p : ℝ} (hp : 0 < p) : 1 - p ≤ p⁻¹ - 1 := by
  have hpinv : p * p⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  have hid : p⁻¹ - 1 - (1 - p) = (1 - p) ^ 2 * p⁻¹ := by
    linear_combination (2 - p) * hpinv
  have hnn : 0 ≤ (1 - p) ^ 2 * p⁻¹ := mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hp.le)
  calc 1 - p ≤ 1 - p + (1 - p) ^ 2 * p⁻¹ := le_add_of_nonneg_right hnn
    _ = p⁻¹ - 1 := by rw [← hid]; ring

/-- For `0 ≤ x` and `q ≤ 1 - x`, `(1 + x) q ≤ 1`, since `(1 + x)(1 - x) = 1 - x ^ 2`. -/
private lemma one_add_mul_le_one_of_le_sub {x q : ℝ} (hx : 0 ≤ x) (hq : q ≤ 1 - x) :
    (1 + x) * q ≤ 1 := by
  calc (1 + x) * q ≤ (1 + x) * (1 - x) := mul_le_mul_of_nonneg_left hq (by linarith)
    _ = 1 - x ^ 2 := by ring
    _ ≤ 1 := sub_le_self 1 (sq_nonneg x)

/-- Bernoulli inequality for negative powers: `1 + m(1-p) ≤ p^{-m}` for `p ∈ (0,1]`, `m > 0`. -/
lemma one_add_mul_le_rpow_neg {p m : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hm : 0 < m) :
    1 + m * (1 - p) ≤ p ^ (-m) := by
  rw [Real.rpow_neg hp0.le]
  have hpm : 0 < p ^ m := Real.rpow_pos_of_pos hp0 m
  have hx : 0 ≤ m * (1 - p) := mul_nonneg hm.le (by linarith)
  rcases le_total 1 m with hm1 | hm1
  · -- `m ≥ 1`: Bernoulli for `u = p⁻¹ ≥ 1`, where `(p^m)⁻¹ = u^m`.
    have hv : 0 < p⁻¹ := inv_pos.mpr hp0
    have hinv1 : 1 - p ≤ p⁻¹ - 1 := one_sub_le_inv_sub_one hp0
    have hbern := one_add_mul_self_le_rpow_one_add (s := p⁻¹ - 1) (by linarith) hm1
    rw [add_sub_cancel] at hbern
    have h2 : m * (1 - p) ≤ m * (p⁻¹ - 1) := mul_le_mul_of_nonneg_left hinv1 hm.le
    rw [← Real.inv_rpow hp0.le]
    linarith
  · -- `0 < m ≤ 1`: Bernoulli in the exponent `m ∈ [0,1]` for `p ≤ 1`.
    have hb := rpow_one_add_le_one_add_mul_self (s := p - 1) (by linarith) hm.le hm1
    rw [add_sub_cancel] at hb
    have hb' : p ^ m ≤ 1 - m * (1 - p) := by linarith
    have key : (1 + m * (1 - p)) * p ^ m ≤ 1 := one_add_mul_le_one_of_le_sub hx hb'
    calc 1 + m * (1 - p) = (1 + m * (1 - p)) * p ^ m * (p ^ m)⁻¹ :=
          (mul_inv_cancel_right₀ hpm.ne' _).symm
      _ ≤ 1 * (p ^ m)⁻¹ := mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hpm.le)
      _ = (p ^ m)⁻¹ := one_mul _

/-- Per-term tail inequality: for `n ≥ 2` and `m > 0`, `m n^{-m-1} ≤ (n-1)^{-m} - n^{-m}`. -/
lemma tail_term_le {m : ℝ} (hm : 0 < m) {n : ℝ} (hn : 2 ≤ n) :
    m * n ^ (-m - 1) ≤ (n - 1) ^ (-m) - n ^ (-m) := by
  have hnpos : 0 < n := by linarith
  have hp0 : 0 < (n - 1) / n := div_pos (by linarith) hnpos
  have hp1 : (n - 1) / n ≤ 1 := by
    rw [div_le_one hnpos]
    linarith
  have hnp : n * ((n - 1) / n) = n - 1 := by
    field_simp
  have h1p : 1 - (n - 1) / n = 1 / n := by
    rw [sub_div, div_self hnpos.ne']
    ring
  have hbern := one_add_mul_le_rpow_neg hp0 hp1 hm
  rw [h1p] at hbern
  have hsplit : (n - 1) ^ (-m) = n ^ (-m) * ((n - 1) / n) ^ (-m) := by
    calc (n - 1) ^ (-m) = (n * ((n - 1) / n)) ^ (-m) := by rw [hnp]
      _ = n ^ (-m) * ((n - 1) / n) ^ (-m) := Real.mul_rpow hnpos.le hp0.le
  have hA : 0 ≤ n ^ (-m) := Real.rpow_nonneg hnpos.le _
  have hn1 : n ^ (-m - 1) = n ^ (-m) / n := Real.rpow_sub_one hnpos.ne' (-m)
  rw [hsplit, hn1]
  have h3 : n ^ (-m) * (m * (1 / n)) ≤ n ^ (-m) * (((n - 1) / n) ^ (-m) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  calc m * (n ^ (-m) / n) = n ^ (-m) * (m * (1 / n)) := by ring
    _ ≤ n ^ (-m) * (((n - 1) / n) ^ (-m) - 1) := h3
    _ = n ^ (-m) * ((n - 1) / n) ^ (-m) - n ^ (-m) := by ring

/-- Telescoped partial tail sums: for `2 ≤ N ≤ M`,
`∑_{n=N}^M n^{-m-1} ≤ ((N-1)^{-m} - M^{-m})/m`. -/
lemma tail_partial_le {m : ℝ} (hm : 0 < m) {N : ℕ} (hN : 2 ≤ N) (M : ℕ) (hNM : N ≤ M) :
    ∑ n ∈ Finset.Icc N M, (n : ℝ) ^ (-m - 1)
      ≤ ((N : ℝ) - 1) ^ (-m) / m - (M : ℝ) ^ (-m) / m := by
  induction M, hNM using Nat.le_induction with
  | base =>
      rw [Finset.Icc_self, Finset.sum_singleton]
      have h := tail_term_le hm (n := (N : ℝ)) (by exact_mod_cast hN)
      have h2 : (N : ℝ) ^ (-m - 1) * m ≤ ((N : ℝ) - 1) ^ (-m) - (N : ℝ) ^ (-m) := by
        linarith [h]
      have h3 := (le_div_iff₀ hm).mpr h2
      rw [sub_div] at h3
      exact h3
  | succ M hM ih =>
      rw [Finset.sum_Icc_succ_top (by omega : N ≤ M + 1)]
      have hM2 : (2 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 ≤ M + 1)
      have h := tail_term_le hm hM2
      have hcast : ((M + 1 : ℕ) : ℝ) - 1 = (M : ℝ) := by push_cast; ring
      rw [hcast] at h
      have h2 : ((M + 1 : ℕ) : ℝ) ^ (-m - 1) * m
          ≤ (M : ℝ) ^ (-m) - ((M + 1 : ℕ) : ℝ) ^ (-m) := by
        linarith [h]
      have h3 := (le_div_iff₀ hm).mpr h2
      rw [sub_div] at h3
      linarith [ih, h3]

/-- Tail sums over any finite set of integers `≥ N` (with `N ≥ 2`). -/
lemma tail_finset_le {m : ℝ} (hm : 0 < m) {N : ℕ} (hN : 2 ≤ N) (S : Finset ℕ)
    (hS : ∀ n ∈ S, N ≤ n) :
    ∑ n ∈ S, (n : ℝ) ^ (-m - 1) ≤ ((N : ℝ) - 1) ^ (-m) / m := by
  classical
  set M : ℕ := max N (S.sup id) with hM
  have hsub : S ⊆ Finset.Icc N M := by
    intro n hn
    rw [Finset.mem_Icc]
    refine ⟨hS n hn, ?_⟩
    have h1 : n ≤ S.sup id := Finset.le_sup (f := id) hn
    exact le_max_of_le_right h1
  have hnn : ∀ n ∈ Finset.Icc N M, (0 : ℝ) ≤ (n : ℝ) ^ (-m - 1) :=
    fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpart := tail_partial_le hm hN M (le_max_left _ _)
  have hMnn : 0 ≤ (M : ℝ) ^ (-m) / m := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg M) _) hm.le
  calc ∑ n ∈ S, (n : ℝ) ^ (-m - 1) ≤ ∑ n ∈ Finset.Icc N M, (n : ℝ) ^ (-m - 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hnn n hn)
    _ ≤ ((N : ℝ) - 1) ^ (-m) / m := by linarith [hpart, hMnn]

/-- Tail sums over any finite set of positive integers: the threshold `N = 1` costs at most
`1 + 1/m`. -/
lemma tail_finset_le_one {m : ℝ} (hm : 0 < m) (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) :
    ∑ n ∈ S, (n : ℝ) ^ (-m - 1) ≤ 1 + 1 / m := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun n => 2 ≤ n)
      (fun n : ℕ => (n : ℝ) ^ (-m - 1))
  have hA : ∑ n ∈ S.filter (fun n => 2 ≤ n), (n : ℝ) ^ (-m - 1) ≤ 1 / m := by
    have h := tail_finset_le hm (N := 2) le_rfl (S.filter (fun n => 2 ≤ n))
      (fun n hn => (Finset.mem_filter.mp hn).2)
    have h1 : (((2 : ℕ) : ℝ) - 1) ^ (-m) / m = 1 / m := by
      norm_num
    rw [h1] at h
    exact h
  have hB : ∑ n ∈ S.filter (fun n => ¬ 2 ≤ n), (n : ℝ) ^ (-m - 1) ≤ 1 := by
    have hsub : S.filter (fun n => ¬ 2 ≤ n) ⊆ {1} := by
      intro n hn
      obtain ⟨hnS, hn2⟩ := Finset.mem_filter.mp hn
      have h1 := hS n hnS
      rw [Finset.mem_singleton]
      omega
    have h : ∑ n ∈ S.filter (fun n => ¬ 2 ≤ n), (n : ℝ) ^ (-m - 1)
        ≤ ∑ n ∈ ({1} : Finset ℕ), (n : ℝ) ^ (-m - 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have h1 : ∑ n ∈ ({1} : Finset ℕ), (n : ℝ) ^ (-m - 1) = 1 := by
      simp
    linarith [h, h1]
  rw [← hsplit]
  linarith [hA, hB]

/-- If `s ≤ t`, `0 ≤ t` and `1 ≤ X`, then `s ≤ t * X`. -/
private lemma le_mul_of_le_of_one_le_factor {s t X : ℝ} (hs : s ≤ t) (ht : 0 ≤ t)
    (hX : 1 ≤ X) : s ≤ t * X :=
  hs.trans (le_mul_of_one_le_right ht hX)

/-- For `X ≥ 0`, `X / m ≤ (1 + 1/m) * X`, because `(1 + 1/m) * X - X / m = X`. -/
private lemma div_le_one_add_inv_mul {X m : ℝ} (hX : 0 ≤ X) : X / m ≤ (1 + 1 / m) * X := by
  calc X / m = X * (1 / m) := div_eq_mul_one_div X m
    _ ≤ X + X * (1 / m) := le_add_of_nonneg_left hX
    _ = (1 + 1 / m) * X := by ring

/-- Finite-set tail bound: if every `n ∈ S` satisfies `⌊R⌋₊ ≤ n` with `R ≥ 1`, then
`∑_{n∈S} n^(-m-1) ≤ (1 + 1/m) · (4^m · R^(-m))`. -/
lemma tail_finset_bound {m R : ℝ} (hm : 0 < m) (hR : 1 ≤ R) (S : Finset ℕ)
    (hS : ∀ n ∈ S, Nat.floor R ≤ n) :
    ∑ n ∈ S, (n : ℝ) ^ (-m - 1) ≤ (1 + 1 / m) * ((4 : ℝ) ^ m * R ^ (-m)) := by
  have hR0 : 0 < R := by linarith
  have hN1 : 1 ≤ Nat.floor R := (Nat.one_le_floor_iff R).mpr hR
  have hpow_nonneg : 0 ≤ (4 : ℝ) ^ m * R ^ (-m) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hR0.le _)
  have hS1 : ∀ n ∈ S, 1 ≤ n := fun n hn => le_trans hN1 (hS n hn)
  have hinvm : 0 ≤ 1 / m := (one_div_pos.mpr hm).le
  have hR4 : (1 : ℝ) + 1 / m ≥ 0 := by linarith
  rcases Nat.lt_or_ge (Nat.floor R) 2 with hlt | hge
  · -- `⌊R⌋ = 1`, so `R < 2`; the bound `1 + 1/m` is absorbed since `4^m R^{-m} ≥ 1`.
    have hfl1 : Nat.floor R = 1 := by omega
    have hRlt : R < 2 := by
      have h := Nat.lt_floor_add_one R
      rw [hfl1] at h
      push_cast at h
      linarith
    have hge1 : (1 : ℝ) ≤ (4 : ℝ) ^ m * R ^ (-m) := by
      have hq : (1 : ℝ) ≤ (4 / R) ^ m := by
        apply Real.one_le_rpow _ hm.le
        rw [le_div_iff₀ hR0]
        linarith
      rw [Real.div_rpow (by norm_num) hR0.le] at hq
      rw [Real.rpow_neg hR0.le, ← div_eq_mul_inv]
      exact hq
    have h := tail_finset_le_one hm S hS1
    exact le_mul_of_le_of_one_le_factor h hR4 hge1
  · -- `⌊R⌋ ≥ 2`: then `⌊R⌋ - 1 ≥ R/4`, and the telescoped bound applies.
    have hT := tail_finset_le hm hge S hS
    have hNR : R < (Nat.floor R : ℝ) + 1 := Nat.lt_floor_add_one R
    have hN2 : (2 : ℝ) ≤ (Nat.floor R : ℝ) := by exact_mod_cast hge
    have hquarter : R / 4 ≤ (Nat.floor R : ℝ) - 1 := by
      rcases le_total R 4 with hR4' | hR4'
      · linarith
      · linarith
    have hpow : ((Nat.floor R : ℝ) - 1) ^ (-m) ≤ (R / 4) ^ (-m) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hquarter (by linarith)
    have hdiv : (R / 4) ^ (-m) = (4 : ℝ) ^ m * R ^ (-m) := by
      rw [Real.div_rpow hR0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
        div_inv_eq_mul, mul_comm]
    have hfin : ((Nat.floor R : ℝ) - 1) ^ (-m) / m ≤ (1 + 1 / m) * ((4 : ℝ) ^ m * R ^ (-m)) := by
      have h1 : ((Nat.floor R : ℝ) - 1) ^ (-m) / m ≤ ((4 : ℝ) ^ m * R ^ (-m)) / m := by
        rw [div_le_div_iff_of_pos_right hm]
        linarith [hpow, hdiv]
      have h2 : ((4 : ℝ) ^ m * R ^ (-m)) / m ≤ (1 + 1 / m) * ((4 : ℝ) ^ m * R ^ (-m)) :=
        div_le_one_add_inv_mul hpow_nonneg
      linarith [h1, h2]
    linarith [hT, hfin]

/-- **Unified partial-sum bound.** For `β > -1`, `∑_{n=1}^N n^β ≤ (1 + 1/(β+1)) N^{β+1}`. -/
lemma sum_rpow_Icc_le_unified {β : ℝ} (hβ : -1 < β) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ β ≤ (1 + 1 / (β + 1)) * (N : ℝ) ^ (β + 1) := by
  have hγ : 0 < β + 1 := by linarith
  have hN0 : 0 ≤ (N : ℝ) ^ (β + 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hinv : 0 ≤ 1 / (β + 1) := div_nonneg zero_le_one hγ.le
  rcases le_total β 0 with hβ0 | hβ0
  · have h := sum_rpow_Icc_le_of_gt_neg_one hβ hβ0 N
    have h2 : (N : ℝ) ^ (β + 1) / (β + 1) = (1 / (β + 1)) * (N : ℝ) ^ (β + 1) := by ring
    have h3 : (1 + 1 / (β + 1)) * (N : ℝ) ^ (β + 1)
        = (N : ℝ) ^ (β + 1) + (1 / (β + 1)) * (N : ℝ) ^ (β + 1) := by ring
    linarith
  · have h4 : 0 ≤ (1 / (β + 1)) * (N : ℝ) ^ (β + 1) := mul_nonneg hinv hN0
    have h3 : (1 + 1 / (β + 1)) * (N : ℝ) ^ (β + 1)
        = (N : ℝ) ^ (β + 1) + (1 / (β + 1)) * (N : ℝ) ^ (β + 1) := by ring
    have hs : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ β ≤ (N : ℝ) ^ (β + 1) := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        simp [Real.zero_rpow hγ.ne']
      · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        have hterm : ∀ n ∈ Finset.Icc 1 N, (n : ℝ) ^ β ≤ (N : ℝ) ^ β := by
          intro n hn
          rw [Finset.mem_Icc] at hn
          exact Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn.2) hβ0
        calc ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ β ≤ ∑ _n ∈ Finset.Icc 1 N, (N : ℝ) ^ β :=
              Finset.sum_le_sum hterm
          _ = (N : ℝ) * (N : ℝ) ^ β := by
              rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
          _ = (N : ℝ) ^ (β + 1) := by
              rw [Real.rpow_add_one hNpos.ne']
              ring
    linarith

end LatticeProb.Euclidean.Series
