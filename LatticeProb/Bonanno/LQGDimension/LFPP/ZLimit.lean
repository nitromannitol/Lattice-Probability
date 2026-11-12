/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.ZLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan

/-!
# Node `ZL`: the `(4.8)`–`(4.9)` limit (pure real analysis)

Proves `Blueprint.Draft.ZLimitBound`.
-/

noncomputable section

open Filter Topology Set Real

namespace LQGDimension

namespace ZLimitAux

/-! ## Elementary exponential domination -/

/-- `y ^ D ≤ exp (D * (y - 1))` for `D ≥ 0`, `y > 0`: from `log y ≤ y - 1`. -/
lemma rpow_le_exp_sub (D : ℝ) (hD : 0 ≤ D) (y : ℝ) (hy : 0 < y) :
    y ^ D ≤ Real.exp (D * (y - 1)) := by
  have h1 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy
  have h2 : D * Real.log y ≤ D * (y - 1) := mul_le_mul_of_nonneg_left h1 hD
  have h3 : Real.log (y ^ D) = D * Real.log y := Real.log_rpow hy D
  calc y ^ D = Real.exp (Real.log (y ^ D)) := (Real.exp_log (Real.rpow_pos_of_pos hy D)).symm
    _ = Real.exp (D * Real.log y) := by rw [h3]
    _ ≤ Real.exp (D * (y - 1)) := Real.exp_le_exp.mpr h2

/-- `w ^ D ≤ D ^ D * exp (w - D)` for `D ≥ 0`, `w > 0`. -/
lemma rpow_le_pow_mul_exp (D w : ℝ) (hD : 0 ≤ D) (hw : 0 < w) :
    w ^ D ≤ D ^ D * Real.exp (w - D) := by
  rcases hD.eq_or_lt with hD0 | hD0
  · rw [← hD0]
    simp only [Real.rpow_zero, sub_zero, one_mul]
    exact Real.one_le_exp hw.le
  · have hD0' : D ≠ 0 := hD0.ne'
    set u := w / D with hu_def
    have hu : 0 < u := div_pos hw hD0
    have hwu : w = D * u := by
      rw [hu_def]
      field_simp
    have hstep : u ^ D ≤ Real.exp (D * (u - 1)) := rpow_le_exp_sub D hD u hu
    have heq : D * (u - 1) = w - D := by rw [hwu]; ring
    rw [heq] at hstep
    calc w ^ D = (D * u) ^ D := by rw [hwu]
      _ = D ^ D * u ^ D := Real.mul_rpow hD hu.le
      _ ≤ D ^ D * Real.exp (w - D) :=
          mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hD D)

/-- `x ^ D * exp (-(c * x)) ≤ (D / c) ^ D * exp (-D)` for `D ≥ 0`, `c > 0`, `x > 0`. -/
lemma poly_le_const_mul_exp (D c x : ℝ) (hD : 0 ≤ D) (hc : 0 < c) (hx : 0 < x) :
    x ^ D * Real.exp (-(c * x)) ≤ (D / c) ^ D * Real.exp (-D) := by
  have hw : 0 < c * x := mul_pos hc hx
  have hmain : (c * x) ^ D ≤ D ^ D * Real.exp (c * x - D) := rpow_le_pow_mul_exp D (c * x) hD hw
  rw [Real.mul_rpow hc.le hx.le] at hmain
  have hcD : 0 < c ^ D := Real.rpow_pos_of_pos hc D
  have hx' : x ^ D ≤ (D ^ D / c ^ D) * Real.exp (c * x - D) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcD]
    calc x ^ D * c ^ D = c ^ D * x ^ D := by ring
      _ ≤ D ^ D * Real.exp (c * x - D) := hmain
  rw [← Real.div_rpow hD hc.le] at hx'
  calc x ^ D * Real.exp (-(c * x)) ≤
        (D / c) ^ D * Real.exp (c * x - D) * Real.exp (-(c * x)) :=
        mul_le_mul_of_nonneg_right hx' (Real.exp_nonneg _)
    _ = (D / c) ^ D * Real.exp (-D) := by
        rw [mul_assoc, ← Real.exp_add, show c * x - D + -(c * x) = -D by ring]

/-- `log (x ^ D) = D * log x` for `x ≥ 0` (any real `D`), including the junk case `x = 0`. -/
lemma log_rpow_nonneg (x D : ℝ) (hx : 0 ≤ x) : Real.log (x ^ D) = D * Real.log x := by
  rcases hx.eq_or_lt with hx0 | hx0
  · rw [← hx0]
    rcases eq_or_ne D 0 with hD0 | hD0
    · simp [hD0]
    · rw [Real.zero_rpow hD0, Real.log_zero, mul_zero]
  · exact Real.log_rpow hx0 D

/-! ## Tail bound for a polynomial times a decaying exponential -/

/-- `Σ_k (k+1)^D exp(-c k)` is summable and bounded, for `D ≥ 0`, `c > 0`. -/
lemma tail_geom_bound (D c : ℝ) (hD : 0 ≤ D) (hc : 0 < c) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ D * Real.exp (-(c * k))) ∧
    ∑' k : ℕ, ((k : ℝ) + 1) ^ D * Real.exp (-(c * k)) ≤
      (2 * D / c) ^ D * Real.exp (-D) * Real.exp (c / 2) * (1 - Real.exp (-(c / 2)))⁻¹ := by
  set r : ℝ := Real.exp (-(c / 2)) with hr_def
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by
    rw [hr_def]
    have hneg : -(c / 2) < 0 := by linarith
    calc Real.exp (-(c / 2)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
      _ = 1 := Real.exp_zero
  set K : ℝ := (2 * D / c) ^ D * Real.exp (-D) * Real.exp (c / 2) with hK_def
  have hgsum : Summable (fun k : ℕ => K * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hrk : ∀ k : ℕ, r ^ k = Real.exp (-(c / 2) * (k : ℝ)) := by
    intro k
    rw [hr_def, ← Real.exp_nat_mul, mul_comm]
  have hbound : ∀ k : ℕ, ((k : ℝ) + 1) ^ D * Real.exp (-(c * k)) ≤ K * r ^ k := by
    intro k
    have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hc2 : (0 : ℝ) < c / 2 := by linarith
    have hstep := poly_le_const_mul_exp D (c / 2) ((k : ℝ) + 1) hD hc2 hx
    have hrw : D / (c / 2) = 2 * D / c := by field_simp
    rw [hrw] at hstep
    have hexp_eq : Real.exp (-(c * (k : ℝ))) =
        Real.exp (-(c / 2 * ((k : ℝ) + 1))) * Real.exp (c / 2) * Real.exp (-(c / 2) * (k : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add,
        show -(c / 2 * ((k : ℝ) + 1)) + c / 2 + -(c / 2) * (k : ℝ) = -(c * (k : ℝ)) by ring]
    rw [hexp_eq, hrk]
    calc ((k : ℝ) + 1) ^ D *
          (Real.exp (-(c / 2 * ((k : ℝ) + 1))) * Real.exp (c / 2) * Real.exp (-(c / 2) * (k : ℝ))) =
        (((k : ℝ) + 1) ^ D * Real.exp (-(c / 2 * ((k : ℝ) + 1)))) *
          (Real.exp (c / 2) * Real.exp (-(c / 2) * (k : ℝ))) := by ring
      _ ≤ ((2 * D / c) ^ D * Real.exp (-D)) * (Real.exp (c / 2) * Real.exp (-(c / 2) * (k : ℝ))) := by
          apply mul_le_mul_of_nonneg_right hstep
          positivity
      _ = K * Real.exp (-(c / 2) * (k : ℝ)) := by rw [hK_def]; ring
  have hsum : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ D * Real.exp (-(c * k))) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hbound hgsum
  refine ⟨hsum, ?_⟩
  calc ∑' k : ℕ, ((k : ℝ) + 1) ^ D * Real.exp (-(c * k)) ≤ ∑' k : ℕ, K * r ^ k :=
        hsum.tsum_le_tsum hbound hgsum
    _ = K * ∑' k : ℕ, r ^ k := tsum_mul_left
    _ = K * (1 - r)⁻¹ := by rw [tsum_geometric_of_lt_one hr0 hr1]
    _ = (2 * D / c) ^ D * Real.exp (-D) * Real.exp (c / 2) * (1 - Real.exp (-(c / 2)))⁻¹ := by
        rw [hK_def, hr_def]

/-! ## Splitting a nonnegative series at a finite cutoff -/

/-- If `f ≥ 0` is dominated by a summable `g ≥ 0` from index `N` on, `f` is summable and its
sum is at most the head (`range N`) plus the tail bound `∑' g`. -/
lemma tsum_le_sum_add_tsum {f g : ℕ → ℝ} (N : ℕ) (hf0 : ∀ k, 0 ≤ f k)
    (hg0 : ∀ k, 0 ≤ g k) (hgsum : Summable g) (htail : ∀ k, N ≤ k → f k ≤ g k) :
    Summable f ∧ ∑' k, f k ≤ ∑ k ∈ Finset.range N, f k + ∑' k, g k := by
  classical
  set aux : ℕ → ℝ := fun k => if k < N then f k else 0 with haux_def
  have haux_sum : Summable aux := summable_of_ne_finset_zero (s := Finset.range N)
    (fun b hb => by
      simp only [Finset.mem_range, not_lt] at hb
      simp only [haux_def, if_neg (not_lt.mpr hb)])
  have hle : ∀ k, f k ≤ aux k + g k := by
    intro k
    by_cases hk : k < N
    · simp only [haux_def, if_pos hk]
      linarith only [hg0 k]
    · simp only [haux_def, if_neg hk, zero_add]
      exact htail k (not_lt.mp hk)
  have hsum : Summable f := Summable.of_nonneg_of_le hf0 hle (haux_sum.add hgsum)
  refine ⟨hsum, ?_⟩
  have haux_eq : ∑' k, aux k = ∑ k ∈ Finset.range N, f k := by
    have hHS : HasSum aux (∑ k ∈ Finset.range N, aux k) := hasSum_sum_of_ne_finset_zero
      (s := Finset.range N) (fun b hb => by
        simp only [Finset.mem_range, not_lt] at hb
        simp only [haux_def, if_neg (not_lt.mpr hb)])
    rw [hHS.tsum_eq]
    exact Finset.sum_congr rfl (fun k hk => by simp only [haux_def, if_pos (Finset.mem_range.mp hk)])
  calc ∑' k, f k ≤ ∑' k, (aux k + g k) := hsum.tsum_le_tsum hle (haux_sum.add hgsum)
    _ = ∑' k, aux k + ∑' k, g k := (haux_sum.hasSum.add hgsum.hasSum).tsum_eq
    _ = ∑ k ∈ Finset.range N, f k + ∑' k, g k := by rw [haux_eq]

/-! ## Threshold bounds: a `k^{1/4}` (resp. `√k`) term is beaten by `k/4` past a threshold -/

/-- For `C ≥ 0`, `n ≥ 1`, `k ≥ 1` and `k ≥ (4·2^{1/4}·C)^{4/3} · n`, `C n^{3/4} (k+1)^{1/4} ≤ k/4`. -/
lemma quarter_pow_le (C : ℝ) (hC : 0 ≤ C) (n k : ℝ) (hn : 1 ≤ n) (hk1 : 1 ≤ k)
    (hk : (4 * (2 : ℝ) ^ (1 / 4 : ℝ) * C) ^ (4 / 3 : ℝ) * n ≤ k) :
    C * n ^ (3 / 4 : ℝ) * (k + 1) ^ (1 / 4 : ℝ) ≤ k / 4 := by
  have hkpos : (0 : ℝ) < k := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  set base : ℝ := 4 * (2 : ℝ) ^ (1 / 4 : ℝ) * C with hbase_def
  have hbase_nonneg : 0 ≤ base := by positivity
  have hexp1 : (4 / 3 : ℝ) * (3 / 4 : ℝ) = 1 := by norm_num
  have hKe : (base ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) = base := by
    rw [← Real.rpow_mul hbase_nonneg, hexp1, Real.rpow_one]
  have hkrpow : base * n ^ (3 / 4 : ℝ) ≤ k ^ (3 / 4 : ℝ) := by
    have h1 : (base ^ (4 / 3 : ℝ) * n) ^ (3 / 4 : ℝ) ≤ k ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hk (by norm_num)
    rwa [Real.mul_rpow (by positivity) hnpos.le, hKe] at h1
  have hstep1 : (k + 1) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) * k ^ (1 / 4 : ℝ) := by
    have hk1' : k + 1 ≤ 2 * k := by linarith
    calc (k + 1) ^ (1 / 4 : ℝ) ≤ (2 * k) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hk1' (by norm_num)
      _ = (2 : ℝ) ^ (1 / 4 : ℝ) * k ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) hkpos.le
  have hkk : k ^ (3 / 4 : ℝ) * k ^ (1 / 4 : ℝ) = k := by
    rw [← Real.rpow_add hkpos, show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have hCn : 0 ≤ C * n ^ (3 / 4 : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hkrpow
    (show (0 : ℝ) ≤ k ^ (1 / 4 : ℝ) / 4 by positivity)
  have hLHS : base * n ^ (3 / 4 : ℝ) * (k ^ (1 / 4 : ℝ) / 4) =
      C * n ^ (3 / 4 : ℝ) * ((2 : ℝ) ^ (1 / 4 : ℝ) * k ^ (1 / 4 : ℝ)) := by
    rw [hbase_def]; ring
  have hRHS : k ^ (3 / 4 : ℝ) * (k ^ (1 / 4 : ℝ) / 4) = k / 4 := by
    rw [show k ^ (3 / 4 : ℝ) * (k ^ (1 / 4 : ℝ) / 4) =
      (k ^ (3 / 4 : ℝ) * k ^ (1 / 4 : ℝ)) / 4 by ring, hkk]
  rw [hLHS, hRHS] at hmul
  calc C * n ^ (3 / 4 : ℝ) * (k + 1) ^ (1 / 4 : ℝ) ≤
        C * n ^ (3 / 4 : ℝ) * ((2 : ℝ) ^ (1 / 4 : ℝ) * k ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep1 hCn
    _ ≤ k / 4 := hmul

/-- For `A ≥ 0`, `k ≥ 1` and `k ≥ 32 A²`, `A * √(k+1) ≤ k / 4`. -/
lemma sqrt_lin_le (A : ℝ) (hA : 0 ≤ A) (k : ℝ) (hk1 : 1 ≤ k) (hk : 32 * A ^ 2 ≤ k) :
    A * Real.sqrt (k + 1) ≤ k / 4 := by
  have hkpos : (0 : ℝ) < k := by linarith
  have hstep : Real.sqrt (k + 1) ≤ Real.sqrt 2 * Real.sqrt k := by
    have h2k : k + 1 ≤ 2 * k := by linarith
    calc Real.sqrt (k + 1) ≤ Real.sqrt (2 * k) := Real.sqrt_le_sqrt h2k
      _ = Real.sqrt 2 * Real.sqrt k := Real.sqrt_mul (by norm_num) k
  have hAstep : A * Real.sqrt (k + 1) ≤ A * (Real.sqrt 2 * Real.sqrt k) :=
    mul_le_mul_of_nonneg_left hstep hA
  refine hAstep.trans ?_
  have hsqk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hkpos.le
  have h1 : (4 * A * Real.sqrt 2) ^ 2 ≤ k := by
    have heq : (4 * A * Real.sqrt 2) ^ 2 = 32 * A ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [heq]; exact hk
  have hcoef : 4 * A * Real.sqrt 2 ≤ Real.sqrt k :=
    (Real.le_sqrt (by positivity) hkpos.le).mpr h1
  have hmul2 : (4 * A * Real.sqrt 2) * Real.sqrt k ≤ Real.sqrt k * Real.sqrt k :=
    mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg k)
  rw [hsqk] at hmul2
  have hfinal : A * (Real.sqrt 2 * Real.sqrt k) = (4 * A * Real.sqrt 2 * Real.sqrt k) / 4 := by
    ring
  rw [hfinal]
  linarith only [hmul2]

/-! ## Bounding the clean (`g = 1`) limiting series -/

/-- `quarter_pow_le` without a sign hypothesis on `C1`. -/
lemma quarter_pow_le' (C1 : ℝ) (n k : ℝ) (hn : 1 ≤ n) (hk1 : 1 ≤ k)
    (hk : (4 * (2 : ℝ) ^ (1 / 4 : ℝ) * max C1 0) ^ (4 / 3 : ℝ) * n ≤ k) :
    C1 * n ^ (3 / 4 : ℝ) * (k + 1) ^ (1 / 4 : ℝ) ≤ k / 4 := by
  rcases le_total C1 0 with h | h
  · have h1 : C1 * n ^ (3 / 4 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    have h2 : C1 * n ^ (3 / 4 : ℝ) * (k + 1) ^ (1 / 4 : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h1 (by positivity)
    linarith
  · have hCeq : max C1 0 = C1 := max_eq_left h
    rw [hCeq] at hk
    exact quarter_pow_le C1 h n k hn hk1 hk

/-- The bound on the "clean" (`g = 1`) limiting series of (4.9), uniformly in `n, A`. -/
lemma clean_series_bound (κ C1 C2 C3 D : ℝ) (hκ : 0 < κ) (hC2 : 0 < C2) (hC3 : 0 ≤ C3)
    (hD : 0 ≤ D) :
    ∃ CS : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 0 ≤ A →
      Summable (fun k : ℕ => (C2 * ((16 : ℝ) ^ n) ^ D * ((k : ℝ) + 1) ^ D) *
        Real.exp ((n : ℝ) ^ (1 / 4 : ℝ) *
            (min (A + C1) (C1 * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + C1))
          + κ * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * C3 * Real.sqrt ((k : ℝ) + 1))) ∧
      Real.log (∑' k : ℕ, (C2 * ((16 : ℝ) ^ n) ^ D * ((k : ℝ) + 1) ^ D) *
        Real.exp ((n : ℝ) ^ (1 / 4 : ℝ) *
            (min (A + C1) (C1 * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + C1))
          + κ * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * C3 * Real.sqrt ((k : ℝ) + 1))) ≤
        (n : ℝ) ^ (1 / 4 : ℝ) * (A + CS * (n : ℝ) ^ (3 / 4 : ℝ)) := by
  set K : ℝ := max (max ((4 * (2 : ℝ) ^ (1 / 4 : ℝ) * max C1 0) ^ (4 / 3 : ℝ)) (32 * (κ * C3) ^ 2)) 1
    with hK_def
  have hK1 : 1 ≤ K := le_max_right _ _
  have hKa : (4 * (2 : ℝ) ^ (1 / 4 : ℝ) * max C1 0) ^ (4 / 3 : ℝ) ≤ K :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hKb : 32 * (κ * C3) ^ 2 ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  set Γ2 : ℝ := (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ with hΓ2_def
  have hexp14lt1 : Real.exp (-(1 / 4 : ℝ)) < 1 := by
    calc Real.exp (-(1 / 4 : ℝ)) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero
  have h1mexp14pos : (0:ℝ) < 1 - Real.exp (-(1 / 4 : ℝ)) := by linarith
  have hΓ2pos : 0 < Γ2 := by
    rw [hΓ2_def]; exact inv_pos.mpr h1mexp14pos
  have hΓ2ge1 : 1 ≤ Γ2 := by
    have hcancel : Γ2 * (1 - Real.exp (-(1 / 4 : ℝ))) = 1 := by
      rw [hΓ2_def]; exact inv_mul_cancel₀ h1mexp14pos.ne'
    have hexpand : Γ2 * (1 - Real.exp (-(1 / 4 : ℝ))) = Γ2 - Γ2 * Real.exp (-(1 / 4 : ℝ)) := by
      ring
    rw [hexpand] at hcancel
    have hpos2 : 0 ≤ Γ2 * Real.exp (-(1 / 4 : ℝ)) := mul_nonneg hΓ2pos.le (Real.exp_pos _).le
    linarith only [hcancel, hpos2]
  have hlogΓ2nonneg : 0 ≤ Real.log Γ2 := Real.log_nonneg hΓ2ge1
  set C_head : ℝ := |C1| + |Real.log C2| + (D + 1) * Real.log (K + 1) + D * Real.log 16
      + (D + 1) + κ * C3 * Real.sqrt (K + 1) with hChead_def
  set C_tail : ℝ := |Real.log C2| + |C1| + 1 / 4 + |D * Real.log (4 * D)| + Real.log Γ2
      + D * Real.log 16 with hCtail_def
  refine ⟨max C_head C_tail + Real.log 2, fun n hn A hA => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set nR : ℝ := (n : ℝ) with hnR_def
  set t : ℝ := nR ^ (1 / 4 : ℝ) with ht_def
  have htpos : 0 < t := Real.rpow_pos_of_pos (by linarith) _
  have ht1 : 1 ≤ t := by rw [ht_def]; exact Real.one_le_rpow hn1 (by norm_num)
  have hnR34ge1 : 1 ≤ nR ^ (3 / 4 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hidentity : t * nR ^ (3 / 4 : ℝ) = nR := by
    rw [ht_def, ← Real.rpow_add (by linarith : (0:ℝ) < nR)]
    norm_num
  have ht_le_nR : t ≤ nR := by
    calc t = nR ^ (1/4:ℝ) := ht_def
      _ ≤ nR ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = nR := Real.rpow_one nR
  have ht2_eq : t ^ (2:ℕ) = nR ^ (1/2 : ℝ) := by
    rw [ht_def, ← Real.rpow_natCast (nR ^ (1/4:ℝ)) 2, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ nR)]
    norm_num
  have ht2_eq_sqrt : t ^ (2:ℕ) = Real.sqrt nR := by
    rw [ht2_eq, Real.sqrt_eq_rpow]
  have ht2_le_nR : t ^ 2 ≤ nR := by
    rw [ht2_eq]
    calc nR ^ (1/2:ℝ) ≤ nR ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = nR := Real.rpow_one nR
  set M : ℝ := (16 : ℝ) ^ n with hM_def
  have hMpos : 0 < M := by rw [hM_def]; positivity
  have hlogM : Real.log M = nR * Real.log 16 := by
    rw [hM_def]; exact_mod_cast Real.log_pow 16 n
  set f : ℕ → ℝ := fun k : ℕ => (C2 * M ^ D * ((k : ℝ) + 1) ^ D) *
      Real.exp (t * (min (A + C1) (C1 * nR ^ (3/4:ℝ) * ((k : ℝ) + 1) ^ (1/4:ℝ) - k + C1))
        + κ * t ^ 2 * C3 * Real.sqrt ((k : ℝ) + 1)) with hf_def
  set g : ℕ → ℝ := fun k : ℕ => (C2 * M ^ D * Real.exp (t * C1)) *
      (((k : ℝ) + 1) ^ D * Real.exp (-(t / 2 * (k : ℝ)))) with hg_def
  have hf0 : ∀ k, 0 ≤ f k := by intro k; rw [hf_def]; positivity
  have hg0 : ∀ k, 0 ≤ g k := by intro k; rw [hg_def]; positivity
  have ht2pos : 0 < t / 2 := by linarith
  obtain ⟨hgsum, hgbound⟩ := tail_geom_bound D (t / 2) hD ht2pos
  have hgsum' : Summable g := by rw [hg_def]; exact hgsum.mul_left _
  clear_value f g
  set Nc : ℕ := ⌈K * nR⌉₊ with hNc_def
  have hNc_ge : K * nR ≤ (Nc : ℝ) := Nat.le_ceil _
  have hNc1 : 1 ≤ Nc := by
    have h1 : (1:ℝ) ≤ K * nR := by nlinarith only [hK1, hn1]
    have h2 : (1:ℝ) ≤ (Nc:ℝ) := h1.trans hNc_ge
    exact_mod_cast h2
  have hNc_le : (Nc : ℝ) ≤ (K + 1) * nR := by
    have h1 : (Nc : ℝ) < K * nR + 1 := Nat.ceil_lt_add_one (by positivity)
    nlinarith only [h1, hn1]
  -- tail domination: for k ≥ Nc, f k ≤ g k
  have htail : ∀ k : ℕ, Nc ≤ k → f k ≤ g k := by
    intro k hk
    have hkR : K * nR ≤ (k : ℝ) := hNc_ge.trans (by exact_mod_cast hk)
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have h3 := hNc1.trans hk
      exact_mod_cast h3
    have hA1 : (4 * (2:ℝ) ^ (1/4:ℝ) * max C1 0) ^ (4/3:ℝ) * nR ≤ (k : ℝ) :=
      (mul_le_mul_of_nonneg_right hKa (by linarith : (0:ℝ) ≤ nR)).trans hkR
    have hAstep : C1 * nR ^ (3/4:ℝ) * ((k:ℝ) + 1) ^ (1/4:ℝ) ≤ (k:ℝ) / 4 :=
      quarter_pow_le' C1 nR (k:ℝ) hn1 hk1 hA1
    have hBthresh : 32 * (κ * t * C3) ^ 2 ≤ (k : ℝ) := by
      have step1 : 32 * (κ*t*C3)^2 = 32*(κ*C3)^2 * t^2 := by ring
      rw [step1]
      calc 32*(κ*C3)^2 * t^2 ≤ 32*(κ*C3)^2 * nR :=
            mul_le_mul_of_nonneg_left ht2_le_nR (by positivity)
        _ ≤ K * nR := mul_le_mul_of_nonneg_right hKb (by linarith)
        _ ≤ (k:ℝ) := hkR
    have hBstep : κ * t * C3 * Real.sqrt ((k:ℝ) + 1) ≤ (k:ℝ) / 4 :=
      sqrt_lin_le (κ*t*C3) (by positivity) (k:ℝ) hk1 hBthresh
    have hXbound : t * (C1 * nR ^ (3/4:ℝ) * ((k:ℝ)+1) ^ (1/4:ℝ) - (k:ℝ) + C1)
        + κ * t^2 * C3 * Real.sqrt ((k:ℝ)+1) ≤ -(t*(k:ℝ)/2) + t*C1 := by
      have e1 : t * (C1 * nR ^ (3/4:ℝ) * ((k:ℝ)+1) ^ (1/4:ℝ)) ≤ t * ((k:ℝ)/4) :=
        mul_le_mul_of_nonneg_left hAstep htpos.le
      have e2 : κ * t^2 * C3 * Real.sqrt ((k:ℝ)+1) ≤ t * ((k:ℝ)/4) := by
        have hh := mul_le_mul_of_nonneg_left hBstep htpos.le
        calc κ*t^2*C3*Real.sqrt ((k:ℝ)+1) = t*(κ*t*C3*Real.sqrt ((k:ℝ)+1)) := by ring
          _ ≤ t*((k:ℝ)/4) := hh
      have hdist : t * (C1 * nR ^ (3/4:ℝ) * ((k:ℝ)+1) ^ (1/4:ℝ) - (k:ℝ) + C1) =
          t * (C1 * nR ^ (3/4:ℝ) * ((k:ℝ)+1) ^ (1/4:ℝ)) - t*(k:ℝ) + t*C1 := by ring
      rw [hdist]
      linarith only [e1, e2]
    have hBleX : min (A+C1) (C1*nR^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - (k:ℝ) + C1) ≤
        C1*nR^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - (k:ℝ) + C1 := min_le_right _ _
    have hExpBound : t * (min (A+C1) (C1*nR^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - (k:ℝ) + C1))
        + κ*t^2*C3*Real.sqrt ((k:ℝ)+1) ≤ -(t*(k:ℝ)/2) + t*C1 := by
      have hh := mul_le_mul_of_nonneg_left hBleX htpos.le
      linarith only [hXbound, hh]
    have hstep : Real.exp (t * (min (A+C1) (C1*nR^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - (k:ℝ) + C1))
        + κ*t^2*C3*Real.sqrt ((k:ℝ)+1)) ≤ Real.exp (-(t*(k:ℝ)/2) + t*C1) :=
      Real.exp_le_exp.mpr hExpBound
    have heq2 : Real.exp (-(t*(k:ℝ)/2) + t*C1) =
        Real.exp (t*C1) * Real.exp (-(t/2*(k:ℝ))) := by
      rw [show -(t*(k:ℝ)/2) + t*C1 = t*C1 + -(t/2*(k:ℝ)) by ring, Real.exp_add]
    rw [heq2] at hstep
    simp only [hf_def, hg_def]
    calc (C2*M^D*((k:ℝ)+1)^D) *
          Real.exp (t*(min (A+C1) (C1*nR^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ)-(k:ℝ)+C1))
            + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))
        ≤ (C2*M^D*((k:ℝ)+1)^D) * (Real.exp (t*C1) * Real.exp (-(t/2*(k:ℝ)))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (C2*M^D*Real.exp (t*C1)) * (((k:ℝ)+1)^D * Real.exp (-(t/2*(k:ℝ)))) := by ring
  obtain ⟨hfsum, hSplit⟩ := tsum_le_sum_add_tsum Nc hf0 hg0 hgsum' htail
  refine ⟨hfsum, ?_⟩
  -- Head bound
  set Y : ℝ := C2 * M ^ D * (Nc:ℝ) ^ (D+1) *
      Real.exp (t*(A+C1) + κ*t^2*C3*Real.sqrt (Nc:ℝ)) with hY_def
  clear_value Y
  have hY_ge : ∑ k ∈ Finset.range Nc, f k ≤ Y := by
    have hbound_k : ∀ k ∈ Finset.range Nc, f k ≤
        C2 * M ^ D * (Nc:ℝ) ^ D * Real.exp (t*(A+C1) + κ*t^2*C3*Real.sqrt (Nc:ℝ)) := by
      intro k hk
      simp only [Finset.mem_range] at hk
      have hk1 : (k:ℝ) + 1 ≤ (Nc:ℝ) := by exact_mod_cast hk
      have hpow_le : ((k:ℝ)+1) ^ D ≤ (Nc:ℝ) ^ D := Real.rpow_le_rpow (by positivity) hk1 hD
      have hsqrt_le : Real.sqrt ((k:ℝ)+1) ≤ Real.sqrt (Nc:ℝ) := Real.sqrt_le_sqrt hk1
      have hmin_le : min (A+C1) (C1*nR^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - (k:ℝ) + C1) ≤ A + C1 :=
        min_le_left _ _
      have hexp_le : t * (min (A+C1) (C1*nR^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - (k:ℝ) + C1))
          + κ*t^2*C3*Real.sqrt ((k:ℝ)+1) ≤ t*(A+C1) + κ*t^2*C3*Real.sqrt (Nc:ℝ) := by
        have e1 : t * (min (A+C1) (C1*nR^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - (k:ℝ) + C1)) ≤ t*(A+C1) :=
          mul_le_mul_of_nonneg_left hmin_le htpos.le
        have e2 : κ*t^2*C3*Real.sqrt ((k:ℝ)+1) ≤ κ*t^2*C3*Real.sqrt (Nc:ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
        linarith only [e1, e2]
      simp only [hf_def]
      calc (C2 * M ^ D * ((k:ℝ)+1) ^ D) *
            Real.exp (t * (min (A+C1) (C1*nR^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - (k:ℝ) + C1))
              + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))
          ≤ (C2 * M ^ D * ((k:ℝ)+1) ^ D) * Real.exp (t*(A+C1) + κ*t^2*C3*Real.sqrt (Nc:ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (by positivity)
        _ ≤ (C2 * M ^ D * (Nc:ℝ) ^ D) * Real.exp (t*(A+C1) + κ*t^2*C3*Real.sqrt (Nc:ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_left hpow_le (by positivity)
    rw [hY_def]
    calc ∑ k ∈ Finset.range Nc, f k ≤
          ∑ _k ∈ Finset.range Nc, C2*M^D*(Nc:ℝ)^D*Real.exp (t*(A+C1)+κ*t^2*C3*Real.sqrt (Nc:ℝ)) :=
          Finset.sum_le_sum hbound_k
      _ = (Nc:ℝ) * (C2*M^D*(Nc:ℝ)^D*Real.exp (t*(A+C1)+κ*t^2*C3*Real.sqrt (Nc:ℝ))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = C2*M^D*(Nc:ℝ)^(D+1)*Real.exp (t*(A+C1)+κ*t^2*C3*Real.sqrt (Nc:ℝ)) := by
          rw [Real.rpow_add (show (0:ℝ) < (Nc:ℝ) by positivity), Real.rpow_one]
          ring
  have hNcpos : 0 < (Nc:ℝ) := by exact_mod_cast hNc1
  have hMDpos : 0 < M ^ D := Real.rpow_pos_of_pos hMpos D
  have hNcD1pos : 0 < (Nc:ℝ) ^ (D+1) := Real.rpow_pos_of_pos hNcpos (D+1)
  have hexpHeadPos : 0 < Real.exp (t*(A+C1) + κ*t^2*C3*Real.sqrt (Nc:ℝ)) := Real.exp_pos _
  have hYpos : 0 < Y := by
    rw [hY_def]
    exact mul_pos (mul_pos (mul_pos hC2 hMDpos) hNcD1pos) hexpHeadPos
  have hlogY : Real.log Y = Real.log C2 + D * Real.log M + (D+1) * Real.log (Nc:ℝ) +
      (t*(A+C1) + κ*t^2*C3*Real.sqrt (Nc:ℝ)) := by
    rw [hY_def,
      Real.log_mul (mul_pos (mul_pos hC2 hMDpos) hNcD1pos).ne' hexpHeadPos.ne',
      Real.log_mul (mul_pos hC2 hMDpos).ne' hNcD1pos.ne',
      Real.log_mul hC2.ne' hMDpos.ne',
      log_rpow_nonneg M D hMpos.le, log_rpow_nonneg (Nc:ℝ) (D+1) hNcpos.le, Real.log_exp]
  have hlogNc_le : Real.log (Nc:ℝ) ≤ Real.log (K+1) + nR := by
    have h1 : Real.log (Nc:ℝ) ≤ Real.log ((K+1)*nR) :=
      Real.log_le_log hNcpos hNc_le
    have h2 : Real.log ((K+1)*nR) = Real.log (K+1) + Real.log nR :=
      Real.log_mul (by positivity) (show (0:ℝ) < nR by linarith).ne'
    have h3 : Real.log nR ≤ nR := by
      have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < nR by linarith)
      linarith only [h4]
    linarith only [h1, h2, h3]
  have hsqrtNc_le : Real.sqrt (Nc:ℝ) ≤ Real.sqrt (K+1) * Real.sqrt nR := by
    calc Real.sqrt (Nc:ℝ) ≤ Real.sqrt ((K+1)*nR) := Real.sqrt_le_sqrt hNc_le
      _ = Real.sqrt (K+1) * Real.sqrt nR := Real.sqrt_mul (by positivity) nR
  have hsqrtnR_le : Real.sqrt nR ≤ nR := by
    have hnRsq : nR ≤ nR^2 := by
      nlinarith only [mul_nonneg (by linarith : (0:ℝ) ≤ nR - 1) (by linarith : (0:ℝ) ≤ nR)]
    calc Real.sqrt nR ≤ Real.sqrt (nR^2) := Real.sqrt_le_sqrt hnRsq
      _ = nR := Real.sqrt_sq (by linarith)
  have hlogK1nonneg : 0 ≤ Real.log (K+1) := Real.log_nonneg (by linarith)
  have hC2_le : Real.log C2 ≤ |Real.log C2| * nR :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hn1)
  have hDlogM_eq : D * Real.log M = D * Real.log 16 * nR := by rw [hlogM]; ring
  have hNcterm_le : (D+1) * Real.log (Nc:ℝ) ≤ (D+1)*Real.log (K+1)*nR + (D+1)*nR := by
    have h1 : (D+1) * Real.log (Nc:ℝ) ≤ (D+1) * (Real.log (K+1) + nR) :=
      mul_le_mul_of_nonneg_left hlogNc_le (by positivity)
    have h1' : (D+1) * (Real.log (K+1) + nR) = (D+1)*Real.log (K+1) + (D+1)*nR := by ring
    rw [h1'] at h1
    have h2 : (D+1) * Real.log (K+1) ≤ (D+1)*Real.log (K+1)*nR :=
      le_mul_of_one_le_right (by positivity) hn1
    linarith only [h1, h2]
  have htC1_le : t * C1 ≤ |C1| * nR := by
    have h1 : C1 ≤ |C1| := le_abs_self C1
    have h2 : t * C1 ≤ t * |C1| := mul_le_mul_of_nonneg_left h1 htpos.le
    have h3 : t * |C1| ≤ nR * |C1| := mul_le_mul_of_nonneg_right ht_le_nR (abs_nonneg C1)
    nlinarith only [h2, h3]
  have hsqrtterm_le : κ*t^2*C3*Real.sqrt (Nc:ℝ) ≤ κ*C3*Real.sqrt (K+1)*nR := by
    have h1 : κ*t^2*C3*Real.sqrt (Nc:ℝ) ≤ κ*t^2*C3*(Real.sqrt (K+1)*Real.sqrt nR) :=
      mul_le_mul_of_nonneg_left hsqrtNc_le (by positivity)
    have h2 : κ*t^2*C3*(Real.sqrt (K+1)*Real.sqrt nR) =
        κ*C3*Real.sqrt (K+1)*(t^2*Real.sqrt nR) := by ring
    have h3 : t^2 * Real.sqrt nR = nR := by
      rw [ht2_eq_sqrt]; exact Real.mul_self_sqrt (by linarith)
    rw [h2, h3] at h1
    exact h1
  have hCheadnR : C_head * nR = |C1| * nR + |Real.log C2| * nR + (D+1)*Real.log (K+1)*nR
      + D*Real.log 16*nR + (D+1)*nR + κ*C3*Real.sqrt (K+1)*nR := by
    rw [hChead_def]; ring
  have hheadfinal : Real.log Y ≤ t*A + C_head*nR := by
    rw [hlogY, hCheadnR]
    linarith only [hC2_le, hDlogM_eq, hNcterm_le, htC1_le, hsqrtterm_le]
  have hYexp : Y ≤ Real.exp (t*A + C_head*nR) := by
    calc Y = Real.exp (Real.log Y) := (Real.exp_log hYpos).symm
      _ ≤ Real.exp (t*A + C_head*nR) := Real.exp_le_exp.mpr hheadfinal
  -- Tail bound
  have ht4pos : (0:ℝ) < t/2/2 := by linarith
  have hexp4lt1 : Real.exp (-(t/2/2)) < 1 := by
    calc Real.exp (-(t/2/2)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have h1mexp4pos : (0:ℝ) < 1 - Real.exp (-(t/2/2)) := by linarith
  have hpowDpos : 0 < (2*D/(t/2)) ^ D := by
    rcases hD.eq_or_lt with hD0 | hD0
    · rw [← hD0]; simp
    · exact Real.rpow_pos_of_pos (by positivity) D
  set Z : ℝ := (C2*M^D*Real.exp (t*C1)) *
      ((2*D/(t/2))^D * Real.exp (-D) * Real.exp (t/2/2) * (1-Real.exp (-(t/2/2)))⁻¹) with hZ_def
  clear_value Z
  have hgtsum_le : ∑' k, g k ≤ Z := by
    have heq1 : ∑' k, g k = (C2*M^D*Real.exp (t*C1)) *
        ∑' k : ℕ, (((k:ℝ)+1)^D * Real.exp (-(t/2*(k:ℝ)))) := by
      rw [hg_def, tsum_mul_left]
    rw [heq1, hZ_def]
    exact mul_le_mul_of_nonneg_left hgbound (by positivity)
  have hZpos : 0 < Z := by
    rw [hZ_def]
    exact mul_pos (mul_pos (mul_pos hC2 hMDpos) (Real.exp_pos _))
      (mul_pos (mul_pos (mul_pos hpowDpos (Real.exp_pos _)) (Real.exp_pos _))
        (inv_pos.mpr h1mexp4pos))
  have hlogZ_split : Real.log Z = Real.log (C2*M^D*Real.exp (t*C1)) +
      Real.log ((2*D/(t/2))^D * Real.exp (-D) * Real.exp (t/2/2) * (1-Real.exp (-(t/2/2)))⁻¹) := by
    rw [hZ_def, Real.log_mul (mul_pos (mul_pos hC2 hMDpos) (Real.exp_pos _)).ne'
      (mul_pos (mul_pos (mul_pos hpowDpos (Real.exp_pos _)) (Real.exp_pos _))
        (inv_pos.mpr h1mexp4pos)).ne']
  have hlogPrefactor : Real.log (C2*M^D*Real.exp (t*C1)) = Real.log C2 + D*Real.log M + t*C1 := by
    rw [Real.log_mul (mul_pos hC2 hMDpos).ne' (Real.exp_pos _).ne',
      Real.log_mul hC2.ne' hMDpos.ne', log_rpow_nonneg M D hMpos.le, Real.log_exp]
  have hlogBracket : Real.log ((2*D/(t/2))^D * Real.exp (-D) * Real.exp (t/2/2) *
      (1-Real.exp (-(t/2/2)))⁻¹) =
      D * Real.log (2*D/(t/2)) + (-D) + t/2/2 - Real.log (1 - Real.exp (-(t/2/2))) := by
    rw [Real.log_mul (mul_pos (mul_pos hpowDpos (Real.exp_pos _)) (Real.exp_pos _)).ne'
          (inv_ne_zero h1mexp4pos.ne'),
      Real.log_mul (mul_pos hpowDpos (Real.exp_pos _)).ne' (Real.exp_pos _).ne',
      Real.log_mul hpowDpos.ne' (Real.exp_pos _).ne',
      log_rpow_nonneg (2*D/(t/2)) D (by positivity), Real.log_exp, Real.log_exp, Real.log_inv]
    ring
  have hDlogfrac_le : D * Real.log (2*D/(t/2)) ≤ |D * Real.log (4*D)| := by
    have heq : (2*D/(t/2)) = 4*D/t := by ring
    rw [heq]
    rcases hD.eq_or_lt with hD0 | hD0
    · rw [← hD0]; simp
    · have hlogsplit : Real.log (4*D/t) = Real.log (4*D) - Real.log t :=
        Real.log_div (by positivity) htpos.ne'
      rw [hlogsplit, mul_sub]
      have h1 : 0 ≤ D * Real.log t := mul_nonneg hD0.le (Real.log_nonneg ht1)
      have h2 : D * Real.log (4*D) ≤ |D * Real.log (4*D)| := le_abs_self _
      linarith
  have htterm_le : t/2/2 ≤ (1/4)*nR := by
    have heq : t/2/2 = t/4 := by ring
    rw [heq]; linarith only [ht_le_nR]
  have hlogGamma_le : -Real.log (1 - Real.exp (-(t/2/2))) ≤ Real.log Γ2 := by
    have hexple : Real.exp (-(t/2/2)) ≤ Real.exp (-(1/4:ℝ)) := by
      apply Real.exp_le_exp.mpr
      have heq : t/2/2 = t/4 := by ring
      rw [heq]; linarith only [ht1]
    have hle : 1 - Real.exp (-(1/4:ℝ)) ≤ 1 - Real.exp (-(t/2/2)) := by linarith
    have hlog_le : Real.log (1 - Real.exp (-(1/4:ℝ))) ≤ Real.log (1 - Real.exp (-(t/2/2))) :=
      Real.log_le_log (by linarith only [hexp14lt1]) hle
    have hinv_eq : Real.log Γ2 = -Real.log (1 - Real.exp (-(1/4:ℝ))) := by
      rw [hΓ2_def, Real.log_inv]
    linarith only [hlog_le, hinv_eq]
  have hCtailnR : C_tail * nR = |Real.log C2| * nR + |C1| * nR + (1/4)*nR + |D*Real.log (4*D)| * nR
      + Real.log Γ2*nR + D*Real.log 16*nR := by
    rw [hCtail_def]; ring
  have htailfinal : Real.log Z ≤ C_tail * nR := by
    rw [hlogZ_split, hlogPrefactor, hlogBracket, hCtailnR]
    have hDlogfrac_le' : D * Real.log (2*D/(t/2)) ≤ |D * Real.log (4*D)| * nR :=
      hDlogfrac_le.trans (le_mul_of_one_le_right (abs_nonneg _) hn1)
    have hGamma_le' : Real.log Γ2 ≤ Real.log Γ2 * nR :=
      le_mul_of_one_le_right hlogΓ2nonneg hn1
    linarith only [hDlogfrac_le', hC2_le, hDlogM_eq, htC1_le, htterm_le, hlogGamma_le, hGamma_le', hD]
  have hZexp : Z ≤ Real.exp (C_tail * nR) := by
    calc Z = Real.exp (Real.log Z) := (Real.exp_log hZpos).symm
      _ ≤ Real.exp (C_tail * nR) := Real.exp_le_exp.mpr htailfinal
  -- Combine
  have hSfin : ∑' k, f k ≤ Real.exp (t*A + C_head*nR) + Real.exp (C_tail*nR) := by
    calc ∑' k, f k ≤ ∑ k ∈ Finset.range Nc, f k + ∑' k, g k := hSplit
      _ ≤ Y + Z := add_le_add hY_ge hgtsum_le
      _ ≤ Real.exp (t*A+C_head*nR) + Real.exp (C_tail*nR) := add_le_add hYexp hZexp
  have hb1 : Real.exp (t*A+C_head*nR) ≤ Real.exp (t*A + max C_head C_tail*nR) := by
    apply Real.exp_le_exp.mpr
    have h1 : C_head*nR ≤ max C_head C_tail*nR :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    linarith
  have hb2 : Real.exp (C_tail*nR) ≤ Real.exp (t*A + max C_head C_tail*nR) := by
    apply Real.exp_le_exp.mpr
    have h1 : C_tail*nR ≤ max C_head C_tail*nR :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    have h2 : 0 ≤ t*A := mul_nonneg htpos.le hA
    linarith
  have hmaxbound : Real.exp (t*A + C_head*nR) + Real.exp (C_tail*nR) ≤
      2 * Real.exp (t*A + max C_head C_tail * nR) := by linarith only [hb1, hb2]
  have hf0pos : 0 < f 0 := by rw [hf_def]; positivity
  have hfsumpos : 0 < ∑' k, f k := lt_of_lt_of_le hf0pos (hfsum.le_tsum 0 (fun j _ => hf0 j))
  have hlog2le : Real.log 2 ≤ Real.log 2 * nR := le_mul_of_one_le_right (by positivity) hn1
  have hstep2 : ∑' k, f k ≤ Real.exp (Real.log 2 + (t*A + max C_head C_tail*nR)) := by
    calc ∑' k, f k ≤ 2 * Real.exp (t*A+max C_head C_tail*nR) := hSfin.trans hmaxbound
      _ = Real.exp (Real.log 2) * Real.exp (t*A+max C_head C_tail*nR) := by
          rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
      _ = Real.exp (Real.log 2 + (t*A+max C_head C_tail*nR)) := (Real.exp_add _ _).symm
  have hfinallog : Real.log (∑' k, f k) ≤ Real.log 2 + (t*A + max C_head C_tail * nR) := by
    calc Real.log (∑' k, f k) ≤
          Real.log (Real.exp (Real.log 2 + (t*A + max C_head C_tail*nR))) :=
          Real.log_le_log hfsumpos hstep2
      _ = Real.log 2 + (t*A + max C_head C_tail*nR) := Real.log_exp _
  have hgoal_eq : t * (A + (max C_head C_tail + Real.log 2) * nR ^ (3/4:ℝ)) =
      t*A + max C_head C_tail*nR + Real.log 2*nR := by
    have h1 : t * ((max C_head C_tail + Real.log 2) * nR ^ (3/4:ℝ)) =
        (max C_head C_tail + Real.log 2) * (t * nR^(3/4:ℝ)) := by ring
    rw [mul_add, h1, hidentity]; ring
  rw [hgoal_eq]
  linarith only [hfinallog, hlog2le]

/-! ## Summability of the crude-bound (domination) series -/

/-- The series dominating `Z_δ(t)` uniformly via the crude bound (4.5) and `g ≤ M` is
summable, for any real `Cn` (no sign restriction) and any `M > 0`, `t > 0`. -/
lemma crude_domination_summable (κ C2 C3 D Cn M t : ℝ) (hκ : 0 < κ) (hC2 : 0 < C2)
    (hC3 : 0 ≤ C3) (hD : 0 ≤ D) (hMpos : 0 < M) (htpos : 0 < t) :
    Summable (fun k : ℕ => (C2 * M ^ D * ((k : ℝ) + 1) ^ D) *
      Real.exp (t * (Cn * ((k : ℝ) + 1) ^ (1/4:ℝ) - (k : ℝ))
        + κ * t ^ 2 * C3 * M ^ 2 * Real.sqrt ((k : ℝ) + 1))) := by
  set K' : ℝ := max (max ((4 * (2:ℝ) ^ (1/4:ℝ) * max Cn 0) ^ (4/3:ℝ))
      (32 * (κ * t * C3 * M ^ 2) ^ 2)) 1 with hK'_def
  have hK'a : (4 * (2:ℝ) ^ (1/4:ℝ) * max Cn 0) ^ (4/3:ℝ) ≤ K' :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hK'b : 32 * (κ * t * C3 * M ^ 2) ^ 2 ≤ K' := (le_max_right _ _).trans (le_max_left _ _)
  have hK'1 : (1:ℝ) ≤ K' := le_max_right _ _
  set f : ℕ → ℝ := fun k : ℕ => (C2 * M ^ D * ((k : ℝ) + 1) ^ D) *
      Real.exp (t * (Cn * ((k : ℝ) + 1) ^ (1/4:ℝ) - (k : ℝ))
        + κ * t ^ 2 * C3 * M ^ 2 * Real.sqrt ((k : ℝ) + 1)) with hf_def
  set g : ℕ → ℝ := fun k : ℕ => (C2 * M ^ D) * (((k : ℝ) + 1) ^ D * Real.exp (-(t/2 * (k:ℝ))))
    with hg_def
  have hf0 : ∀ k, 0 ≤ f k := by intro k; rw [hf_def]; positivity
  have hg0 : ∀ k, 0 ≤ g k := by intro k; rw [hg_def]; positivity
  have ht2pos : 0 < t / 2 := by linarith
  obtain ⟨hgsum, -⟩ := tail_geom_bound D (t / 2) hD ht2pos
  have hgsum' : Summable g := by rw [hg_def]; exact hgsum.mul_left _
  clear_value f g
  set Ne : ℕ := ⌈K'⌉₊ with hNe_def
  have hNe_ge : K' ≤ (Ne : ℝ) := Nat.le_ceil _
  have hNe1 : 1 ≤ Ne := by
    have h2 : (1:ℝ) ≤ (Ne:ℝ) := hK'1.trans hNe_ge
    exact_mod_cast h2
  have htail : ∀ k : ℕ, Ne ≤ k → f k ≤ g k := by
    intro k hk
    have hkR : K' ≤ (k:ℝ) := hNe_ge.trans (by exact_mod_cast hk)
    have hk1 : (1:ℝ) ≤ (k:ℝ) := by
      have h3 := hNe1.trans hk
      exact_mod_cast h3
    have hAa : (4 * (2:ℝ) ^ (1/4:ℝ) * max Cn 0) ^ (4/3:ℝ) * (1:ℝ) ≤ (k:ℝ) := by
      rw [mul_one]; exact hK'a.trans hkR
    have hAstep0 : Cn * (1:ℝ) ^ (3/4:ℝ) * ((k:ℝ)+1) ^ (1/4:ℝ) ≤ (k:ℝ)/4 :=
      quarter_pow_le' Cn 1 (k:ℝ) (le_refl 1) hk1 hAa
    have hAstep : Cn * ((k:ℝ)+1) ^ (1/4:ℝ) ≤ (k:ℝ)/4 := by
      rwa [Real.one_rpow, mul_one] at hAstep0
    have hBthresh : 32 * (κ*t*C3*M^2) ^ 2 ≤ (k:ℝ) := hK'b.trans hkR
    have hBstep : κ * t * C3 * M^2 * Real.sqrt ((k:ℝ)+1) ≤ (k:ℝ)/4 :=
      sqrt_lin_le (κ*t*C3*M^2) (by positivity) (k:ℝ) hk1 hBthresh
    have hdist : t * (Cn * ((k:ℝ)+1) ^ (1/4:ℝ) - (k:ℝ)) =
        t * (Cn * ((k:ℝ)+1) ^ (1/4:ℝ)) - t*(k:ℝ) := by ring
    have e1 : t * (Cn * ((k:ℝ)+1) ^ (1/4:ℝ)) ≤ t * ((k:ℝ)/4) :=
      mul_le_mul_of_nonneg_left hAstep htpos.le
    have e2 : κ*t^2*C3*M^2*Real.sqrt ((k:ℝ)+1) ≤ t * ((k:ℝ)/4) := by
      have hh := mul_le_mul_of_nonneg_left hBstep htpos.le
      calc κ*t^2*C3*M^2*Real.sqrt ((k:ℝ)+1) = t*(κ*t*C3*M^2*Real.sqrt ((k:ℝ)+1)) := by ring
        _ ≤ t*((k:ℝ)/4) := hh
    have hExpBound : t * (Cn * ((k:ℝ)+1) ^ (1/4:ℝ) - (k:ℝ))
        + κ*t^2*C3*M^2*Real.sqrt ((k:ℝ)+1) ≤ -(t*(k:ℝ)/2) := by
      rw [hdist]; linarith only [e1, e2]
    have hstep : Real.exp (t * (Cn * ((k:ℝ)+1) ^ (1/4:ℝ) - (k:ℝ))
        + κ*t^2*C3*M^2*Real.sqrt ((k:ℝ)+1)) ≤ Real.exp (-(t*(k:ℝ)/2)) :=
      Real.exp_le_exp.mpr hExpBound
    have heq2 : Real.exp (-(t*(k:ℝ)/2)) = Real.exp (-(t/2*(k:ℝ))) := by
      rw [show -(t*(k:ℝ)/2) = -(t/2*(k:ℝ)) by ring]
    rw [heq2] at hstep
    simp only [hf_def, hg_def]
    rw [← mul_assoc (C2 * M ^ D)]
    exact mul_le_mul_of_nonneg_left hstep
      (show (0:ℝ) ≤ C2 * M ^ D * ((k:ℝ)+1) ^ D by positivity)
  exact (tsum_le_sum_add_tsum Ne hf0 hg0 hgsum' htail).1

/-- For a nonnegative summable series, some finite cutoff leaves a tail summing to at most `1`. -/
lemma tsum_tail_le_one {D : ℕ → ℝ} (hDsum : Summable D) :
    ∃ Ne : ℕ, ∑' k, D k - ∑ k ∈ Finset.range Ne, D k ≤ 1 := by
  have htend : Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, D k) Filter.atTop (𝓝 (∑' k, D k)) :=
    hDsum.hasSum.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun N => ∑' k, D k - ∑ k ∈ Finset.range N, D k) Filter.atTop (𝓝 0) := by
    have h3 := (tendsto_const_nhds (x := ∑' k, D k)).sub htend
    simpa using h3
  obtain ⟨Ne, hNe⟩ := (Metric.tendsto_atTop.mp h2) 1 (by norm_num)
  refine ⟨Ne, ?_⟩
  have h4 := hNe Ne (le_refl Ne)
  rw [Real.dist_eq, sub_zero] at h4
  exact (le_abs_self _).trans h4.le

/-- The indicator-tail of a nonnegative summable series is summable, with tsum the difference
of the full sum and the head. -/
lemma tail_summable_and_eq {D : ℕ → ℝ} (hDsum : Summable D) (N : ℕ) :
    Summable (fun k => if N ≤ k then D k else 0) ∧
    ∑' k, (if N ≤ k then D k else 0) = ∑' k, D k - ∑ k ∈ Finset.range N, D k := by
  set auxHead : ℕ → ℝ := fun k => if k < N then D k else 0 with hauxHead_def
  have hauxHead_sum : Summable auxHead := summable_of_ne_finset_zero (s := Finset.range N)
    (fun b hb => by
      simp only [Finset.mem_range, not_lt] at hb
      simp only [hauxHead_def, if_neg (not_lt.mpr hb)])
  have hauxHead_eq : ∑' k, auxHead k = ∑ k ∈ Finset.range N, D k := by
    have hHS : HasSum auxHead (∑ k ∈ Finset.range N, auxHead k) := hasSum_sum_of_ne_finset_zero
      (s := Finset.range N) (fun b hb => by
        simp only [Finset.mem_range, not_lt] at hb
        simp only [hauxHead_def, if_neg (not_lt.mpr hb)])
    rw [hHS.tsum_eq]
    exact Finset.sum_congr rfl
      (fun k hk => by simp only [hauxHead_def, if_pos (Finset.mem_range.mp hk)])
  have heq : ∀ k, (if N ≤ k then D k else 0) = D k - auxHead k := by
    intro k
    by_cases hk : N ≤ k
    · simp only [if_pos hk, hauxHead_def, if_neg (not_lt.mpr hk)]; ring
    · simp only [if_neg hk, hauxHead_def, if_pos (not_le.mp hk)]; ring
  have heqfun : (fun k => if N ≤ k then D k else 0) = fun k => D k - auxHead k := funext heq
  refine ⟨by rw [heqfun]; exact hDsum.sub hauxHead_sum, ?_⟩
  rw [heqfun, (hDsum.hasSum.sub hauxHead_sum.hasSum).tsum_eq, hauxHead_eq]

/-! ## The growth factor `g_{δ,n}(k)` tends to `1` pointwise as `δ ↓ 0` -/

lemma gFactor_eventually_one (M : ℕ) (c0 : ℝ) (hc0 : 0 < c0) (hM : 0 < M) (k : ℕ) :
    ∀ᶠ δ in nhdsWithin (0:ℝ) (Set.Ioi 0), Blueprint.Draft.gFactor M δ c0 k = 1 := by
  have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hc0M : (0:ℝ) < c0 / (M:ℝ) := by positivity
  have htendsto : Filter.Tendsto (fun δ:ℝ => δ^2*((k:ℝ)+1)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun δ:ℝ => δ^2*((k:ℝ)+1)) (𝓝 (0:ℝ)) (𝓝 (0*((k:ℝ)+1))) := by
      apply Filter.Tendsto.mul _ tendsto_const_nhds
      simpa using (continuous_pow 2).tendsto (0:ℝ)
    simpa using h1.mono_left nhdsWithin_le_nhds
  have heventually : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ^2*((k:ℝ)+1) < c0/(M:ℝ) := by
    have h2 := (Metric.tendsto_nhds.mp htendsto) (c0/(M:ℝ)) hc0M
    filter_upwards [h2] with δ hδ
    rw [Real.dist_eq, sub_zero] at hδ
    calc δ^2*((k:ℝ)+1) ≤ |δ^2*((k:ℝ)+1)| := le_abs_self _
      _ < c0/(M:ℝ) := hδ
  filter_upwards [heventually] with δ hδ
  simp only [Blueprint.Draft.gFactor, if_pos hδ.le]

end ZLimitAux

open ZLimitAux

/-- **Node `ZL`** ((4.8)–(4.9) limit, real analysis). -/
theorem zLimitBound : Blueprint.Draft.ZLimitBound := by
  intro κ C1 C2 C3 D c0 hκ hC2 hC3 hD hc0
  obtain ⟨CS, hCS⟩ := clean_series_bound κ C1 C2 C3 D hκ hC2 hC3 hD
  set CS' : ℝ := max CS 0 with hCS'_def
  have hCS'nonneg : 0 ≤ CS' := le_max_right _ _
  have hCSCS' : CS ≤ CS' := le_max_left _ _
  refine ⟨CS' + Real.log 2 + 1, fun n hn A Cn hA mδ hCrude hLimit θ hθ => ?_⟩
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  set t : ℝ := (n:ℝ) ^ (1/4:ℝ) with ht_def
  set M : ℝ := (16:ℝ) ^ n with hM_def
  have htpos : 0 < t := by rw [ht_def]; exact Real.rpow_pos_of_pos (by linarith) _
  have ht1 : 1 ≤ t := by rw [ht_def]; exact Real.one_le_rpow hn1 (by norm_num)
  have hnR34ge1 : 1 ≤ (n:ℝ) ^ (3/4:ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hidentity : t * (n:ℝ) ^ (3/4:ℝ) = (n:ℝ) := by
    rw [ht_def, ← Real.rpow_add (by linarith : (0:ℝ) < (n:ℝ))]; norm_num
  have hMpos : 0 < M := by rw [hM_def]; positivity
  have hMnatpos : 0 < (16^n : ℕ) := by positivity
  have hMcast : ((16^n:ℕ):ℝ) = M := by rw [hM_def]; push_cast; ring
  have hMnat1 : (1:ℝ) ≤ M := by
    rw [← hMcast]
    exact_mod_cast Nat.one_le_pow n 16 (by norm_num)
  obtain ⟨hSsum, hSbound⟩ := hCS n hn A hA
  rw [← ht_def, ← hM_def] at hSbound hSsum
  have hSbound' : Real.log (∑' k : ℕ, (C2 * M ^ D * ((k:ℝ)+1) ^ D) *
      Real.exp (t * (min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
        + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))) ≤ t * (A + CS' * (n:ℝ)^(3/4:ℝ)) := by
    have hCSstep : CS * (n:ℝ)^(3/4:ℝ) ≤ CS' * (n:ℝ)^(3/4:ℝ) :=
      mul_le_mul_of_nonneg_right hCSCS' (by positivity)
    have hstep : t * (A + CS * (n:ℝ)^(3/4:ℝ)) ≤ t * (A + CS' * (n:ℝ)^(3/4:ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hCSstep]) htpos.le
    linarith only [hSbound, hstep]
  -- crude domination series
  set Dser : ℕ → ℝ := fun k => (C2 * M ^ D * ((k:ℝ)+1) ^ D) *
      Real.exp (t * (Cn*((k:ℝ)+1)^(1/4:ℝ)-(k:ℝ))
        + κ*t^2*C3*M^2*Real.sqrt ((k:ℝ)+1)) with hDser_def
  have hDsum : Summable Dser := by
    rw [hDser_def]
    exact crude_domination_summable κ C2 C3 D Cn M t hκ hC2 hC3 hD hMpos htpos
  clear_value Dser
  obtain ⟨Ne, hNe_tail⟩ := tsum_tail_le_one hDsum
  obtain ⟨hDtail_sum, hDtail_eq⟩ := tail_summable_and_eq hDsum Ne
  have hDtail_le1 : ∑' k, (if Ne ≤ k then Dser k else 0) ≤ 1 := by
    rw [hDtail_eq]; exact hNe_tail
  have hDtail0 : ∀ k, 0 ≤ (if Ne ≤ k then Dser k else 0) := by
    intro k
    by_cases hk : Ne ≤ k
    · rw [if_pos hk, hDser_def]; positivity
    · simp [if_neg hk]
  -- pointwise eventually facts on range Ne
  have hEach : ∀ k ∈ Finset.range Ne, ∀ᶠ δ in 𝓝[>] (0:ℝ),
      mδ δ k ≤ min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1) + θ ∧
      Blueprint.Draft.gFactor (16^n) δ c0 k = 1 := by
    intro k _
    filter_upwards [hLimit k θ hθ, gFactor_eventually_one (16^n) c0 hc0 hMnatpos k] with δ hδ1 hδ2
    exact ⟨hδ1, hδ2⟩
  have hHead : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ k ∈ Finset.range Ne,
      mδ δ k ≤ min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1) + θ ∧
      Blueprint.Draft.gFactor (16^n) δ c0 k = 1 :=
    (Finset.eventually_all (Finset.range Ne)).mpr hEach
  have hδlt1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [hHead, hδlt1, self_mem_nhdsWithin] with δ hHδ hδlt1' hδmem
  have hδpos : 0 < δ := hδmem
  have hδIoo : δ ∈ Set.Ioo (0:ℝ) 1 := ⟨hδpos, hδlt1'⟩
  show (Real.log (∑' k : ℕ, (C2 * M ^ D * ((k:ℝ)+1) ^ D) *
      Real.exp (t * (mδ δ k)
        + κ*t^2*(C3*(Blueprint.Draft.gFactor (16^n) δ c0 k)^2*Real.sqrt ((k:ℝ)+1)))) + 1) / t ≤
    A + (CS' + Real.log 2 + 1) * (n:ℝ)^(3/4:ℝ) + θ
  set fδ : ℕ → ℝ := fun k => (C2 * M ^ D * ((k:ℝ)+1) ^ D) *
      Real.exp (t * (mδ δ k)
        + κ*t^2*(C3*(Blueprint.Draft.gFactor (16^n) δ c0 k)^2*Real.sqrt ((k:ℝ)+1)))
    with hfδ_def
  -- domination: fδ k ≤ Dser k
  have hgFactor_nonneg : ∀ k, 0 ≤ Blueprint.Draft.gFactor (16^n) δ c0 k := by
    intro k
    simp only [Blueprint.Draft.gFactor]
    split_ifs <;> positivity
  have hgFactor_le : ∀ k, Blueprint.Draft.gFactor (16^n) δ c0 k ≤ M := by
    intro k
    simp only [Blueprint.Draft.gFactor]
    split_ifs with h
    · linarith only [hMnat1]
    · exact le_of_eq hMcast
  have hfδ_le_Dser : ∀ k, fδ k ≤ Dser k := by
    intro k
    have hm_le : mδ δ k ≤ Cn*((k:ℝ)+1)^(1/4:ℝ) - (k:ℝ) := hCrude δ hδIoo k
    have hv_le : C3*(Blueprint.Draft.gFactor (16^n) δ c0 k)^2*Real.sqrt ((k:ℝ)+1) ≤
        C3*M^2*Real.sqrt ((k:ℝ)+1) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hC3
      exact pow_le_pow_left₀ (hgFactor_nonneg k) (hgFactor_le k) 2
    have hexp_le : t*(mδ δ k) + κ*t^2*(C3*(Blueprint.Draft.gFactor (16^n) δ c0 k)^2*Real.sqrt ((k:ℝ)+1)) ≤
        t*(Cn*((k:ℝ)+1)^(1/4:ℝ)-(k:ℝ)) + κ*t^2*C3*M^2*Real.sqrt ((k:ℝ)+1) := by
      have e1 : t*(mδ δ k) ≤ t*(Cn*((k:ℝ)+1)^(1/4:ℝ)-(k:ℝ)) :=
        mul_le_mul_of_nonneg_left hm_le htpos.le
      have e2 : κ*t^2*(C3*(Blueprint.Draft.gFactor (16^n) δ c0 k)^2*Real.sqrt ((k:ℝ)+1)) ≤
          κ*t^2*C3*M^2*Real.sqrt ((k:ℝ)+1) := by
        have hh := mul_le_mul_of_nonneg_left hv_le (show (0:ℝ) ≤ κ*t^2 by positivity)
        have heq : κ*t^2*(C3*M^2*Real.sqrt ((k:ℝ)+1)) = κ*t^2*C3*M^2*Real.sqrt ((k:ℝ)+1) := by ring
        linarith only [hh, heq.le, heq.ge]
      linarith only [e1, e2]
    simp only [hfδ_def, hDser_def]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (by positivity)
  have htail_δ : ∀ k, Ne ≤ k → fδ k ≤ (if Ne ≤ k then Dser k else 0) := by
    intro k hk
    rw [if_pos hk]
    exact hfδ_le_Dser k
  -- head bound: for k < Ne, fδ k ≤ exp(tθ) * (S's k-th summand)
  have hfδ_le_headS : ∀ k ∈ Finset.range Ne, fδ k ≤ Real.exp (t*θ) *
      ((C2*M^D*((k:ℝ)+1)^D) * Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
        + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))) := by
    intro k hk
    obtain ⟨hm_le, hg_eq⟩ := hHδ k hk
    have hexp_le : t*(mδ δ k) + κ*t^2*(C3*(Blueprint.Draft.gFactor (16^n) δ c0 k)^2*Real.sqrt ((k:ℝ)+1)) ≤
        t*θ + (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
          + κ*t^2*C3*Real.sqrt ((k:ℝ)+1)) := by
      rw [hg_eq]
      have e4 : κ*t^2*(C3*(1:ℝ)^2*Real.sqrt ((k:ℝ)+1)) = κ*t^2*C3*Real.sqrt ((k:ℝ)+1) := by ring
      rw [e4]
      have e1 : t*(mδ δ k) ≤ t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1) + θ) :=
        mul_le_mul_of_nonneg_left hm_le htpos.le
      have e2 : t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1) + θ) =
          t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1)) + t*θ := by ring
      linarith only [e1, e2]
    simp only [hfδ_def]
    calc (C2*M^D*((k:ℝ)+1)^D) *
          Real.exp (t*(mδ δ k) + κ*t^2*(C3*(Blueprint.Draft.gFactor (16^n) δ c0 k)^2*Real.sqrt ((k:ℝ)+1)))
        ≤ (C2*M^D*((k:ℝ)+1)^D) *
            Real.exp (t*θ + (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
              + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (by positivity)
      _ = Real.exp (t*θ) * ((C2*M^D*((k:ℝ)+1)^D) *
            Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
              + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))) := by
          rw [Real.exp_add]; ring
  have hfδ0 : ∀ k, 0 ≤ fδ k := by intro k; simp only [hfδ_def]; positivity
  obtain ⟨hfδsum, hfδSplit⟩ := tsum_le_sum_add_tsum Ne hfδ0 hDtail0 hDtail_sum htail_δ
  have hheadS_le : ∑ k ∈ Finset.range Ne, fδ k ≤
      Real.exp (t*θ) * ∑' k : ℕ, (C2*M^D*((k:ℝ)+1)^D) *
        Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
          + κ*t^2*C3*Real.sqrt ((k:ℝ)+1)) := by
    calc ∑ k ∈ Finset.range Ne, fδ k ≤
          ∑ k ∈ Finset.range Ne, Real.exp (t*θ) * ((C2*M^D*((k:ℝ)+1)^D) *
            Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
              + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))) :=
          Finset.sum_le_sum hfδ_le_headS
      _ = Real.exp (t*θ) * ∑ k ∈ Finset.range Ne, ((C2*M^D*((k:ℝ)+1)^D) *
            Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
              + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (t*θ) * ∑' k : ℕ, (C2*M^D*((k:ℝ)+1)^D) *
            Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
              + κ*t^2*C3*Real.sqrt ((k:ℝ)+1)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact hSsum.sum_le_tsum (Finset.range Ne) (fun i _ => by positivity)
  have hSfin : ∑' k, fδ k ≤ Real.exp (t*θ) *
      (∑' k : ℕ, (C2*M^D*((k:ℝ)+1)^D) *
        Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
          + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))) + 1 :=
    hfδSplit.trans (add_le_add hheadS_le hDtail_le1)
  have hSvalpos : 0 < ∑' k : ℕ, (C2*M^D*((k:ℝ)+1)^D) *
      Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
        + κ*t^2*C3*Real.sqrt ((k:ℝ)+1)) :=
    hSsum.tsum_pos (fun i => by positivity) 0 (by positivity)
  have hSbound_exp : (∑' k : ℕ, (C2*M^D*((k:ℝ)+1)^D) *
      Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
        + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))) ≤ Real.exp (t*(A+CS'*(n:ℝ)^(3/4:ℝ))) := by
    calc (∑' k : ℕ, (C2*M^D*((k:ℝ)+1)^D) *
          Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
            + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))) =
          Real.exp (Real.log (∑' k : ℕ, (C2*M^D*((k:ℝ)+1)^D) *
            Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
              + κ*t^2*C3*Real.sqrt ((k:ℝ)+1)))) := (Real.exp_log hSvalpos).symm
      _ ≤ Real.exp (t*(A+CS'*(n:ℝ)^(3/4:ℝ))) := Real.exp_le_exp.mpr hSbound'
  have hfinal_le : ∑' k, fδ k ≤ Real.exp (t*θ + t*(A+CS'*(n:ℝ)^(3/4:ℝ))) + 1 := by
    calc ∑' k, fδ k ≤ Real.exp (t*θ) *
          (∑' k : ℕ, (C2*M^D*((k:ℝ)+1)^D) *
            Real.exp (t*(min (A+C1) (C1*(n:ℝ)^(3/4:ℝ)*((k:ℝ)+1)^(1/4:ℝ) - k + C1))
              + κ*t^2*C3*Real.sqrt ((k:ℝ)+1))) + 1 := hSfin
      _ ≤ Real.exp (t*θ) * Real.exp (t*(A+CS'*(n:ℝ)^(3/4:ℝ))) + 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hSbound_exp (Real.exp_pos _).le) (le_refl 1)
      _ = Real.exp (t*θ + t*(A+CS'*(n:ℝ)^(3/4:ℝ))) + 1 := by rw [← Real.exp_add]
  have hfδ0pos : 0 < fδ 0 := by simp only [hfδ_def]; positivity
  have hfδsumpos : 0 < ∑' k, fδ k :=
    lt_of_lt_of_le hfδ0pos (hfδsum.le_tsum 0 (fun j _ => hfδ0 j))
  have hExpNonneg : (0:ℝ) ≤ t*θ + t*(A+CS'*(n:ℝ)^(3/4:ℝ)) := by positivity
  have hOneLe : (1:ℝ) ≤ Real.exp (t*θ + t*(A+CS'*(n:ℝ)^(3/4:ℝ))) := Real.one_le_exp hExpNonneg
  have hfinal_le2 : ∑' k, fδ k ≤
      Real.exp (Real.log 2 + (t*θ + t*(A+CS'*(n:ℝ)^(3/4:ℝ)))) := by
    calc ∑' k, fδ k ≤ Real.exp (t*θ+t*(A+CS'*(n:ℝ)^(3/4:ℝ))) + 1 := hfinal_le
      _ ≤ 2 * Real.exp (t*θ+t*(A+CS'*(n:ℝ)^(3/4:ℝ))) := by linarith only [hOneLe]
      _ = Real.exp (Real.log 2) * Real.exp (t*θ+t*(A+CS'*(n:ℝ)^(3/4:ℝ))) := by
          rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
      _ = Real.exp (Real.log 2 + (t*θ+t*(A+CS'*(n:ℝ)^(3/4:ℝ)))) := (Real.exp_add _ _).symm
  have hlogfinal : Real.log (∑' k, fδ k) ≤ Real.log 2 + (t*θ + t*(A+CS'*(n:ℝ)^(3/4:ℝ))) := by
    calc Real.log (∑' k, fδ k) ≤
          Real.log (Real.exp (Real.log 2 + (t*θ + t*(A+CS'*(n:ℝ)^(3/4:ℝ))))) :=
          Real.log_le_log hfδsumpos hfinal_le2
      _ = Real.log 2 + (t*θ + t*(A+CS'*(n:ℝ)^(3/4:ℝ))) := Real.log_exp _
  have hgoal_eq : t * (A + (CS' + Real.log 2 + 1) * (n:ℝ)^(3/4:ℝ) + θ) =
      t*A + t*θ + t*(CS'*(n:ℝ)^(3/4:ℝ)) + t*(Real.log 2*(n:ℝ)^(3/4:ℝ)) + t*(n:ℝ)^(3/4:ℝ) := by
    ring
  have hlog2le : Real.log 2 ≤ t*(Real.log 2*(n:ℝ)^(3/4:ℝ)) := by
    have h1 : Real.log 2 ≤ Real.log 2 * (n:ℝ)^(3/4:ℝ) :=
      le_mul_of_one_le_right (by positivity) hnR34ge1
    have h2 : Real.log 2 * (n:ℝ)^(3/4:ℝ) ≤ t*(Real.log 2*(n:ℝ)^(3/4:ℝ)) :=
      le_mul_of_one_le_left (by positivity) ht1
    linarith only [h1, h2]
  have h1let : (1:ℝ) ≤ t*(n:ℝ)^(3/4:ℝ) := by
    rw [hidentity]; exact hn1
  rw [div_le_iff₀ htpos]
  have hfinal : Real.log (∑' k, fδ k) + 1 ≤
      t * (A + (CS' + Real.log 2 + 1) * (n:ℝ)^(3/4:ℝ) + θ) := by
    rw [hgoal_eq]
    linarith only [hlogfinal, hlog2le, h1let]
  linarith only [hfinal]

end LQGDimension
