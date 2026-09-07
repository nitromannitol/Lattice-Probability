/-
The weight a truncated lazy Green function gives to each simple-walk kernel.

The lazy kernel is the binomial average `Q^r(0,·) = ∑_k 2^{-r} C(r,k) P^k(0,·)`
of `LatticeProb/Walk/GreenIdentity.lean`, so the truncated lazy Green function
`g_R = ∑_{r < R} Q^r(0,·)` is `∑_k A_R(k) P^k(0,·)` with

  `A_R(k) = ∑_{r < R} 2^{-r} C(r,k)`,

a smoothed version of `2` for `k` below `R/2` and of `0` above it.  Two facts
about that profile are what the truncated Green gradient needs: its total mass
`∑_k A_R(k) = R`, which forces the deficit below `R/2` to equal the excess
above it, and the size of the transition window, which is `O(√R)` by a Chernoff
bound.  Both are proved here, together with the exponentially small tail of the
deficit well below `R/2`.
-/
import Mathlib
import LatticeProb.Walk.GreenIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The profile -/

/-- The total weight that the times before `R` give to the `k`-step simple-walk
kernel inside the truncated lazy Green function. -/
noncomputable def Aw (R k : ℕ) : ℝ := ∑ r ∈ Finset.range R, binomWeight k r

theorem Aw_nonneg (R k : ℕ) : 0 ≤ Aw R k :=
  Finset.sum_nonneg fun r _ => binomWeight_nonneg k r

/-- No simple-walk kernel receives more than the total weight `2`. -/
theorem Aw_le_two (R k : ℕ) : Aw R k ≤ 2 :=
  sum_le_hasSum (Finset.range R) (fun r _ => binomWeight_nonneg k r) (hasSum_binomWeight k)

/-- A kernel of order at least the horizon receives nothing. -/
theorem Aw_eq_zero_of_le {R k : ℕ} (h : R ≤ k) : Aw R k = 0 :=
  Finset.sum_eq_zero fun r hr => binomWeight_of_lt (by
    have := Finset.mem_range.mp hr
    omega)

/-- The weights at one time add to one. -/
theorem sum_binomWeight_row {R r : ℕ} (hr : r < R) :
    ∑ k ∈ Finset.range R, binomWeight k r = 1 := by
  have hsub : Finset.range (r + 1) ⊆ Finset.range R :=
    fun k hk => Finset.mem_range.mpr (by
      simp only [Finset.mem_range] at hk
      omega)
  have hext : ∑ k ∈ Finset.range (r + 1), binomWeight k r
      = ∑ k ∈ Finset.range R, binomWeight k r :=
    Finset.sum_subset hsub fun k _ hk =>
      binomWeight_of_lt (by
        simp only [Finset.mem_range, not_lt] at hk
        omega)
  rw [← hext]
  have : ∑ k ∈ Finset.range (r + 1), binomWeight k r
      = (2 : ℝ)⁻¹ ^ r * ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk =>
      binomWeight_of_le (by
        have := Finset.mem_range.mp hk
        omega)
  rw [this]
  have hchoose : ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) = (2 : ℝ) ^ r := by
    have := Nat.sum_range_choose r
    have hcast : ((∑ k ∈ Finset.range (r + 1), r.choose k : ℕ) : ℝ) = ((2 ^ r : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
    push_cast at hcast
    exact hcast
  rw [hchoose, ← mul_pow]
  norm_num

/-- **The total mass of the profile is the horizon.**  This is what forces the
deficit of the profile below the middle to equal its excess above. -/
theorem sum_Aw (R : ℕ) : ∑ k ∈ Finset.range R, Aw R k = (R : ℝ) := by
  unfold Aw
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun r hr => sum_binomWeight_row (Finset.mem_range.mp hr)]
  simp

/-- **The truncated lazy Green function read through the profile.** -/
theorem gR_eq_sum_Aw (R : ℕ) (x : Site d) :
    gR R x = ∑ k ∈ Finset.range R, Aw R k * srwHeat d k x := by
  unfold Aw
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_mul (Finset.range R) (fun r => binomWeight k r)
      (srwHeat d k x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrR : r < R := Finset.mem_range.mp hr
  have hsub : Finset.range (r + 1) ⊆ Finset.range R :=
    fun k hk => Finset.mem_range.mpr (by
      simp only [Finset.mem_range] at hk
      omega)
  have hext : ∑ k ∈ Finset.range (r + 1), binomWeight k r * srwHeat d k x
      = ∑ k ∈ Finset.range R, binomWeight k r * srwHeat d k x :=
    Finset.sum_subset hsub fun k _ hk => by
      rw [binomWeight_of_lt (by
        simp only [Finset.mem_range, not_lt] at hk
        omega), zero_mul]
  rw [← hext, iterate_delta0_eq_binom r x, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k hk => by
    rw [binomWeight_of_le (by
      have := Finset.mem_range.mp hk
      omega)]
    ring

/-! ### Chernoff bounds for the profile -/

/-- The weighted binomial sum over any index set is at most the full one. -/
theorem sum_binom_pow_le (r : ℕ) (s : Finset ℕ) {l : ℝ} (hl : 0 ≤ l) :
    ∑ k ∈ s, (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) * l ^ k ≤ ((1 + l) / 2) ^ r := by
  have hnn : ∀ k : ℕ, 0 ≤ (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) * l ^ k := by
    intro k; positivity
  have h1 : ∑ k ∈ s, (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) * l ^ k
      ≤ ∑ k ∈ s ∪ Finset.range (r + 1), (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) * l ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun k _ _ => hnn k
  have h2 : ∑ k ∈ s ∪ Finset.range (r + 1), (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) * l ^ k
      = ∑ k ∈ Finset.range (r + 1), (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) * l ^ k := by
    refine (Finset.sum_subset Finset.subset_union_right fun k _ hk => ?_).symm
    simp only [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have h3 : ∑ k ∈ Finset.range (r + 1), (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) * l ^ k
      = ((1 + l) / 2) ^ r := by
    have hpow := add_pow l 1 r
    have : ∑ k ∈ Finset.range (r + 1), (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) * l ^ k
        = (2 : ℝ)⁻¹ ^ r * ∑ k ∈ Finset.range (r + 1), l ^ k * 1 ^ (r - k) * (r.choose k : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, ← hpow, ← mul_pow]
    congr 1
    ring
  linarith [h1, h2.le, h2.ge, h3.le, h3.ge]

/-- **The Chernoff bound for the upper tail of the profile at one time.** -/
theorem binom_upper_chernoff (r m : ℕ) (s : Finset ℕ) (hs : ∀ k ∈ s, m ≤ k)
    {l : ℝ} (hl : 1 ≤ l) :
    ∑ k ∈ s, binomWeight k r ≤ ((1 + l) / 2) ^ r / l ^ m := by
  have hl0 : (0 : ℝ) < l := lt_of_lt_of_le zero_lt_one hl
  have hlm : (0 : ℝ) < l ^ m := pow_pos hl0 m
  have hterm : ∀ k ∈ s, binomWeight k r
      ≤ ((2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) * l ^ k) / l ^ m := by
    intro k hk
    have hml : l ^ m ≤ l ^ k := pow_le_pow_right₀ hl (hs k hk)
    rcases Nat.lt_or_ge r k with h | h
    · rw [binomWeight_of_lt h]
      positivity
    · rw [binomWeight_of_le h, le_div_iff₀ hlm]
      have hc : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) := by positivity
      nlinarith [hc, hml, hlm]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (sum_binom_pow_le r s hl0.le) hlm.le

/-- **The Chernoff bound for the lower tail of the profile at one time.** -/
theorem binom_lower_chernoff (r K : ℕ) (s : Finset ℕ) (hs : ∀ k ∈ s, k ≤ K)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    ∑ k ∈ s, binomWeight k r ≤ ((1 + l) / 2) ^ r / l ^ K := by
  have hlm : (0 : ℝ) < l ^ K := pow_pos hl0 K
  have hterm : ∀ k ∈ s, binomWeight k r
      ≤ ((2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) * l ^ k) / l ^ K := by
    intro k hk
    have hml : l ^ K ≤ l ^ k := pow_le_pow_of_le_one hl0.le hl1 (hs k hk)
    rcases Nat.lt_or_ge r k with h | h
    · rw [binomWeight_of_lt h]
      positivity
    · rw [binomWeight_of_le h, le_div_iff₀ hlm]
      have hc : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) := by positivity
      nlinarith [hc, hml, hlm]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (sum_binom_pow_le r s hl0.le) hlm.le

/-! ### The Gaussian shape of the transition window -/

/-- Hoeffding's bound for a single fair step: `(1 + e^t)/2 ≤ exp(t/2 + t²/8)`. -/
theorem half_one_add_exp_le (t : ℝ) : (1 + Real.exp t) / 2 ≤ Real.exp (t / 2 + t ^ 2 / 8) := by
  have h := Real.cosh_le_exp_half_sq (t / 2)
  rw [Real.cosh_eq] at h
  have hpos : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  have e1 : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have e3 : Real.exp (t / 2) * Real.exp ((t / 2) ^ 2 / 2) = Real.exp (t / 2 + t ^ 2 / 8) := by
    rw [← Real.exp_add]; ring_nf
  have hmul := mul_le_mul_of_nonneg_left h hpos.le
  rw [e3] at hmul
  have hlhs : Real.exp (t / 2) * ((Real.exp (t / 2) + Real.exp (-(t / 2))) / 2)
      = (1 + Real.exp t) / 2 := by
    field_simp
    nlinarith [e1, e2]
  linarith [hmul, hlhs.le, hlhs.ge]

/-- The same bound raised to the power of the number of steps. -/
theorem pow_half_one_add_exp_le (t : ℝ) (r : ℕ) :
    ((1 + Real.exp t) / 2) ^ r ≤ Real.exp ((r : ℝ) * (t / 2 + t ^ 2 / 8)) := by
  have hnn : (0 : ℝ) ≤ (1 + Real.exp t) / 2 := by positivity
  calc ((1 + Real.exp t) / 2) ^ r ≤ (Real.exp (t / 2 + t ^ 2 / 8)) ^ r :=
        pow_le_pow_left₀ hnn (half_one_add_exp_le t) r
    _ = Real.exp ((r : ℝ) * (t / 2 + t ^ 2 / 8)) := (Real.exp_nat_mul _ r).symm

/-- **One row of the transition window.**  At a time `r` before `2m` the weights
above `m` add to at most the Gaussian `exp(-(2m-r)²/(4m))`. -/
theorem window_row_le {m r : ℕ} (hm : 1 ≤ m) (hr : r < 2 * m) (s : Finset ℕ)
    (hs : ∀ k ∈ s, m ≤ k) :
    ∑ k ∈ s, binomWeight k r ≤ Real.exp (-((2 * (m : ℝ) - r) ^ 2) / (4 * m)) := by
  set M : ℝ := (m : ℝ) with hM
  set R : ℝ := (r : ℝ) with hR
  have hMpos : (0 : ℝ) < M := by
    have h1 : (1 : ℝ) ≤ M := by rw [hM]; exact_mod_cast hm
    linarith
  have hRlt : R < 2 * M := by
    have : (r : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast hr
    push_cast at this
    linarith
  have hRnn : (0 : ℝ) ≤ R := Nat.cast_nonneg r
  set t : ℝ := (2 * M - R) / M with ht
  have htnn : 0 ≤ t := by
    have : (0 : ℝ) ≤ 2 * M - R := by linarith
    exact div_nonneg this hMpos.le
  have hl : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp htnn
  have hchern := binom_upper_chernoff r m s hs hl
  have hden : Real.exp t ^ m = Real.exp (M * t) := by
    rw [← Real.exp_nat_mul]
  refine le_trans hchern ?_
  rw [hden, div_eq_mul_inv, ← Real.exp_neg]
  have hnum := pow_half_one_add_exp_le t r
  have hmul : ((1 + Real.exp t) / 2) ^ r * Real.exp (-(M * t))
      ≤ Real.exp ((R : ℝ) * (t / 2 + t ^ 2 / 8)) * Real.exp (-(M * t)) :=
    mul_le_mul_of_nonneg_right hnum (Real.exp_pos _).le
  refine le_trans hmul ?_
  rw [← Real.exp_add, Real.exp_le_exp]
  have hJ : (0 : ℝ) ≤ 2 * M - R := by linarith
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hkey : R * (t / 2 + t ^ 2 / 8) + -(M * t) ≤ -((2 * M - R) ^ 2) / (4 * M) := by
    rw [ht, ← sub_nonneg]
    have expand : -((2 * M - R) ^ 2) / (4 * M)
          - (R * (((2 * M - R) / M) / 2 + ((2 * M - R) / M) ^ 2 / 8)
            + -(M * ((2 * M - R) / M)))
        = (2 * M - R) ^ 3 / (8 * M ^ 2) := by
      field_simp
      ring
    rw [expand]
    exact div_nonneg (pow_nonneg hJ 3) (by positivity)
  exact hkey

/-- `exp(1/4) ≤ 4/3`, from `1 - x ≤ exp(-x)`. -/
theorem exp_quarter_le : Real.exp (1 / 4) ≤ 4 / 3 := by
  have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
  have hpos : (0 : ℝ) < Real.exp (1 / 4) := Real.exp_pos _
  have hinv : Real.exp (-(1 / 4 : ℝ)) = (Real.exp (1 / 4))⁻¹ := by
    rw [Real.exp_neg]
  rw [hinv] at h
  have h34 : (3 / 4 : ℝ) ≤ (Real.exp (1 / 4))⁻¹ := by linarith
  have := (le_inv_comm₀ (by norm_num : (0:ℝ) < 3/4) hpos).mp h34
  linarith

/-- **The Gaussian sum.**  The transition window has width `O(√m)`. -/
theorem sum_exp_neg_sq_le (m N : ℕ) (hm : 1 ≤ m) :
    ∑ i ∈ Finset.range N, Real.exp (-(((i : ℝ) + 1) ^ 2) / (4 * m)) ≤ 4 * Real.sqrt m := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  set sm : ℝ := Real.sqrt m with hsmdef
  have hsm1 : (1 : ℝ) ≤ sm := by
    rw [hsmdef]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt m := Real.sqrt_le_sqrt hmR
  have hsmpos : (0 : ℝ) < sm := lt_of_lt_of_le zero_lt_one hsm1
  have hsmsq : sm ^ 2 = (m : ℝ) := Real.sq_sqrt (by linarith)
  set u : ℝ := 1 / (2 * sm) with hudef
  have hupos : (0 : ℝ) < u := by rw [hudef]; positivity
  have husq : u ^ 2 = 1 / (4 * (m : ℝ)) := by
    rw [hudef, div_pow, ← hsmsq]
    ring_nf
  set q : ℝ := Real.exp (-u) with hqdef
  have hq0 : (0 : ℝ) < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hqdef]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have hqle : q ≤ 1 / (1 + u) := by
    have h2 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have h3 : (Real.exp u)⁻¹ ≤ (1 + u)⁻¹ := by
      exact inv_anti₀ h1u h2
    rw [hqdef, Real.exp_neg, one_div]
    exact h3
  have hsub : u / (1 + u) ≤ 1 - q := by
    have hid : 1 - 1 / (1 + u) = u / (1 + u) := by
      field_simp
      ring
    linarith [hqle, hid.ge, hid.le]
  have hsubpos : (0 : ℝ) < 1 - q := by linarith
  have hgeom : ∑ i ∈ Finset.range N, q ^ i ≤ (1 - q)⁻¹ :=
    sum_le_hasSum (Finset.range N) (fun i _ => pow_nonneg hq0.le i)
      (hasSum_geometric_of_lt_one hq0.le hq1)
  have hinvle : (1 - q)⁻¹ ≤ 3 * sm := by
    have hd : (0 : ℝ) < u / (1 + u) := by positivity
    have h1 : (1 - q)⁻¹ ≤ (u / (1 + u))⁻¹ := inv_anti₀ hd hsub
    have h2 : (u / (1 + u))⁻¹ = (1 + u) / u := by
      rw [inv_div]
    have h3 : (1 + u) / u = 2 * sm + 1 := by
      rw [hudef]
      field_simp
    have h4 : (2 : ℝ) * sm + 1 ≤ 3 * sm := by linarith
    linarith [h1, h2.le, h2.ge, h3.le, h3.ge]
  have hterm : ∀ i ∈ Finset.range N,
      Real.exp (-(((i : ℝ) + 1) ^ 2) / (4 * m)) ≤ Real.exp (1 / 4) * q ^ (i + 1) := by
    intro i _
    have hn : (1 : ℝ) ≤ (i : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    have hqpow : q ^ (i + 1) = Real.exp (-(((i : ℝ) + 1) * u)) := by
      rw [hqdef, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hexpo : -(((i : ℝ) + 1) ^ 2) / (4 * m) ≤ 1 / 4 + -(((i : ℝ) + 1) * u) := by
      have hkey : (((i : ℝ) + 1) ^ 2) / (4 * m) = (((i : ℝ) + 1) * u) ^ 2 := by
        rw [mul_pow, husq]
        field_simp
      have hsq : (((i : ℝ) + 1) * u) - 1 / 4 ≤ (((i : ℝ) + 1) * u) ^ 2 := by
        nlinarith [sq_nonneg (((i : ℝ) + 1) * u - 1 / 2)]
      have hneg : -(((i : ℝ) + 1) ^ 2) / (4 * m) = -((((i : ℝ) + 1) ^ 2) / (4 * m)) := by
        ring
      rw [hneg, hkey]
      linarith
    calc Real.exp (-(((i : ℝ) + 1) ^ 2) / (4 * m))
        ≤ Real.exp (1 / 4 + -(((i : ℝ) + 1) * u)) := Real.exp_le_exp.mpr hexpo
      _ = Real.exp (1 / 4) * q ^ (i + 1) := by rw [Real.exp_add, hqpow]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hfac : ∑ i ∈ Finset.range N, Real.exp (1 / 4) * q ^ (i + 1)
      = Real.exp (1 / 4) * q * ∑ i ∈ Finset.range N, q ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
  rw [hfac]
  have hexp4 : Real.exp (1 / 4) ≤ 4 / 3 := exp_quarter_le
  have hpos1 : (0 : ℝ) ≤ Real.exp (1 / 4) * q := by positivity
  have h2 : (0 : ℝ) ≤ (1 - q)⁻¹ := le_of_lt (by positivity)
  have hstep : q * (1 - q)⁻¹ ≤ 3 * sm := by
    calc q * (1 - q)⁻¹ ≤ 1 * (1 - q)⁻¹ := mul_le_mul_of_nonneg_right hq1.le h2
      _ = (1 - q)⁻¹ := one_mul _
      _ ≤ 3 * sm := hinvle
  calc Real.exp (1 / 4) * q * ∑ i ∈ Finset.range N, q ^ i
      ≤ Real.exp (1 / 4) * q * (1 - q)⁻¹ := mul_le_mul_of_nonneg_left hgeom hpos1
    _ = Real.exp (1 / 4) * (q * (1 - q)⁻¹) := by ring
    _ ≤ Real.exp (1 / 4) * (3 * sm) :=
        mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
    _ ≤ 4 / 3 * (3 * sm) := mul_le_mul_of_nonneg_right hexp4 (by positivity)
    _ = 4 * sm := by ring

/-- **The mass of the profile above the middle of the window** is `O(√m)`.
Together with `LatticeProb.sum_Aw` this bounds the whole discrepancy between the
profile at horizon `2m` and the sharp cut-off at `m`. -/
theorem window_mass_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico m (2 * m), Aw (2 * m) k ≤ 4 * Real.sqrt m := by
  have hswap : ∑ k ∈ Finset.Ico m (2 * m), Aw (2 * m) k
      = ∑ r ∈ Finset.range (2 * m), ∑ k ∈ Finset.Ico m (2 * m), binomWeight k r := by
    unfold Aw
    rw [Finset.sum_comm]
  rw [hswap]
  have hrow : ∀ r ∈ Finset.range (2 * m),
      ∑ k ∈ Finset.Ico m (2 * m), binomWeight k r
        ≤ Real.exp (-((2 * (m : ℝ) - r) ^ 2) / (4 * m)) := fun r hr =>
    window_row_le hm (Finset.mem_range.mp hr) _ fun k hk => (Finset.mem_Ico.mp hk).1
  refine le_trans (Finset.sum_le_sum hrow) ?_
  have hrefl := Finset.sum_range_reflect
    (fun r : ℕ => Real.exp (-((2 * (m : ℝ) - r) ^ 2) / (4 * m))) (2 * m)
  rw [← hrefl]
  have hcong : ∀ i ∈ Finset.range (2 * m),
      Real.exp (-((2 * (m : ℝ) - ((2 * m - 1 - i : ℕ) : ℝ)) ^ 2) / (4 * m))
        = Real.exp (-(((i : ℝ) + 1) ^ 2) / (4 * m)) := by
    intro i hi
    have hi' : i < 2 * m := Finset.mem_range.mp hi
    have hcast : ((2 * m - 1 - i : ℕ) : ℝ) = 2 * (m : ℝ) - 1 - (i : ℝ) := by
      have h1 : ((2 * m - 1 - i : ℕ) : ℝ) = ((2 * m : ℕ) : ℝ) - 1 - (i : ℝ) := by
        have hle : i + 1 ≤ 2 * m := by omega
        have : (2 * m - 1 - i : ℕ) + (i + 1) = 2 * m := by omega
        have hcast2 : (((2 * m - 1 - i : ℕ) : ℝ)) + ((i : ℝ) + 1) = ((2 * m : ℕ) : ℝ) := by
          exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
        linarith
      rw [h1]
      push_cast
      ring
    rw [hcast]
    congr 2
    ring
  rw [Finset.sum_congr rfl hcong]
  exact sum_exp_neg_sq_le m (2 * m) hm

/-- **The profile is exponentially close to its full weight far below the middle
of the window.**  This is what keeps the small-time kernels, which the Gaussian
factor does not control, out of the estimate. -/
theorem deficit_tail_le (m : ℕ) :
    ∑ k ∈ Finset.range (m / 2 + 1), (2 - Aw (2 * m) k) ≤ 8 / 3 * (25 / 32 : ℝ) ^ m := by
  set K : ℕ := m / 2 with hK
  have hsummable : ∀ k : ℕ, Summable (binomWeight k) := fun k => (hasSum_binomWeight k).summable
  have hsum_tail : ∀ k : ℕ, Summable fun i : ℕ => binomWeight k (i + 2 * m) := fun k =>
    (summable_nat_add_iff (2 * m)).mpr (hsummable k)
  have htailk : ∀ k : ℕ, 2 - Aw (2 * m) k = ∑' i : ℕ, binomWeight k (i + 2 * m) := by
    intro k
    have h := Summable.sum_add_tsum_nat_add (f := binomWeight k) (2 * m) (hsummable k)
    rw [(hasSum_binomWeight k).tsum_eq] at h
    unfold Aw
    linarith
  have hexch : ∑ k ∈ Finset.range (K + 1), (2 - Aw (2 * m) k)
      = ∑' i : ℕ, ∑ k ∈ Finset.range (K + 1), binomWeight k (i + 2 * m) := by
    rw [Summable.tsum_finsetSum fun k _ => hsum_tail k]
    exact Finset.sum_congr rfl fun k _ => htailk k
  set c : ℝ := ((5 : ℝ) / 8) ^ (2 * m) * (4 : ℝ) ^ K with hc
  have hcnn : (0 : ℝ) ≤ c := by positivity
  have hmaj : ∀ i : ℕ, ∑ k ∈ Finset.range (K + 1), binomWeight k (i + 2 * m)
      ≤ ((5 : ℝ) / 8) ^ i * c := by
    intro i
    have h := binom_lower_chernoff (i + 2 * m) K (Finset.range (K + 1))
      (fun k hk => by
        simp only [Finset.mem_range] at hk
        omega) (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 : ℝ) / 4 ≤ 1)
    refine le_trans h (le_of_eq ?_)
    have h58 : ((1 : ℝ) + 1 / 4) / 2 = 5 / 8 := by norm_num
    have hq : ((1 : ℝ) / 4) ^ K = ((4 : ℝ) ^ K)⁻¹ := by
      rw [one_div, inv_pow]
    rw [h58, hq, div_inv_eq_mul, hc, pow_add]
    ring
  have hgeomsum : Summable fun i : ℕ => ((5 : ℝ) / 8) ^ i * c :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right c
  have hlhs : Summable fun i : ℕ => ∑ k ∈ Finset.range (K + 1), binomWeight k (i + 2 * m) :=
    summable_sum fun k _ => hsum_tail k
  rw [hexch]
  refine le_trans (hlhs.tsum_le_tsum hmaj hgeomsum) ?_
  have h4K : (4 : ℝ) ^ K ≤ (2 : ℝ) ^ m := by
    have h1 : (4 : ℝ) ^ K = (2 : ℝ) ^ (2 * K) := by
      rw [pow_mul]
      norm_num
    rw [h1]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hfin : ((5 : ℝ) / 8) ^ (2 * m) * (4 : ℝ) ^ K ≤ (25 / 32 : ℝ) ^ m := by
    have h1 : ((5 : ℝ) / 8) ^ (2 * m) = (25 / 64 : ℝ) ^ m := by
      rw [pow_mul]
      norm_num
    have h2 : (25 / 32 : ℝ) ^ m = (25 / 64 : ℝ) ^ m * (2 : ℝ) ^ m := by
      rw [← mul_pow]
      norm_num
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left h4K (by positivity)
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  have hinv : ((1 : ℝ) - 5 / 8)⁻¹ = 8 / 3 := by norm_num
  rw [hinv, hc]
  exact mul_le_mul_of_nonneg_left hfin (by norm_num)

/-- **The total discrepancy between the profile at horizon `2m` and the sharp
cut-off at `m`.**  The deficit below `m` and the excess above it are equal,
because the profile carries total mass `2m`, so both are the window mass. -/
theorem sum_abs_profile_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range (2 * m), |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)|
      ≤ 8 * Real.sqrt m := by
  have hmle : m ≤ 2 * m := by omega
  have hsplit : ∑ k ∈ Finset.range (2 * m), |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)|
      = ∑ k ∈ Finset.range m, |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)|
        + ∑ k ∈ Finset.Ico m (2 * m), |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)| := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le m) hmle]
  have hlow : ∑ k ∈ Finset.range m, |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)|
      = ∑ k ∈ Finset.range m, (2 - Aw (2 * m) k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_range.mp hk), abs_of_nonpos (by linarith [Aw_le_two (2 * m) k])]
    ring
  have hhigh : ∑ k ∈ Finset.Ico m (2 * m), |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)|
      = ∑ k ∈ Finset.Ico m (2 * m), Aw (2 * m) k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_neg (by
      have := (Finset.mem_Ico.mp hk).1
      omega), sub_zero, abs_of_nonneg (Aw_nonneg (2 * m) k)]
  have htotal : ∑ k ∈ Finset.range m, Aw (2 * m) k
      + ∑ k ∈ Finset.Ico m (2 * m), Aw (2 * m) k = (2 * m : ℝ) := by
    have h := sum_Aw (2 * m)
    rw [Finset.range_eq_Ico] at h
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le m) hmle]
    push_cast at h ⊢
    linarith
  have hbal : ∑ k ∈ Finset.range m, (2 - Aw (2 * m) k)
      = ∑ k ∈ Finset.Ico m (2 * m), Aw (2 * m) k := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linarith
  rw [hsplit, hlow, hhigh, hbal]
  have hw := window_mass_le m hm
  linarith

end LatticeProb
