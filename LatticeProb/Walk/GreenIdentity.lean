/-
The Green function of the lazy walk is twice the Green function of the simple
walk, in dimension three and above.

`Q = (I + P) / 2` holds with probability `1/2` and otherwise takes one step of
simple random walk, so its `r`-step kernel is the binomial average

  `Q^r(0, ·) = 2^{-r} ∑_{k ≤ r} C(r, k) P^k(0, ·)`,

which is the statement `LatticeProb.iterate_delta0_eq_binom` below.  Summing on
`r` and exchanging the two sums replaces the weight of `P^k(0, ·)` by

  `∑_{r ≥ k} 2^{-r} C(r, k) = 2`,

the value of the geometric-type series `∑_{n} C(n + k, k) x^n = (1-x)^{-(k+1)}`
at `x = 1/2` after the factor `2^{-k}` is restored.  The exchange is legitimate
because every term is nonnegative and, in dimension `d ≥ 3`, both truncated
Green functions are bounded uniformly in the horizon: this is
`LatticeProb.gR_high_dim_le` for the lazy walk and
`LatticeProb.srwGreen_high_dim_le` for the simple walk.  The conclusion,

  `∑_r Q^r(0, x) = 2 ∑_j P^j(0, x)`,

is the expected one: laziness halves the speed of the walk without changing
where it goes, so it doubles the expected number of visits to every site.
-/
import Mathlib
import LatticeProb.Walk.Green
import LatticeProb.Walk.SRWGreenSup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

variable {d : ℕ}

/-! ### One step of the simple walk on a binomial combination of heat kernels -/

/-- The simple-walk operator applied to `2^{-r} ∑_{k ≤ r} C(r,k) P^k(0, ·)`
advances each heat kernel by one step.  Nothing here is special to the binomial
weights: the identity is linearity of `walkOp` over a finite sum together with
`LatticeProb.srwHeat_succ`. -/
theorem walkOp_binom (r : ℕ) (x : Site d) :
    walkOp (fun y => (2 : ℝ)⁻¹ ^ r *
        ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * srwHeat d k y) x
      = (2 : ℝ)⁻¹ ^ r * ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * srwHeat d (k + 1) x := by
  have hterm : ∀ k ∈ Finset.range (r + 1),
      (r.choose k : ℝ) * srwHeat d (k + 1) x
        = (∑ a : Dir d, (r.choose k : ℝ) * srwHeat d k (x + dirVec a)) / (2 * (d : ℝ)) := by
    intro k _
    rw [srwHeat_succ_eq_sum_dir, ← Finset.mul_sum, mul_div_assoc]
  have hswap :
      ∑ a : Dir d, ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * srwHeat d k (x + dirVec a)
        = ∑ k ∈ Finset.range (r + 1), ∑ a : Dir d,
            (r.choose k : ℝ) * srwHeat d k (x + dirVec a) := Finset.sum_comm
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← mul_div_assoc]
  simp only [walkOp_eq_sum_dir]
  rw [← Finset.mul_sum, hswap]

/-! ### Pascal's rule, in the shape the induction needs -/

/-- Pascal's rule summed against the heat kernels: the binomial combination at
level `r + 1` splits into the level-`r` combination and its one-step shift.  The
two boundary indices are the `k = 0` term, which the shifted sum does not carry,
and the `k = r + 1` term, whose coefficient `C(r, r+1)` vanishes. -/
theorem pascal_sum_srwHeat (r : ℕ) (x : Site d) :
    ∑ k ∈ Finset.range (r + 1 + 1), ((r + 1).choose k : ℝ) * srwHeat d k x
      = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * srwHeat d k x
        + ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * srwHeat d (k + 1) x := by
  have h1 : ∑ k ∈ Finset.range (r + 1 + 1), ((r + 1).choose k : ℝ) * srwHeat d k x
      = ∑ k ∈ Finset.range (r + 1), ((r + 1).choose (k + 1) : ℝ) * srwHeat d (k + 1) x
        + ((r + 1).choose 0 : ℝ) * srwHeat d 0 x :=
    Finset.sum_range_succ' (fun k => ((r + 1).choose k : ℝ) * srwHeat d k x) (r + 1)
  have h2 : ∑ k ∈ Finset.range (r + 1), ((r + 1).choose (k + 1) : ℝ) * srwHeat d (k + 1) x
      = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * srwHeat d (k + 1) x
        + ∑ k ∈ Finset.range (r + 1), (r.choose (k + 1) : ℝ) * srwHeat d (k + 1) x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  have h3 : ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * srwHeat d k x
      = ∑ k ∈ Finset.range r, (r.choose (k + 1) : ℝ) * srwHeat d (k + 1) x
        + (r.choose 0 : ℝ) * srwHeat d 0 x :=
    Finset.sum_range_succ' (fun k => (r.choose k : ℝ) * srwHeat d k x) r
  have h4 : ∑ k ∈ Finset.range (r + 1), (r.choose (k + 1) : ℝ) * srwHeat d (k + 1) x
      = ∑ k ∈ Finset.range r, (r.choose (k + 1) : ℝ) * srwHeat d (k + 1) x
        + (r.choose (r + 1) : ℝ) * srwHeat d (r + 1) x :=
    Finset.sum_range_succ (fun k => (r.choose (k + 1) : ℝ) * srwHeat d (k + 1) x) r
  have h5 : (r.choose (r + 1) : ℝ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    norm_num
  have h6 : ((r + 1).choose 0 : ℝ) = 1 := by simp
  have h7 : (r.choose 0 : ℝ) = 1 := by simp
  rw [h5, zero_mul, add_zero] at h4
  rw [h6, one_mul] at h1
  rw [h7, one_mul] at h3
  linarith [h1, h2, h3, h4]

/-! ### The binomial expansion of the lazy kernel -/

/-- **The lazy kernel is a binomial average of the simple-walk kernels.**
`Q^r(0, x) = 2^{-r} ∑_{k ≤ r} C(r,k) P^k(0, x)`, because `Q = (I + P)/2` and `I`
commutes with `P`. -/
theorem iterate_delta0_eq_binom (r : ℕ) (x : Site d) :
    Q^[r] (delta0 : Site d → ℝ) x
      = (2 : ℝ)⁻¹ ^ r * ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * srwHeat d k x := by
  induction r generalizing x with
  | zero => simp [delta0]
  | succ r ih =>
    have hfun : (Q^[r] (delta0 : Site d → ℝ))
        = fun y => (2 : ℝ)⁻¹ ^ r *
            ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * srwHeat d k y := funext ih
    rw [Function.iterate_succ_apply', Q_eq_walkOp]
    simp only [hfun]
    rw [walkOp_binom, pascal_sum_srwHeat]
    ring

/-! ### The weight each simple-walk kernel receives -/

/-- The weight `2^{-r} C(r,k)` that `P^k(0, ·)` carries inside `Q^r(0, ·)`,
extended by zero to the times `r < k` at which it is absent. -/
noncomputable def binomWeight (k r : ℕ) : ℝ :=
  if k ≤ r then (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) else 0

/-- The value of the weight at the times that carry it. -/
theorem binomWeight_of_le {k r : ℕ} (h : k ≤ r) :
    binomWeight k r = (2 : ℝ)⁻¹ ^ r * (r.choose k : ℝ) := if_pos h

/-- The weight vanishes before time `k`. -/
theorem binomWeight_of_lt {k r : ℕ} (h : r < k) : binomWeight k r = 0 :=
  if_neg (by omega)

/-- The weight is nonnegative. -/
theorem binomWeight_nonneg (k r : ℕ) : 0 ≤ binomWeight k r := by
  rcases Nat.lt_or_ge r k with h | h
  · rw [binomWeight_of_lt h]
  · rw [binomWeight_of_le h]
    positivity

/-- **The weight identity.**  The total weight `∑_{r ≥ k} 2^{-r} C(r,k)` that
`P^k(0, ·)` receives is `2`, for every `k`.  After the substitution `r = n + k`
this is the series `∑_n C(n+k, k) x^n = (1-x)^{-(k+1)}` at `x = 1/2`, times the
restored factor `2^{-k}`. -/
theorem hasSum_binomWeight (k : ℕ) : HasSum (binomWeight k) 2 := by
  have hnorm : ‖(2 : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
    norm_num
  have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hval : (2 : ℝ)⁻¹ ^ k * (1 / (1 - (2 : ℝ)⁻¹) ^ (k + 1)) = 2 := by
    rw [show (1 : ℝ) - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ by norm_num]
    simp only [inv_pow, one_div, inv_inv]
    rw [pow_succ, inv_mul_cancel_left₀ h2k]
  have hfe : ∀ n : ℕ, (2 : ℝ)⁻¹ ^ k * (((n + k).choose k : ℝ) * (2 : ℝ)⁻¹ ^ n)
      = binomWeight k (n + k) := by
    intro n
    rw [binomWeight_of_le (Nat.le_add_left k n), pow_add]
    ring
  have h0 := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k hnorm).mul_left ((2 : ℝ)⁻¹ ^ k)
  have key : HasSum (fun n : ℕ => binomWeight k (n + k)) 2 := by
    simpa only [hfe, hval] using h0
  have hzero : ∑ i ∈ Finset.range k, binomWeight k i = 0 :=
    Finset.sum_eq_zero fun i hi => binomWeight_of_lt (Finset.mem_range.mp hi)
  have h5 := (hasSum_nat_add_iff (f := binomWeight k) k).mp key
  rwa [hzero, add_zero] at h5

/-- The weight identity as a `tsum`. -/
theorem tsum_two_pow_choose (k : ℕ) :
    ∑' r : ℕ, (if k ≤ r then ((2 : ℝ)⁻¹) ^ r * (r.choose k : ℝ) else 0) = 2 :=
  (hasSum_binomWeight k).tsum_eq

/-! ### The double family -/

/-- The contribution of `P^k(0, x)` to `Q^r(0, x)`.  Summing on `k` returns the
lazy kernel; summing on `r` returns twice the simple-walk kernel. -/
noncomputable def binomTerm (d : ℕ) (x : Site d) (r k : ℕ) : ℝ :=
  binomWeight k r * srwHeat d k x

/-- Every term of the double family is nonnegative, which is what makes the
exchange of the two sums legitimate. -/
theorem binomTerm_nonneg (x : Site d) (r k : ℕ) : 0 ≤ binomTerm d x r k :=
  mul_nonneg (binomWeight_nonneg k r) (srwHeat_nonneg k x)

/-- The double family vanishes above the diagonal. -/
theorem binomTerm_eq_zero_of_lt (x : Site d) {r k : ℕ} (h : r < k) :
    binomTerm d x r k = 0 := by
  rw [binomTerm, binomWeight_of_lt h, zero_mul]

/-- For a fixed time the family has finite support, so it is summable in `k`. -/
theorem summable_binomTerm_snd (x : Site d) (r : ℕ) :
    Summable fun k => binomTerm d x r k :=
  summable_of_ne_finset_zero (s := Finset.range (r + 1)) fun k hk =>
    binomTerm_eq_zero_of_lt x (by
      have := Finset.mem_range.not.mp hk
      omega)

/-- Summing the double family on `k` returns the lazy kernel: this is the
binomial expansion again, with the finite sum written as a `tsum`. -/
theorem tsum_binomTerm_snd (x : Site d) (r : ℕ) :
    ∑' k : ℕ, binomTerm d x r k = Q^[r] (delta0 : Site d → ℝ) x := by
  rw [tsum_eq_sum (s := Finset.range (r + 1)) fun k hk =>
    binomTerm_eq_zero_of_lt x (by
      have := Finset.mem_range.not.mp hk
      omega)]
  rw [iterate_delta0_eq_binom r x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ r := by
    have := Finset.mem_range.mp hk
    omega
  rw [binomTerm, binomWeight_of_le hk']
  ring

/-- Summing the double family on `r` returns twice the simple-walk kernel: this
is the weight identity. -/
theorem tsum_binomTerm_fst (x : Site d) (k : ℕ) :
    ∑' r : ℕ, binomTerm d x r k = 2 * srwHeat d k x :=
  ((hasSum_binomWeight k).mul_right (srwHeat d k x)).tsum_eq

/-! ### Convergence in dimension three and above -/

/-- The lazy Green function converges in `d ≥ 3`: the partial sums are the
truncated Green functions `g_n`, which are nondecreasing and bounded by
`1 + 3 C_d`. -/
theorem summable_iterate_delta0 (hd : 3 ≤ d) (x : Site d) :
    Summable fun r : ℕ => Q^[r] (delta0 : Site d → ℝ) x := by
  refine summable_of_sum_range_le (c := 1 + 3 * greenConst d)
    (fun r => iterate_delta0_nonneg r x) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.range_zero, Finset.sum_empty]
    linarith [greenConst_nonneg d]
  · have h := gR_high_dim_le hd n hn x
    rwa [gR] at h

/-- The simple-walk Green function converges in `d ≥ 3`, by the same argument
applied to `LatticeProb.srwGreen_high_dim_le`. -/
theorem summable_srwHeat (hd : 3 ≤ d) (x : Site d) :
    Summable fun j : ℕ => srwHeat d j x := by
  refine summable_of_sum_range_le (c := 1 + 3 * (Real.sqrt 2 ^ d * greenConst d))
    (fun j => srwHeat_nonneg j x) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.range_zero, Finset.sum_empty]
    linarith [srwGreenConst_nonneg d]
  · have h := srwGreen_high_dim_le hd n hn x
    rwa [srwGreen] at h

/-- The double family is summable over `ℕ × ℕ`.  All its terms are nonnegative
and the sums of its rows are the lazy kernels, which are summable, so the
criterion of `summable_prod_of_nonneg` applies. -/
theorem summable_binomTerm (hd : 3 ≤ d) (x : Site d) :
    Summable (Function.uncurry (binomTerm d x)) := by
  refine (summable_prod_of_nonneg (f := Function.uncurry (binomTerm d x))
    (fun p => binomTerm_nonneg x p.1 p.2)).mpr ⟨fun r => summable_binomTerm_snd x r, ?_⟩
  exact (summable_iterate_delta0 hd x).congr fun r => (tsum_binomTerm_snd x r).symm

/-! ### The identity -/

/-- **The Green function of the lazy walk is twice the Green function of the
simple walk**, in dimension three and above, where both converge.  Laziness
halves the speed of the walk without changing its trajectory, so it doubles the
expected number of visits to every site. -/
theorem tsum_iterate_delta0_eq (hd : 3 ≤ d) (x : Site d) :
    ∑' r : ℕ, Q^[r] (delta0 : Site d → ℝ) x = 2 * ∑' j : ℕ, srwHeat d j x := by
  have hcomm := (summable_binomTerm hd x).tsum_comm
  calc ∑' r : ℕ, Q^[r] (delta0 : Site d → ℝ) x
      = ∑' r : ℕ, ∑' k : ℕ, binomTerm d x r k :=
        tsum_congr fun r => (tsum_binomTerm_snd x r).symm
    _ = ∑' k : ℕ, ∑' r : ℕ, binomTerm d x r k := hcomm.symm
    _ = ∑' k : ℕ, 2 * srwHeat d k x := tsum_congr fun k => tsum_binomTerm_fst x k
    _ = 2 * ∑' j : ℕ, srwHeat d j x := tsum_mul_left

end LatticeProb
