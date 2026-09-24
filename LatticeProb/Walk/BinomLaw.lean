/-
The fair binomial law on `ℤ` (the number of successes in `l` trials of success
probability `1/2`, extended by zero outside `[0, l]`), its autocorrelation `conv`
with its own translate, and the shift energy identity
`∑_l ∑_j (binomLaw l (j - q) - binomLaw l j)² = 4|q|`.

Write `b_l` for `binomLaw l`, and

    conv l q = ∑_j b_l(j) b_l(j + q).

Expanding the square in the shift energy turns the summand into `2(conv l 0 - conv l q)`.
One step of Pascal's rule, `b_{l+1}(j) = (b_l(j-1) + b_l(j))/2`, makes `conv` satisfy the
lazy random walk recursion

    conv (l+1) q = (conv l (q-1) + 2 conv l q + conv l (q+1))/4,

and `conv 0` is the point mass at `0`. Summing the recursion over `l < L` telescopes, which
turns the partial sums

    S_L(q) = ∑_{l < L} (conv l 0 - conv l q)

into the discrete boundary value problem `S_L(q+1) - 2S_L(q) + S_L(q-1) = 4(1{q=0} - conv L q)`,
whose solution is `S_L(q) = 2q` up to an error controlled by `conv L 0`. That error vanishes
because `conv l 0` is the central binomial coefficient over `4^l`, and `(l+1)(conv l 0)^2` is
nonincreasing, so `conv l 0 ≤ (l+1)^{-1/2}`. The limit is therefore `2|q|`, and the shift
energy is twice it.

This object is distinct from `LatticeProb.Walk.binomPMF` of `LatticeProb/Walk/BinomialLocalCLT.lean`,
which indexes the same fair binomial pmf by the simple-random-walk position (`binomPMF m j =
C(m, (m+j)/2)/2^m`, requiring `j` and `m` to share parity) rather than the number of successes;
that module builds the local-CLT Gaussian approximation, not this shift-correlation identity.

Moved from Parking-Sharpness (`Parking.binomLaw` of `Parking/Support/Oriented.lean`, and
`Parking.conv` together with the shift-energy identity of `Parking/Support/Shift.lean`).
-/
import Mathlib

noncomputable section

open scoped BigOperators
open Filter Topology Finset

namespace LatticeProb.Walk

/-! ### The binomial law -/

/-- The fair binomial law on `ℤ`: the probability of `j` successes in `l` trials of success
probability `1/2`, extended by zero for `j < 0`. -/
def binomLaw (l : ℕ) (j : ℤ) : ℝ :=
  (if 0 ≤ j then (Nat.choose l j.toNat : ℝ) else 0) / 2 ^ l

/-- The binomial law vanishes below zero. -/
theorem binomLaw_of_neg (l : ℕ) {j : ℤ} (hj : j < 0) : binomLaw l j = 0 := by
  simp [binomLaw, not_le.mpr hj]

/-- The binomial law is nonnegative. -/
theorem binomLaw_nonneg (l : ℕ) (j : ℤ) : 0 ≤ binomLaw l j := by
  unfold binomLaw
  positivity

/-- The binomial law vanishes above the number of trials. -/
theorem binomLaw_of_gt (l : ℕ) {j : ℤ} (hj : (l : ℤ) < j) : binomLaw l j = 0 := by
  rcases lt_or_ge j 0 with h | h
  · exact binomLaw_of_neg l h
  · have : l < j.toNat := by omega
    simp [binomLaw, h, Nat.choose_eq_zero_of_lt this]

/-- With zero trials, the binomial law is the point mass at `0`. -/
theorem binomLaw_zero (j : ℤ) : binomLaw 0 j = if j = 0 then 1 else 0 := by
  rcases lt_or_ge j 0 with h | h
  · rw [binomLaw_of_neg 0 h, if_neg (by omega)]
  · rcases eq_or_lt_of_le h with h0 | h0
    · simp [binomLaw, ← h0]
    · rw [binomLaw_of_gt 0 (by exact_mod_cast h0), if_neg (by omega)]

/-- Pascal's rule for the binomial law: `b_{l+1}(j) = (b_l(j-1) + b_l(j))/2`. -/
theorem binomLaw_succ (n : ℕ) (j : ℤ) :
    binomLaw (n + 1) j = (binomLaw n (j - 1) + binomLaw n j) / 2 := by
  rcases lt_or_ge j 0 with h | h
  · rw [binomLaw_of_neg _ h, binomLaw_of_neg _ h, binomLaw_of_neg _ (by omega : j - 1 < 0)]
    norm_num
  · rcases eq_or_lt_of_le h with h0 | h0
    · rw [← h0, binomLaw_of_neg n (by omega : (0 : ℤ) - 1 < 0)]
      simp [binomLaw, pow_succ]
      ring
    · have hj : j.toNat = (j - 1).toNat + 1 := by omega
      have h1 : (0 : ℤ) ≤ j - 1 := by omega
      simp only [binomLaw, if_pos h, if_pos h1, hj, Nat.choose_succ_succ']
      rw [pow_succ]
      push_cast
      ring

/-- The binomial law is symmetric about half the number of trials. -/
theorem binomLaw_symm (n : ℕ) (j : ℤ) : binomLaw n ((n : ℤ) - j) = binomLaw n j := by
  rcases lt_or_ge j 0 with h | h
  · rw [binomLaw_of_neg n h, binomLaw_of_gt n (by omega)]
  · rcases lt_or_ge (n : ℤ) j with h' | h'
    · rw [binomLaw_of_gt n h', binomLaw_of_neg n (by omega)]
    · have h1 : ((n : ℤ) - j).toNat = n - j.toNat := by omega
      have h2 : j.toNat ≤ n := by omega
      simp only [binomLaw, if_pos h, if_pos (by omega : (0 : ℤ) ≤ (n : ℤ) - j), h1]
      rw [Nat.choose_symm h2]

/-! ### The convolution of the binomial law with its translate -/

/-- The product of two translates of the binomial law is finitely supported. -/
theorem summable_binom_prod (l : ℕ) (a b : ℤ) :
    Summable fun j : ℤ => binomLaw l (j + a) * binomLaw l (j + b) := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (-a) ((l : ℤ) - a)) fun j hj => ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at hj
  rcases hj with hj | hj
  · rw [binomLaw_of_neg l (by omega), zero_mul]
  · rw [binomLaw_of_gt l (by omega), zero_mul]

/-- `conv l q = ∑_j b_l(j) b_l(j+q)`, the correlation of the binomial law with
its translate. -/
def conv (l : ℕ) (q : ℤ) : ℝ := ∑' j : ℤ, binomLaw l j * binomLaw l (j + q)

/-- The correlation series is summable. -/
theorem summable_conv (l : ℕ) (q : ℤ) :
    Summable fun j : ℤ => binomLaw l j * binomLaw l (j + q) := by
  have := summable_binom_prod l 0 q
  simpa using this

/-- The correlation is nonnegative. -/
theorem conv_nonneg (l : ℕ) (q : ℤ) : 0 ≤ conv l q :=
  tsum_nonneg fun j => mul_nonneg (binomLaw_nonneg l j) (binomLaw_nonneg l (j + q))

/-- The correlation is even. -/
theorem conv_neg (l : ℕ) (q : ℤ) : conv l (-q) = conv l q := by
  have h := (Equiv.addRight q).tsum_eq (fun j : ℤ => binomLaw l j * binomLaw l (j + -q))
  simp only [Equiv.coe_addRight] at h
  rw [conv, ← h, conv]
  refine tsum_congr fun j => ?_
  rw [show j + q + -q = j by ring]
  exact mul_comm _ _

/-- With zero trials, the correlation is the point mass at `0`. -/
theorem conv_zero_index (q : ℤ) : conv 0 q = if q = 0 then 1 else 0 := by
  rw [conv]
  have h : ∀ j : ℤ, binomLaw 0 j * binomLaw 0 (j + q)
      = if j = 0 then (if q = 0 then 1 else 0) else 0 := by
    intro j
    rw [binomLaw_zero, binomLaw_zero]
    by_cases hj : j = 0
    · simp [hj]
    · simp [hj]
  rw [tsum_congr h, tsum_ite_eq]

/-! ### The lazy random walk recursion -/

/-- The correlation satisfies the lazy random walk recursion in the trial count. -/
theorem conv_succ (l : ℕ) (q : ℤ) :
    conv (l + 1) q = (conv l (q - 1) + 2 * conv l q + conv l (q + 1)) / 4 := by
  have hexp : ∀ j : ℤ, binomLaw (l + 1) j * binomLaw (l + 1) (j + q)
      = (binomLaw l (j - 1) * binomLaw l (j + q - 1)
        + binomLaw l (j - 1) * binomLaw l (j + q)
        + binomLaw l j * binomLaw l (j + q - 1)
        + binomLaw l j * binomLaw l (j + q)) / 4 := by
    intro j
    rw [binomLaw_succ l j, binomLaw_succ l (j + q)]
    ring
  have hs1 : Summable fun j : ℤ => binomLaw l (j - 1) * binomLaw l (j + q - 1) := by
    have := summable_binom_prod l (-1) (q - 1)
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
  have hs2 : Summable fun j : ℤ => binomLaw l (j - 1) * binomLaw l (j + q) := by
    have := summable_binom_prod l (-1) q
    simpa [sub_eq_add_neg] using this
  have hs3 : Summable fun j : ℤ => binomLaw l j * binomLaw l (j + q - 1) := by
    have := summable_binom_prod l 0 (q - 1)
    simpa [sub_eq_add_neg, add_assoc] using this
  have hs4 : Summable fun j : ℤ => binomLaw l j * binomLaw l (j + q) := summable_conv l q
  have e1 : ∑' j : ℤ, binomLaw l (j - 1) * binomLaw l (j + q - 1) = conv l q := by
    have h := (Equiv.addRight (1 : ℤ)).tsum_eq
      (fun j : ℤ => binomLaw l (j - 1) * binomLaw l (j + q - 1))
    simp only [Equiv.coe_addRight] at h
    rw [← h, conv]
    exact tsum_congr fun j => by rw [show j + 1 - 1 = j by ring, show j + 1 + q - 1 = j + q by ring]
  have e2 : ∑' j : ℤ, binomLaw l (j - 1) * binomLaw l (j + q) = conv l (q + 1) := by
    have h := (Equiv.addRight (1 : ℤ)).tsum_eq
      (fun j : ℤ => binomLaw l (j - 1) * binomLaw l (j + q))
    simp only [Equiv.coe_addRight] at h
    rw [← h, conv]
    exact tsum_congr fun j => by
      rw [show j + 1 - 1 = j by ring, show j + 1 + q = j + (q + 1) by ring]
  have e3 : ∑' j : ℤ, binomLaw l j * binomLaw l (j + q - 1) = conv l (q - 1) := by
    rw [conv]
    exact tsum_congr fun j => by rw [show j + q - 1 = j + (q - 1) by ring]
  rw [conv, tsum_congr hexp, tsum_div_const,
    Summable.tsum_add ((hs1.add hs2).add hs3) hs4, Summable.tsum_add (hs1.add hs2) hs3,
    Summable.tsum_add hs1 hs2,
    e1, e2, e3, ← conv]
  ring

/-! ### The correlation at zero is the central binomial coefficient -/

/-- The correlation at zero shift is the central binomial coefficient over `4^l`. -/
theorem conv_zero_eq (l : ℕ) : conv l 0 = (Nat.centralBinom l : ℝ) / 4 ^ l := by
  have hsupp : ∀ j : ℤ, j ∉ Finset.Icc (0 : ℤ) (l : ℤ) →
      binomLaw l j * binomLaw l (j + 0) = 0 := by
    intro j hj
    simp only [Finset.mem_Icc, not_and_or, not_le] at hj
    rcases hj with hj | hj
    · rw [binomLaw_of_neg l hj, zero_mul]
    · rw [binomLaw_of_gt l hj, zero_mul]
  rw [conv, tsum_eq_sum hsupp]
  have hmap : ∑ j ∈ Finset.Icc (0 : ℤ) (l : ℤ), binomLaw l j * binomLaw l (j + 0)
      = ∑ i ∈ Finset.range (l + 1), ((Nat.choose l i : ℝ) / 2 ^ l) ^ 2 := by
    rw [show Finset.Icc (0 : ℤ) (l : ℤ)
        = (Finset.range (l + 1)).map ⟨fun i : ℕ => (i : ℤ), fun a b h => by simpa using h⟩ by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨j.toNat, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        omega]
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.Embedding.coeFn_mk, add_zero, binomLaw,
      if_pos (Int.natCast_nonneg i), Int.toNat_natCast]
    ring
  rw [hmap]
  have h4 : (4 : ℝ) ^ l = (2 ^ l) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have key : ∑ i ∈ Finset.range (l + 1), ((Nat.choose l i : ℝ) / 2 ^ l) ^ 2
      = ((∑ i ∈ Finset.range (l + 1), Nat.choose l i ^ 2 : ℕ) : ℝ) / 4 ^ l := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow, h4]
    push_cast
    ring
  rw [key, Nat.sum_range_choose_sq, Nat.centralBinom]

/-! ### The correlation is largest at the origin -/

/-- The correlation of the binomial law with a fixed shift, summed as a shifted square. -/
theorem tsum_sq_shift (l : ℕ) (q : ℤ) :
    ∑' j : ℤ, binomLaw l (j + q) * binomLaw l (j + q) = conv l 0 := by
  have h := (Equiv.addRight q).tsum_eq (fun j : ℤ => binomLaw l j * binomLaw l j)
  simp only [Equiv.coe_addRight] at h
  rw [h, conv]
  exact (tsum_congr fun j => by rw [add_zero]).symm

/-- The shifted square of the binomial law is summable. -/
theorem summable_sq (l : ℕ) (q : ℤ) :
    Summable fun j : ℤ => binomLaw l (j + q) * binomLaw l (j + q) := summable_binom_prod l q q

/-- The correlation is maximized at zero shift. -/
theorem conv_le (l : ℕ) (q : ℤ) : conv l q ≤ conv l 0 := by
  have hs1 : Summable fun j : ℤ => binomLaw l (j + 0) * binomLaw l (j + 0) := summable_sq l 0
  have hs2 : Summable fun j : ℤ => binomLaw l (j + q) * binomLaw l (j + q) := summable_sq l q
  have hbound : ∀ j : ℤ, binomLaw l j * binomLaw l (j + q)
      ≤ (binomLaw l (j + 0) * binomLaw l (j + 0)
        + binomLaw l (j + q) * binomLaw l (j + q)) / 2 := by
    intro j
    rw [add_zero]
    nlinarith [sq_nonneg (binomLaw l j - binomLaw l (j + q))]
  have hle : conv l q ≤ ∑' j : ℤ, (binomLaw l (j + 0) * binomLaw l (j + 0)
      + binomLaw l (j + q) * binomLaw l (j + q)) / 2 :=
    Summable.tsum_le_tsum hbound (summable_conv l q) ((hs1.add hs2).div_const 2)
  refine hle.trans (le_of_eq ?_)
  rw [tsum_div_const, Summable.tsum_add hs1 hs2, tsum_sq_shift l 0, tsum_sq_shift l q]
  ring

/-! ### The correlation at the origin vanishes -/

/-- A recursion for the correlation at zero shift, from the central-binomial recursion. -/
theorem conv_zero_succ (l : ℕ) :
    2 * ((l : ℝ) + 1) * conv (l + 1) 0 = (2 * (l : ℝ) + 1) * conv l 0 := by
  have h : ((l : ℝ) + 1) * (Nat.centralBinom (l + 1) : ℝ)
      = 2 * (2 * (l : ℝ) + 1) * (Nat.centralBinom l : ℝ) := by
    have := Nat.succ_mul_centralBinom_succ l
    have := congrArg (fun n : ℕ => (n : ℝ)) this
    push_cast at this
    linarith [this]
  rw [conv_zero_eq, conv_zero_eq, pow_succ]
  have h4 : (0 : ℝ) < 4 ^ l := by positivity
  field_simp
  nlinarith [h, h4]

/-- `(l+1) · conv l 0 ^ 2 ≤ 1`, so `conv l 0` decays at rate `l^{-1/2}`. -/
theorem conv_zero_sq_le (l : ℕ) : ((l : ℝ) + 1) * conv l 0 ^ 2 ≤ 1 := by
  induction l with
  | zero => simp [conv_zero_index]
  | succ l ih =>
      have hstep := conv_zero_succ l
      have hnn : 0 ≤ conv l 0 := conv_nonneg l 0
      have hnn' : 0 ≤ conv (l + 1) 0 := conv_nonneg (l + 1) 0
      have hL : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
      have hsq : (2 * ((l : ℝ) + 1)) ^ 2 * conv (l + 1) 0 ^ 2
          = (2 * (l : ℝ) + 1) ^ 2 * conv l 0 ^ 2 := by
        have := congrArg (fun x : ℝ => x ^ 2) hstep
        simpa [mul_pow] using this
      have hpoly : ((l : ℝ) + 2) * (2 * (l : ℝ) + 1) ^ 2 ≤ 4 * ((l : ℝ) + 1) ^ 3 := by
        nlinarith [hL]
      have hpos : (0 : ℝ) < 4 * ((l : ℝ) + 1) ^ 2 := by positivity
      have hkey : (((l : ℝ) + 1) + 1) * conv (l + 1) 0 ^ 2 ≤ ((l : ℝ) + 1) * conv l 0 ^ 2 := by
        refine le_of_mul_le_mul_right ?_ hpos
        calc (((l : ℝ) + 1) + 1) * conv (l + 1) 0 ^ 2 * (4 * ((l : ℝ) + 1) ^ 2)
            = ((l : ℝ) + 2) * ((2 * (l : ℝ) + 1) ^ 2 * conv l 0 ^ 2) := by
              rw [← hsq]; ring
          _ ≤ (4 * ((l : ℝ) + 1) ^ 3) * conv l 0 ^ 2 := by
              nlinarith [hpoly, sq_nonneg (conv l 0)]
          _ = ((l : ℝ) + 1) * conv l 0 ^ 2 * (4 * ((l : ℝ) + 1) ^ 2) := by ring
      push_cast
      linarith [hkey, ih]

/-- The correlation at zero shift is at most `1`. -/
theorem conv_zero_le_one (l : ℕ) : conv l 0 ≤ 1 := by
  have h := conv_zero_sq_le l
  have hnn : 0 ≤ conv l 0 := conv_nonneg l 0
  nlinarith [Nat.cast_nonneg (α := ℝ) l]

/-- The correlation at zero shift tends to zero as the number of trials grows. -/
theorem conv_zero_tendsto : Tendsto (fun l : ℕ => conv l 0) atTop (𝓝 0) := by
  have hsq : Tendsto (fun l : ℕ => conv l 0 ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun l => sq_nonneg _) (fun l => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have h := conv_zero_sq_le l
    have hpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hpos]
    linarith [h]
  have hrw : (fun l : ℕ => conv l 0) = fun l : ℕ => Real.sqrt (conv l 0 ^ 2) := by
    funext l
    rw [Real.sqrt_sq (conv_nonneg l 0)]
  rw [hrw]
  have h2 := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  rw [Real.sqrt_zero] at h2
  exact h2

/-! ### The partial sums -/

/-- `∑_{l < L} conv l q`. -/
def sumConv (L : ℕ) (q : ℤ) : ℝ := ∑ l ∈ Finset.range L, conv l q

/-- `S_L(q) = ∑_{l < L} (conv l 0 - conv l q)`. -/
def shiftPartial (L : ℕ) (q : ℤ) : ℝ := ∑ l ∈ Finset.range L, (conv l 0 - conv l q)

/-- The partial sums of the shift difference unfold to a difference of `sumConv`. -/
theorem shiftPartial_eq (L : ℕ) (q : ℤ) : shiftPartial L q = sumConv L 0 - sumConv L q := by
  rw [shiftPartial, sumConv, sumConv, Finset.sum_sub_distrib]

/-- The partial sum at zero shift vanishes. -/
theorem shiftPartial_zero (L : ℕ) : shiftPartial L 0 = 0 := by
  simp [shiftPartial]

/-- The partial sum is even in the shift. -/
theorem shiftPartial_neg (L : ℕ) (q : ℤ) : shiftPartial L (-q) = shiftPartial L q := by
  simp only [shiftPartial, conv_neg]

/-- The finite partial sums of the correlation satisfy the discrete boundary value problem. -/
theorem sumConv_recursion (L : ℕ) (q : ℤ) :
    2 * sumConv L q - sumConv L (q - 1) - sumConv L (q + 1)
      = 4 * ((if q = 0 then 1 else 0) - conv L q) := by
  have hterm : ∀ l : ℕ, conv l q - conv (l + 1) q
      = (2 * conv l q - conv l (q - 1) - conv l (q + 1)) / 4 := by
    intro l
    rw [conv_succ]
    ring
  have h := Finset.sum_range_sub' (fun l => conv l q) L
  rw [Finset.sum_congr rfl fun l _ => hterm l] at h
  rw [← Finset.sum_div, conv_zero_index] at h
  simp only [sumConv]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at *
  linarith [h]

/-- The recursion for `shiftPartial`, in the shift `q`. -/
theorem shiftPartial_recursion (L : ℕ) (q : ℤ) :
    shiftPartial L (q + 1) = 2 * shiftPartial L q - shiftPartial L (q - 1)
      + 4 * (if q = 0 then 1 else 0) - 4 * conv L q := by
  have h := sumConv_recursion L q
  rw [shiftPartial_eq, shiftPartial_eq, shiftPartial_eq]
  linarith [h]

/-- The partial sum at shift `1`, in closed form up to the correlation at zero. -/
theorem shiftPartial_one (L : ℕ) : shiftPartial L 1 = 2 - 2 * conv L 0 := by
  have h := shiftPartial_recursion L 0
  rw [show (0 : ℤ) + 1 = 1 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num,
    shiftPartial_zero, shiftPartial_neg, if_pos rfl] at h
  linarith [h]

/-- The partial sums of the shift energy solve the discrete boundary value
problem up to an error controlled by `conv L 0`. -/
theorem shiftPartial_bound (L : ℕ) : ∀ n : ℕ,
    |shiftPartial L (n : ℤ) - 2 * (n : ℝ)| ≤ 2 * (n : ℝ) ^ 2 * conv L 0 ∧
      |(shiftPartial L ((n : ℤ) + 1) - shiftPartial L (n : ℤ)) - 2|
        ≤ (2 + 4 * (n : ℝ)) * conv L 0 := by
  intro n
  induction n with
  | zero =>
      refine ⟨by simp [shiftPartial_zero], ?_⟩
      rw [show ((0 : ℕ) : ℤ) + 1 = 1 by norm_num, show ((0 : ℕ) : ℤ) = 0 by norm_num,
        shiftPartial_zero, shiftPartial_one]
      have : |(2 - 2 * conv L 0 - 0) - 2| = 2 * conv L 0 := by
        rw [show (2 - 2 * conv L 0 - 0) - 2 = -(2 * conv L 0) by ring, abs_neg,
          abs_of_nonneg (by linarith [conv_nonneg L 0] : (0 : ℝ) ≤ 2 * conv L 0)]
      rw [this]
      simp
  | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hc0 : 0 ≤ conv L 0 := conv_nonneg L 0
      have hcn : 0 ≤ conv L ((n : ℤ) + 1) := conv_nonneg L _
      have hcn' : conv L ((n : ℤ) + 1) ≤ conv L 0 := conv_le L _
      have hcast : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 := by push_cast; ring
      constructor
      · rw [hcast]
        have := abs_add_le ((shiftPartial L (n : ℤ) - 2 * (n : ℝ)))
          ((shiftPartial L ((n : ℤ) + 1) - shiftPartial L (n : ℤ)) - 2)
        have hsum : (shiftPartial L (n : ℤ) - 2 * (n : ℝ))
            + ((shiftPartial L ((n : ℤ) + 1) - shiftPartial L (n : ℤ)) - 2)
            = shiftPartial L ((n : ℤ) + 1) - 2 * ((n : ℝ) + 1) := by ring
        rw [hsum] at this
        push_cast
        nlinarith [this, ih1, ih2, hc0]
      · have hrec := shiftPartial_recursion L ((n : ℤ) + 1)
        rw [show ((n : ℤ) + 1) - 1 = (n : ℤ) by ring, if_neg (by omega)] at hrec
        have hnext : (shiftPartial L ((n : ℤ) + 1 + 1) - shiftPartial L ((n : ℤ) + 1)) - 2
            = ((shiftPartial L ((n : ℤ) + 1) - shiftPartial L (n : ℤ)) - 2)
              - 4 * conv L ((n : ℤ) + 1) := by
          rw [hrec]; ring
        rw [hcast, show (n : ℤ) + 1 + 1 = ((n : ℤ) + 1) + 1 by ring, hnext]
        have habs : |4 * conv L ((n : ℤ) + 1)| = 4 * conv L ((n : ℤ) + 1) :=
          abs_of_nonneg (by linarith [hcn])
        push_cast
        calc |((shiftPartial L ((n : ℤ) + 1) - shiftPartial L (n : ℤ)) - 2)
              - 4 * conv L ((n : ℤ) + 1)|
            ≤ |(shiftPartial L ((n : ℤ) + 1) - shiftPartial L (n : ℤ)) - 2|
              + |4 * conv L ((n : ℤ) + 1)| := by
                have h := abs_add_le ((shiftPartial L ((n : ℤ) + 1) - shiftPartial L (n : ℤ)) - 2)
                  (-(4 * conv L ((n : ℤ) + 1)))
                rwa [← sub_eq_add_neg, abs_neg] at h
          _ ≤ (2 + 4 * (n : ℝ)) * conv L 0 + 4 * conv L 0 := by
              rw [habs]; nlinarith [ih2, hcn']
          _ = (2 + 4 * ((n : ℝ) + 1)) * conv L 0 := by ring

/-! ### The limit of the partial sums -/

/-- The correlation gap at zero shift is nonnegative. -/
theorem conv_diff_nonneg (l : ℕ) (q : ℤ) : 0 ≤ conv l 0 - conv l q := by
  linarith [conv_le l q]

/-- The partial sum is bounded by a quadratic in the shift. -/
theorem shiftPartial_le (L n : ℕ) :
    shiftPartial L (n : ℤ) ≤ 2 * (n : ℝ) + 2 * (n : ℝ) ^ 2 := by
  have h := abs_le.mp (shiftPartial_bound L n).1
  have hc := conv_zero_le_one L
  have hc0 := conv_nonneg L 0
  nlinarith [h.2, sq_nonneg ((n : ℝ))]

/-- The correlation-gap series is summable. -/
theorem summable_shiftSeries (n : ℕ) : Summable fun l : ℕ => conv l 0 - conv l (n : ℤ) :=
  summable_of_sum_range_le (fun l => conv_diff_nonneg l _) fun L => shiftPartial_le L n

/-- The correlation-gap series sums to `2|n|` (stated for a natural `n`). -/
theorem tsum_shiftSeries (n : ℕ) :
    ∑' l : ℕ, (conv l 0 - conv l (n : ℤ)) = 2 * (n : ℝ) := by
  have h1 := (summable_shiftSeries n).hasSum.tendsto_sum_nat
  have hz : Tendsto (fun L : ℕ => 2 * (n : ℝ) ^ 2 * conv L 0) atTop (𝓝 0) := by
    have := conv_zero_tendsto.const_mul (2 * (n : ℝ) ^ 2)
    simpa using this
  have hsq := squeeze_zero_norm
    (f := fun L : ℕ => shiftPartial L (n : ℤ) - 2 * (n : ℝ))
    (fun L => by rw [Real.norm_eq_abs]; exact (shiftPartial_bound L n).1) hz
  have h2 : Tendsto (fun L => shiftPartial L (n : ℤ)) atTop (𝓝 (2 * (n : ℝ))) := by
    have := hsq.add_const (2 * (n : ℝ))
    simpa using this
  exact tendsto_nhds_unique h1 h2

/-! ### The shift energy of one layer -/

/-- The squared difference between two translates of the binomial law is summable. -/
theorem summable_sq_diff (l : ℕ) (q : ℤ) :
    Summable fun j : ℤ => (binomLaw l (j - q) - binomLaw l j) ^ 2 := by
  refine summable_of_ne_finset_zero
    (s := Finset.Icc (min 0 q) (max (l : ℤ) ((l : ℤ) + q))) fun j hj => ?_
  simp only [Finset.mem_Icc, not_and_or, not_le, lt_min_iff, max_lt_iff] at hj
  rcases hj with hj | hj
  · rw [binomLaw_of_neg l (by omega), binomLaw_of_neg l (by omega)]
    ring
  · rw [binomLaw_of_gt l (by omega), binomLaw_of_gt l (by omega)]
    ring

/-- The sum over `j` of the squared difference between two translates of the binomial law is
`2` times the correlation gap. -/
theorem tsum_sq_diff (l : ℕ) (q : ℤ) :
    ∑' j : ℤ, (binomLaw l (j - q) - binomLaw l j) ^ 2 = 2 * (conv l 0 - conv l q) := by
  have s1 : Summable fun j : ℤ => binomLaw l (j - q) * binomLaw l (j - q) := by
    have := summable_binom_prod l (-q) (-q)
    simpa [sub_eq_add_neg] using this
  have s2 : Summable fun j : ℤ => binomLaw l (j - q) * binomLaw l j := by
    have := summable_binom_prod l (-q) 0
    simpa [sub_eq_add_neg] using this
  have s3 : Summable fun j : ℤ => binomLaw l j * binomLaw l j := by
    have := summable_binom_prod l 0 0
    simpa using this
  have e1 : ∑' j : ℤ, binomLaw l (j - q) * binomLaw l (j - q) = conv l 0 := by
    have := tsum_sq_shift l (-q)
    simpa [sub_eq_add_neg] using this
  have e2 : ∑' j : ℤ, binomLaw l (j - q) * binomLaw l j = conv l q := by
    have h := (Equiv.addRight q).tsum_eq (fun j : ℤ => binomLaw l (j - q) * binomLaw l j)
    simp only [Equiv.coe_addRight] at h
    rw [← h, conv]
    exact tsum_congr fun j => by rw [show j + q - q = j by ring]
  have e3 : ∑' j : ℤ, binomLaw l j * binomLaw l j = conv l 0 := by
    have := tsum_sq_shift l 0
    simpa using this
  have hcong : ∀ j : ℤ, (binomLaw l (j - q) - binomLaw l j) ^ 2
      = binomLaw l (j - q) * binomLaw l (j - q) + binomLaw l j * binomLaw l j
        - 2 * (binomLaw l (j - q) * binomLaw l j) := by
    intro j; ring
  rw [tsum_congr hcong, Summable.tsum_sub (s1.add s3) (s2.mul_left 2),
    Summable.tsum_add s1 s3, tsum_mul_left, e1, e2, e3]
  ring

/-- The correlation depends on the shift only through its absolute value. -/
theorem conv_natAbs (l : ℕ) (q : ℤ) : conv l q = conv l (q.natAbs : ℤ) := by
  rcases le_or_gt 0 q with h | h
  · rw [Int.natAbs_of_nonneg h]
  · rw [show ((q.natAbs : ℤ)) = -q by omega, conv_neg]

/-- **The shift energy of the binomial layer laws**: for every integer shift `q`, the
squared difference between the binomial law and its `q`-translate, summed over both the
lattice point `j` and the number of trials `l`, equals `4|q|`. -/
theorem shift_energy (q : ℤ) :
    (∀ l : ℕ, Summable fun j : ℤ => (binomLaw l (j - q) - binomLaw l j) ^ 2) ∧
      Summable (fun l : ℕ => ∑' j : ℤ, (binomLaw l (j - q) - binomLaw l j) ^ 2) ∧
      ∑' l : ℕ, ∑' j : ℤ, (binomLaw l (j - q) - binomLaw l j) ^ 2 = 4 * |(q : ℝ)| := by
  set n : ℕ := q.natAbs with hn
  have hcast : |(q : ℝ)| = (n : ℝ) := by
    have h1 : (((q.natAbs : ℤ)) : ℝ) = |((q : ℤ) : ℝ)| := by
      rw [Int.natCast_natAbs, Int.cast_abs]
    rw [hn, ← h1]
    exact Int.cast_natCast _
  have hterm : ∀ l : ℕ, (∑' j : ℤ, (binomLaw l (j - q) - binomLaw l j) ^ 2)
      = 2 * (conv l 0 - conv l (n : ℤ)) := by
    intro l
    rw [tsum_sq_diff l q, conv_natAbs l q]
  refine ⟨fun l => summable_sq_diff l q, ?_, ?_⟩
  · rw [funext hterm]
    exact (summable_shiftSeries n).mul_left 2
  · rw [tsum_congr hterm, tsum_mul_left, tsum_shiftSeries n, hcast]
    ring

end LatticeProb.Walk
