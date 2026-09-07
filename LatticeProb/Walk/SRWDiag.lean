/-
The on-diagonal heat kernel of the simple random walk.

`p_{2n}(0,0) ≍ n^{-d/2}`.  The upper bound is the Gaussian bound of
`LatticeProb/Walk/SRWGaussBound.lean` read on the diagonal.  The lower bound
needs no local central limit theorem: Chapman-Kolmogorov writes `p_{2n}(0,0)`
as `∑_y p_n(0,y)^2`, the second moment of the walk is exactly `n`, so Chebyshev
keeps half the mass inside the Euclidean ball of radius `√(2n)`, and
Cauchy-Schwarz against that ball, whose cardinality is `O(n^{d/2})`, finishes.

This is the estimate that `∑_y g_t(0,y)^2 = ∑_{a,b<t} p_{a+b}(0,0)` rests on.
-/
import Mathlib
import LatticeProb.Walk.SRWGaussBound
import LatticeProb.Walk.Shells
import LatticeProb.Walk.Path

noncomputable section

open scoped ENNReal NNReal

namespace LatticeProb

variable {d : ℕ}

/-! ### Every sum of the kernel at a fixed time is finite -/

theorem srwHeat_eq_zero_of_notMem_box {n : ℕ} {x : Site d}
    (h : x ∉ boxFinset (0 : Site d) n) : srwHeat d n x = 0 := by
  refine srwHeat_eq_zero_of_lt ?_
  by_contra hc
  exact h (mem_boxFinset_zero_iff.mpr (le_trans (supNorm_le_graphNorm x) (by omega)))

theorem summable_srwHeat_mul (n : ℕ) (f : Site d → ℝ) :
    Summable fun x : Site d => srwHeat d n x * f x :=
  summable_of_ne_finset_zero fun x hx => by
    rw [srwHeat_eq_zero_of_notMem_box hx, zero_mul]

theorem summable_srwHeat_shift_mul (n : ℕ) (v : Site d) (f : Site d → ℝ) :
    Summable fun x : Site d => srwHeat d n (x + v) * f x := by
  classical
  refine summable_of_ne_finset_zero
    (s := (boxFinset (0 : Site d) n).image fun y => y - v) fun x hx => ?_
  have hz : srwHeat d n (x + v) = 0 := by
    refine srwHeat_eq_zero_of_notMem_box fun hmem => hx ?_
    exact Finset.mem_image.mpr ⟨x + v, hmem, by ring⟩
  rw [hz, zero_mul]

/-- Reindexing a sum over the lattice by a translation. -/
theorem tsum_shift (v : Site d) (g : Site d → ℝ) :
    ∑' x : Site d, g (x + v) = ∑' y : Site d, g y :=
  (Equiv.addRight v).tsum_eq g

/-! ### The one-step average -/

theorem tsum_srwHeat_succ_mul (n : ℕ) (f : Site d → ℝ) :
    ∑' x : Site d, srwHeat d (n + 1) x * f x
      = (∑ a : Dir d, ∑' x : Site d, srwHeat d n (x + dirVec a) * f x) / (2 * d) := by
  have hpt : ∀ x : Site d, srwHeat d (n + 1) x * f x
      = ∑ a : Dir d, srwHeat d n (x + dirVec a) * f x / (2 * d) := by
    intro x
    rw [srwHeat_succ_eq_sum_dir, div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
  simp_rw [hpt]
  rw [Summable.tsum_finsetSum fun a _ => (summable_srwHeat_shift_mul n (dirVec a) f).div_const _]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun a _ => tsum_div_const

/-! ### The kernel has total mass one -/

theorem tsum_srwHeat (hd : 0 < d) (n : ℕ) : ∑' x : Site d, srwHeat d n x = 1 := by
  classical
  have hd2 : (2 * (d : ℝ)) ≠ 0 := by positivity
  induction n with
  | zero =>
      have : ∀ x : Site d, srwHeat d 0 x = if x = 0 then 1 else 0 := srwHeat_zero
      simp_rw [this]
      exact tsum_ite_eq (0 : Site d) (fun _ => (1 : ℝ))
  | succ n ih =>
      have h1 := tsum_srwHeat_succ_mul (d := d) n (fun _ => 1)
      simp only [mul_one] at h1
      have h2 : ∀ a : Dir d, ∑' x : Site d, srwHeat d n (x + dirVec a) = 1 := fun a => by
        rw [tsum_shift (dirVec a) (srwHeat d n)]; exact ih
      rw [h1, Finset.sum_congr rfl fun a _ => h2 a]
      rw [Finset.sum_const, Finset.card_univ]
      have hcard : (Fintype.card (Dir d) : ℝ) = 2 * d := by
        simp [Dir, Fintype.card_prod, mul_comm]
      rw [nsmul_eq_mul, hcard, mul_one, div_self hd2]

/-! ### The kernel is symmetric -/

theorem srwHeat_neg (n : ℕ) (x : Site d) : srwHeat d n (-x) = srwHeat d n x := by
  classical
  induction n generalizing x with
  | zero => by_cases h : x = 0 <;> simp [h]
  | succ n ih =>
      rw [srwHeat_succ_eq_sum_dir, srwHeat_succ_eq_sum_dir]
      congr 1
      refine Finset.sum_nbij' (fun a => (a.1, !a.2)) (fun a => (a.1, !a.2))
        (fun a _ => Finset.mem_univ _) (fun a _ => Finset.mem_univ _)
        (fun a _ => by simp) (fun a _ => by simp) fun a _ => ?_
      have hflip : dirVec ((a.1, !a.2) : Dir d) = -dirVec a := by
        rcases a with ⟨c, b⟩
        cases b
        · show dirVec ((c, true) : Dir d) = -dirVec ((c, false) : Dir d)
          rw [dirVec_neg c, neg_neg]
        · show dirVec ((c, false) : Dir d) = -dirVec ((c, true) : Dir d)
          exact dirVec_neg c
      rw [hflip, show x + -dirVec a = -(-x + dirVec a) by ring, ih]

/-! ### Chapman-Kolmogorov -/

theorem srwHeat_add (m : ℕ) : ∀ (n : ℕ) (x : Site d),
    srwHeat d (m + n) x = ∑' y : Site d, srwHeat d m y * srwHeat d n (x - y) := by
  intro n
  induction n with
  | zero =>
      intro x
      have hpt : ∀ y : Site d, srwHeat d m y * srwHeat d 0 (x - y)
          = if y = x then srwHeat d m y else 0 := by
        intro y
        rw [srwHeat_zero]
        by_cases h : y = x
        · simp [h]
        · rw [if_neg (fun hc : x - y = 0 => h (by linear_combination -hc)), if_neg h, mul_zero]
      simp_rw [hpt]
      rw [tsum_ite_eq x (srwHeat d m), Nat.add_zero]
  | succ n ih =>
      intro x
      have hstep : srwHeat d (m + (n + 1)) x
          = (∑ a : Dir d, srwHeat d (m + n) (x + dirVec a)) / (2 * d) := by
        rw [show m + (n + 1) = (m + n) + 1 by omega, srwHeat_succ_eq_sum_dir]
      rw [hstep]
      have hin : ∀ a : Dir d, srwHeat d (m + n) (x + dirVec a)
          = ∑' y : Site d, srwHeat d m y * srwHeat d n (x + dirVec a - y) := fun a => ih _
      rw [Finset.sum_congr rfl fun a _ => hin a]
      have hswap : (∑ a : Dir d, ∑' y : Site d, srwHeat d m y * srwHeat d n (x + dirVec a - y))
          = ∑' y : Site d, ∑ a : Dir d, srwHeat d m y * srwHeat d n (x + dirVec a - y) :=
        (Summable.tsum_finsetSum fun a _ =>
          summable_srwHeat_mul m fun y => srwHeat d n (x + dirVec a - y)).symm
      rw [hswap, ← tsum_div_const]
      refine tsum_congr fun y => ?_
      rw [srwHeat_succ_eq_sum_dir, ← Finset.mul_sum, mul_div_assoc]
      congr 2
      exact Finset.sum_congr rfl fun a _ => by rw [show x - y + dirVec a = x + dirVec a - y by ring]

/-- **The return probability is the `ℓ²` mass of the kernel at half the time.** -/
theorem srwHeat_two_mul_zero (n : ℕ) :
    srwHeat d (2 * n) 0 = ∑' y : Site d, srwHeat d n y ^ 2 := by
  rw [show 2 * n = n + n by ring, srwHeat_add n n 0]
  refine tsum_congr fun y => ?_
  rw [show (0 : Site d) - y = -y by ring, srwHeat_neg, sq]

/-! ### The second moment of the walk -/

/-- The squared Euclidean norm of a site. -/
def sqNorm (x : Site d) : ℝ := ∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2

theorem sqNorm_nonneg (x : Site d) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp] theorem sqNorm_zero : sqNorm (0 : Site d) = 0 := by simp [sqNorm]

theorem sqNorm_dirVec (c : Fin d) : sqNorm (dirVec ((c, true) : Dir d)) = 1 := by
  unfold sqNorm dirVec
  rw [Finset.sum_eq_single c]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- The parallelogram law on the lattice. -/
theorem sqNorm_sub_add_sqNorm_add (y v : Site d) :
    sqNorm (y - v) + sqNorm (y + v) = 2 * sqNorm y + 2 * sqNorm v := by
  unfold sqNorm
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (((y i - v i : ℤ) : ℝ)) ^ 2 + (((y i + v i : ℤ) : ℝ)) ^ 2
    = 2 * ((y i : ℤ) : ℝ) ^ 2 + 2 * ((v i : ℤ) : ℝ) ^ 2
  push_cast
  ring

theorem sum_dir_sqNorm_sub (y : Site d) :
    ∑ a : Dir d, sqNorm (y - dirVec a) = 2 * d * sqNorm y + 2 * d := by
  rw [Fintype.sum_prod_type]
  have hrow : ∀ c : Fin d, (∑ b : Bool, sqNorm (y - dirVec ((c, b) : Dir d)))
      = 2 * sqNorm y + 2 := by
    intro c
    rw [Fintype.sum_bool]
    have hfalse : y - dirVec ((c, false) : Dir d) = y + dirVec ((c, true) : Dir d) := by
      rw [dirVec_neg c]; ring
    rw [hfalse, sqNorm_sub_add_sqNorm_add y (dirVec ((c, true) : Dir d)), sqNorm_dirVec c]
    ring
  rw [Finset.sum_congr rfl fun c _ => hrow c, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The second moment of the walk at time `n` is `n`.** -/
theorem tsum_srwHeat_sqNorm (hd : 0 < d) (n : ℕ) :
    ∑' x : Site d, srwHeat d n x * sqNorm x = n := by
  have hd2 : (2 * (d : ℝ)) ≠ 0 := by positivity
  induction n with
  | zero =>
      have hpt : ∀ x : Site d, srwHeat d 0 x * sqNorm x = if x = 0 then sqNorm x else 0 := by
        intro x
        rw [srwHeat_zero]
        by_cases h : x = 0 <;> simp [h]
      simp_rw [hpt]
      rw [tsum_ite_eq (0 : Site d) (sqNorm (d := d))]
      simp
  | succ n ih =>
      rw [tsum_srwHeat_succ_mul n sqNorm]
      have hre : ∀ a : Dir d, (∑' x : Site d, srwHeat d n (x + dirVec a) * sqNorm x)
          = ∑' y : Site d, srwHeat d n y * sqNorm (y - dirVec a) := by
        intro a
        have := tsum_shift (dirVec a) fun y : Site d => srwHeat d n y * sqNorm (y - dirVec a)
        simpa using this
      rw [Finset.sum_congr rfl fun a _ => hre a]
      have hswap : (∑ a : Dir d, ∑' y : Site d, srwHeat d n y * sqNorm (y - dirVec a))
          = ∑' y : Site d, ∑ a : Dir d, srwHeat d n y * sqNorm (y - dirVec a) :=
        (Summable.tsum_finsetSum fun a _ =>
          summable_srwHeat_mul n fun y => sqNorm (y - dirVec a)).symm
      rw [hswap]
      have hin : ∀ y : Site d, (∑ a : Dir d, srwHeat d n y * sqNorm (y - dirVec a))
          = 2 * d * (srwHeat d n y * sqNorm y) + 2 * d * srwHeat d n y := by
        intro y
        rw [← Finset.mul_sum, sum_dir_sqNorm_sub y]
        ring
      rw [tsum_congr hin]
      rw [Summable.tsum_add
        (((summable_srwHeat_mul n sqNorm).mul_left (2 * (d : ℝ))))
        (((summable_srwHeat_mul n fun _ => 1).congr fun x => by rw [mul_one]).mul_left
          (2 * (d : ℝ)))]
      rw [tsum_mul_left, tsum_mul_left, ih, tsum_srwHeat hd n]
      push_cast
      field_simp

/-! ### The diagonal lower bound -/

theorem sum_box_srwHeat (hd : 0 < d) (n : ℕ) :
    ∑ x ∈ boxFinset (0 : Site d) n, srwHeat d n x = 1 := by
  rw [← tsum_srwHeat hd n]
  exact (tsum_eq_sum fun x hx => srwHeat_eq_zero_of_notMem_box hx).symm

theorem sum_box_srwHeat_sqNorm (hd : 0 < d) (n : ℕ) :
    ∑ x ∈ boxFinset (0 : Site d) n, srwHeat d n x * sqNorm x = n := by
  rw [← tsum_srwHeat_sqNorm hd n]
  exact (tsum_eq_sum fun x hx => by rw [srwHeat_eq_zero_of_notMem_box hx, zero_mul]).symm

theorem sum_box_srwHeat_sq_le (n : ℕ) (B : Finset (Site d))
    (hB : B ⊆ boxFinset (0 : Site d) n) :
    ∑ x ∈ B, srwHeat d n x ^ 2 ≤ srwHeat d (2 * n) 0 := by
  rw [srwHeat_two_mul_zero]
  have hfin : ∑' y : Site d, srwHeat d n y ^ 2
      = ∑ x ∈ boxFinset (0 : Site d) n, srwHeat d n x ^ 2 :=
    tsum_eq_sum fun x hx => by rw [srwHeat_eq_zero_of_notMem_box hx]; ring
  rw [hfin]
  exact Finset.sum_le_sum_of_subset_of_nonneg hB fun x _ _ => sq_nonneg _

/-- **The walk returns to its start with probability at least `c n^{-d/2}`.**
No local central limit theorem is used: Chapman-Kolmogorov turns the return
probability into the `ℓ²` mass of the kernel at time `n`, the second moment of
the walk is exactly `n`, so half the mass sits inside the Euclidean ball of
radius `√(2n)`, and Cauchy-Schwarz against that ball finishes. -/
theorem exists_srwHeat_diag_lower (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c / Real.sqrt n ^ d ≤ srwHeat d (2 * n) 0 := by
  classical
  refine ⟨1 / (4 * 6 ^ d), by positivity, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hn1
  set N : Finset (Site d) := boxFinset (0 : Site d) n with hN
  set B : Finset (Site d) := N.filter (fun y => sqNorm y ≤ 2 * (n : ℝ)) with hBdef
  have hBN : B ⊆ N := Finset.filter_subset _ _
  -- half the mass sits in `B`
  have htail : (∑ x ∈ N \ B, srwHeat d n x) ≤ 1 / 2 := by
    have hkey : (2 * (n : ℝ)) * (∑ x ∈ N \ B, srwHeat d n x) ≤ (n : ℝ) := by
      calc (2 * (n : ℝ)) * ∑ x ∈ N \ B, srwHeat d n x
          = ∑ x ∈ N \ B, (2 * (n : ℝ)) * srwHeat d n x := by rw [Finset.mul_sum]
        _ ≤ ∑ x ∈ N \ B, srwHeat d n x * sqNorm x := by
            refine Finset.sum_le_sum fun x hx => ?_
            rw [Finset.mem_sdiff, hBdef, Finset.mem_filter] at hx
            have hgt : 2 * (n : ℝ) < sqNorm x := by
              by_contra hc
              exact hx.2 ⟨hx.1, not_lt.mp hc⟩
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left hgt.le (srwHeat_nonneg _ _)
        _ ≤ ∑ x ∈ N, srwHeat d n x * sqNorm x :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
              fun x _ _ => mul_nonneg (srwHeat_nonneg _ _) (sqNorm_nonneg _)
        _ = (n : ℝ) := sum_box_srwHeat_sqNorm hd n
    nlinarith
  have hmass : (1 : ℝ) / 2 ≤ ∑ x ∈ B, srwHeat d n x := by
    have hsplit : (∑ x ∈ N \ B, srwHeat d n x) + ∑ x ∈ B, srwHeat d n x
        = ∑ x ∈ N, srwHeat d n x := Finset.sum_sdiff hBN
    have h1 : ∑ x ∈ N, srwHeat d n x = 1 := sum_box_srwHeat hd n
    linarith
  -- the ball has at most `6^d n^{d/2}` sites
  have hcard : (B.card : ℝ) ≤ 6 ^ d * Real.sqrt n ^ d := by
    set K : ℕ := ⌈Real.sqrt (2 * (n : ℝ))⌉₊ with hK
    have hBsub : B ⊆ boxFinset (0 : Site d) K := by
      intro x hx
      rw [hBdef, Finset.mem_filter] at hx
      refine mem_boxFinset_zero_iff.mpr (supNorm_le_iff.mpr fun i => ?_)
      have hi : (((x i : ℤ) : ℝ)) ^ 2 ≤ 2 * (n : ℝ) := by
        refine le_trans (Finset.single_le_sum
          (f := fun j => (((x j : ℤ) : ℝ)) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)) ?_
        exact hx.2
      have habs : |((x i : ℤ) : ℝ)| ≤ Real.sqrt (2 * (n : ℝ)) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hi
      have : |((x i : ℤ) : ℝ)| ≤ (K : ℝ) := le_trans habs (Nat.le_ceil _)
      rw [← Int.cast_abs] at this
      exact_mod_cast this
    have hcardK : (B.card : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) ^ d := by
      have hcc := Finset.card_le_card hBsub
      rw [card_boxFinset_zero (d := d) K] at hcc
      calc (B.card : ℝ) ≤ (((2 * K + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hcc
        _ = ((2 * K + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
    have hKle : ((2 * K + 1 : ℕ) : ℝ) ≤ 6 * Real.sqrt n := by
      have hceil : (K : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) + 1 :=
        le_of_lt (Nat.ceil_lt_add_one (Real.sqrt_nonneg _))
      have hs2 : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt n :=
        Real.sqrt_mul (by norm_num) _
      have h2 : Real.sqrt 2 ≤ 3 / 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
      push_cast
      nlinarith [Real.sqrt_nonneg (n : ℝ)]
    refine le_trans hcardK ?_
    calc ((2 * K + 1 : ℕ) : ℝ) ^ d ≤ (6 * Real.sqrt n) ^ d :=
          pow_le_pow_left₀ (by positivity) hKle d
      _ = 6 ^ d * Real.sqrt n ^ d := by rw [mul_pow]
  -- Cauchy-Schwarz against the ball
  have hCS : (∑ x ∈ B, srwHeat d n x) ^ 2 ≤ (B.card : ℝ) * ∑ x ∈ B, srwHeat d n x ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hle : ∑ x ∈ B, srwHeat d n x ^ 2 ≤ srwHeat d (2 * n) 0 :=
    sum_box_srwHeat_sq_le n B hBN
  have hnn : (0 : ℝ) ≤ srwHeat d (2 * n) 0 := srwHeat_nonneg _ _
  have hquarter : (1 : ℝ) / 4 ≤ (B.card : ℝ) * srwHeat d (2 * n) 0 := by
    have h2 : (1 : ℝ) / 4 ≤ (∑ x ∈ B, srwHeat d n x) ^ 2 := by nlinarith [hmass]
    have h3 : (B.card : ℝ) * (∑ x ∈ B, srwHeat d n x ^ 2)
        ≤ (B.card : ℝ) * srwHeat d (2 * n) 0 :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    linarith
  have hfin : (1 : ℝ) / 4 ≤ (6 ^ d * Real.sqrt n ^ d) * srwHeat d (2 * n) 0 :=
    le_trans hquarter (mul_le_mul_of_nonneg_right hcard hnn)
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt n ^ d),
    div_le_iff₀ (by positivity : (0 : ℝ) < 4 * 6 ^ d)]
  nlinarith [hfin]

/-! ### The diagonal upper bound -/

theorem srwHeat_diag_upper (hd : 0 < d) (n : ℕ) (hn : 1 ≤ n) :
    srwHeat d (2 * n) 0 ≤ (3 ^ d * greenConst d + 1) / Real.sqrt n ^ d := by
  have hR : 1 ≤ 2 * n := by omega
  have h := srwHeat_gaussian (d := d) hd hR (0 : Site d)
  have hgn : graphNorm (0 : Site d) = 0 := by simp
  rw [hgn] at h
  norm_num at h
  refine h.trans ?_
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have h2n : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by push_cast; linarith
  have hrp : ((2 * (n : ℝ))) ^ (-(d : ℝ) / 2)
      = (Real.sqrt (2 * (n : ℝ)) ^ d)⁻¹ := by
    have h2 : (0 : ℝ) < 2 * (n : ℝ) := by linarith
    rw [neg_div, Real.rpow_neg h2.le]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2 * (n : ℝ)) ^ ((1 : ℝ) / 2)) d,
      ← Real.rpow_mul h2.le]
    ring_nf
  rw [hrp]
  have hsq : Real.sqrt (n : ℝ) ^ d ≤ Real.sqrt (2 * (n : ℝ)) ^ d :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith)) d
  have hpos : (0 : ℝ) < Real.sqrt (n : ℝ) ^ d :=
    pow_pos (Real.sqrt_pos.mpr hnpos) d
  have hgc : (0 : ℝ) ≤ 3 ^ d * greenConst d := by
    have := greenConst_nonneg d
    positivity
  have hinv : (Real.sqrt (2 * (n : ℝ)) ^ d)⁻¹ ≤ (Real.sqrt (n : ℝ) ^ d)⁻¹ :=
    one_div_le_one_div_of_le hpos hsq |>.trans_eq (by rw [one_div]) |>.trans_eq' (by rw [one_div])
  have hinvnn : (0 : ℝ) ≤ (Real.sqrt (n : ℝ) ^ d)⁻¹ := le_of_lt (inv_pos.mpr hpos)
  calc 3 ^ d * greenConst d * (Real.sqrt (2 * (n : ℝ)) ^ d)⁻¹
      ≤ 3 ^ d * greenConst d * (Real.sqrt (n : ℝ) ^ d)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hgc
    _ ≤ (3 ^ d * greenConst d + 1) / Real.sqrt (n : ℝ) ^ d := by
        rw [div_eq_mul_inv]
        nlinarith

/-- **The on-diagonal heat kernel is of order `n^{-d/2}`.** -/
theorem exists_srwHeat_diag_bounds (hd : 0 < d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      c / Real.sqrt n ^ d ≤ srwHeat d (2 * n) 0 ∧
        srwHeat d (2 * n) 0 ≤ C / Real.sqrt n ^ d := by
  obtain ⟨c, hc, hlow⟩ := exists_srwHeat_diag_lower hd
  have hgc : (0 : ℝ) < 3 ^ d * greenConst d + 1 := by
    have := greenConst_nonneg d
    have h3 : (0 : ℝ) ≤ 3 ^ d := by positivity
    nlinarith
  exact ⟨c, 3 ^ d * greenConst d + 1, hc, hgc, fun n hn =>
    ⟨hlow n hn, srwHeat_diag_upper hd n hn⟩⟩

end LatticeProb

end
