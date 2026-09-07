/-
The gradient of the TRUNCATED Green function of the simple random walk.

The simple walk has a parity obstruction: for neighbouring sites `y` and `z` the
kernels `P^j(0,y)` and `P^j(0,z)` are supported on complementary sets of times,
so no cancellation is visible time by time and the schedule decomposition gives
only `r^{-d/2}` for the difference.  The lazy walk has no such obstruction, and
`LatticeProb/Walk/GRGrad.lean` proves the gradient bound for its truncated Green
function uniformly in the horizon.

What carries the bound across is the profile of `LatticeProb/Walk/BinomWindow.lean`:
the lazy Green function truncated at `2m` is `∑_k A_{2m}(k) P^k(0,·)`, a smoothed
version of `2 ∑_{k < m} P^k(0,·)`, and the two differ by the transition window,
whose mass is `O(√m)` and which sits at times of order `m`, where the kernel is
of size `m^{-d/2}` with its Gaussian factor.  That produces `m^{(1-d)/2}` times a
Gaussian, whose maximum over the horizon is exactly `|x|^{1-d}`.  Well below the
window the profile is exponentially close to its full weight `2`, which keeps the
small times, where the kernel is not small, out of the estimate.

The conclusion is `LatticeProb.exists_srwGreen_gradient`, uniform in the
truncation, which the infinite-horizon form of `LatticeProb/Walk/SimpleTransfer.lean`
does not give and which is what a sum over horizons needs.
-/
import Mathlib
import LatticeProb.Walk.BinomWindow
import LatticeProb.Walk.GRGrad
import LatticeProb.Walk.SRWGaussBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The kernel is a probability -/

/-- The simple-walk kernel never exceeds one. -/
theorem srwHeat_le_one (hd : 0 < d) (j : ℕ) (x : Site d) : srwHeat d j x ≤ 1 := by
  induction j generalizing x with
  | zero =>
    rw [srwHeat_zero]
    split <;> norm_num
  | succ j ih =>
    rw [srwHeat_succ_eq_sum_dir]
    have hcard : (Finset.univ : Finset (Dir d)).card = 2 * d := by
      simp [Dir, Fintype.card_prod, Nat.mul_comm]
    have hdpos : (0 : ℝ) < 2 * (d : ℝ) := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      linarith
    have hsum : ∑ a : Dir d, srwHeat d j (x + dirVec a) ≤ 2 * (d : ℝ) := by
      calc ∑ a : Dir d, srwHeat d j (x + dirVec a) ≤ ∑ _a : Dir d, (1 : ℝ) :=
            Finset.sum_le_sum fun a _ => ih _
        _ = ((Finset.univ : Finset (Dir d)).card : ℝ) := by simp
        _ = 2 * (d : ℝ) := by rw [hcard]; push_cast; ring
    rw [div_le_one hdpos]
    exact hsum

/-! ### The truncated lazy Green function against the truncated simple one -/

/-- The discrepancy between the lazy Green function truncated at `2m` and twice
the simple one truncated at `m`, read off the profile. -/
theorem gR_sub_two_srwGreen (m : ℕ) (x : Site d) :
    gR (2 * m) x - 2 * srwGreen d m x
      = ∑ k ∈ Finset.range (2 * m),
          (Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)) * srwHeat d k x := by
  have hsub : Finset.range m ⊆ Finset.range (2 * m) :=
    fun k hk => Finset.mem_range.mpr (by
      simp only [Finset.mem_range] at hk
      omega)
  have h2 : ∑ k ∈ Finset.range (2 * m), (if k < m then (2 : ℝ) else 0) * srwHeat d k x
      = 2 * srwGreen d m x := by
    rw [← Finset.sum_subset hsub fun k _ hk => by
      simp only [Finset.mem_range, not_lt] at hk
      rw [if_neg (by omega), zero_mul]]
    unfold srwGreen
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk => by
      rw [if_pos (Finset.mem_range.mp hk)]
  rw [gR_eq_sum_Aw (2 * m) x, ← h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The maximum of the window bound over the horizon -/

/-- **The Gaussian window bound.**  The factor `m^{(1-d)/2}` produced by the
window, weighted by its own Gaussian factor, is at most `(1+n)^{1-d}` uniformly
in the horizon: the maximum over `m` sits at `m ≍ n²` and has that size.  The
proof squares both sides, so that the exponential can be traded for a single
term of its series with the INTEGER exponent `d - 1`. -/
theorem exists_gauss_window_le (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 1 ≤ m →
      (m : ℝ) ^ ((1 - (d : ℝ)) / 2)
          * Real.exp (-((n : ℝ) ^ 2) / (16 * (1 + (d : ℝ)) * m))
        ≤ C * (1 + (n : ℝ)) ^ (1 - (d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set K : ℝ := (Nat.factorial (d - 1) : ℝ) * (8 * (1 + (d : ℝ))) ^ (d - 1) with hKdef
  have hKpos : (0 : ℝ) < K := by
    rw [hKdef]
    have h1 : (0 : ℝ) < (Nat.factorial (d - 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (d - 1)
    have h2 : (0 : ℝ) < (8 * (1 + (d : ℝ))) ^ (d - 1) := by positivity
    positivity
  refine ⟨max 1 (Real.sqrt K * 2 ^ ((d : ℝ) - 1)), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    ?_⟩
  intro m n hm
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hexpneg : (1 - (d : ℝ)) / 2 ≤ 0 := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : (-(((0 : ℕ) : ℝ) ^ 2)) / (16 * (1 + (d : ℝ)) * m) = 0 := by
      norm_num
    rw [h1, Real.exp_zero, mul_one]
    have h2 : (m : ℝ) ^ ((1 - (d : ℝ)) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hmR hexpneg
    have h3 : (1 + ((0 : ℕ) : ℝ)) ^ (1 - (d : ℝ)) = 1 := by
      norm_num
    rw [h3, mul_one]
    exact le_trans h2 (le_max_left _ _)
  · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    set A : ℝ := (m : ℝ) ^ ((1 - (d : ℝ)) / 2)
        * Real.exp (-((n : ℝ) ^ 2) / (16 * (1 + (d : ℝ)) * m)) with hAdef
    have hA0 : (0 : ℝ) ≤ A := by
      rw [hAdef]
      positivity
    set t : ℝ := (n : ℝ) ^ 2 / (8 * (1 + (d : ℝ)) * m) with htdef
    have htpos : (0 : ℝ) < t := by
      rw [htdef]
      positivity
    have hAsq : A ^ 2 = (m : ℝ) ^ (1 - (d : ℝ)) * Real.exp (-t) := by
      rw [hAdef, mul_pow]
      congr 1
      · rw [← Real.rpow_natCast ((m : ℝ) ^ ((1 - (d : ℝ)) / 2)) 2, ← Real.rpow_mul hm0.le]
        congr 1
        push_cast
        ring
      · rw [← Real.exp_nat_mul, htdef]
        congr 1
        push_cast
        field_simp
        ring
    have hexp := exp_neg_le_factorial_div (d - 1) htpos
    have hmpow : (m : ℝ) ^ (1 - (d : ℝ)) * (m : ℝ) ^ (d - 1) = 1 := by
      rw [← Real.rpow_natCast (m : ℝ) (d - 1), ← Real.rpow_add hm0]
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        have : (1 : ℕ) ≤ d := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      norm_num
    have hnsq : ((n : ℝ) ^ (1 - (d : ℝ))) ^ 2 = (((n : ℝ) ^ 2) ^ (d - 1))⁻¹ := by
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        have h1d : (1 : ℕ) ≤ d := by omega
        push_cast [Nat.cast_sub h1d]
        ring
      rw [← Real.rpow_natCast ((n : ℝ) ^ (1 - (d : ℝ))) 2, ← Real.rpow_mul hn0.le,
        ← Real.rpow_natCast ((n : ℝ) ^ 2) (d - 1), hcast,
        ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul hn0.le,
        ← Real.rpow_neg hn0.le]
      congr 1
      push_cast
      ring
    have hA2 : A ^ 2 ≤ K * (((n : ℝ) ^ (1 - (d : ℝ))) ^ 2) := by
      have hstep : A ^ 2 ≤ (m : ℝ) ^ (1 - (d : ℝ))
          * ((Nat.factorial (d - 1) : ℝ) / t ^ (d - 1)) := by
        rw [hAsq]
        exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hm0.le _)
      refine le_trans hstep (le_of_eq ?_)
      have htQ : t ^ (d - 1)
          = ((n : ℝ) ^ 2) ^ (d - 1) / ((8 * (1 + (d : ℝ))) ^ (d - 1) * (m : ℝ) ^ (d - 1)) := by
        rw [htdef, div_pow, mul_pow]
      have hdiv : (Nat.factorial (d - 1) : ℝ) / t ^ (d - 1)
          = (Nat.factorial (d - 1) : ℝ)
            * ((8 * (1 + (d : ℝ))) ^ (d - 1) * (m : ℝ) ^ (d - 1))
            / ((n : ℝ) ^ 2) ^ (d - 1) := by
        rw [htQ, div_div_eq_mul_div]
      rw [hdiv, hKdef, hnsq]
      have hPne : (((n : ℝ) ^ 2) ^ (d - 1)) ≠ 0 := by positivity
      have hfinal : (m : ℝ) ^ (1 - (d : ℝ))
            * ((Nat.factorial (d - 1) : ℝ)
              * ((8 * (1 + (d : ℝ))) ^ (d - 1) * (m : ℝ) ^ (d - 1))
              / ((n : ℝ) ^ 2) ^ (d - 1))
          = ((m : ℝ) ^ (1 - (d : ℝ)) * (m : ℝ) ^ (d - 1))
            * ((Nat.factorial (d - 1) : ℝ) * (8 * (1 + (d : ℝ))) ^ (d - 1)
              * (((n : ℝ) ^ 2) ^ (d - 1))⁻¹) := by
        field_simp
      rw [hfinal, hmpow, one_mul]
    have hBnn : (0 : ℝ) ≤ Real.sqrt K * (n : ℝ) ^ (1 - (d : ℝ)) := by positivity
    have hAle : A ≤ Real.sqrt K * (n : ℝ) ^ (1 - (d : ℝ)) := by
      have hsq : A ^ 2 ≤ (Real.sqrt K * (n : ℝ) ^ (1 - (d : ℝ))) ^ 2 := by
        have hexp2 : (Real.sqrt K * (n : ℝ) ^ (1 - (d : ℝ))) ^ 2
            = K * ((n : ℝ) ^ (1 - (d : ℝ))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hKpos.le]
        rw [hexp2]
        exact hA2
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hA0, Real.sqrt_sq hBnn] at h
    refine le_trans hAle (le_trans (shift_one_le hd hn (Real.sqrt_nonneg K)) ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

/-! ### The error between the two truncations -/

/-- **The truncation error.**  Uniformly in `m`, the lazy Green function
truncated at `2m` differs from twice the simple one truncated at `m` by at most
`C (1+|x|)^{1-d}`.  Below the window the profile is exponentially close to its
full weight; inside it the total discrepancy is `O(√m)` and the kernel is
`O(m^{-d/2})` with its Gaussian factor. -/
theorem exists_window_error_le (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (x : Site d),
      |gR (2 * m) x - 2 * srwGreen d m x|
        ≤ C * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
  obtain ⟨C₁, hC₁pos, hgauss⟩ := exists_gauss_window_le d hd
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hgc : (0 : ℝ) ≤ greenConst d := greenConst_nonneg d
  set c : ℝ := Real.log (32 / 25) with hcdef
  have hcpos : (0 : ℝ) < c := Real.log_pos (by norm_num)
  set Clow : ℝ := 8 / 3 * (Nat.factorial (d - 1) : ℝ) * (2 / c) ^ (d - 1) with hClow
  have hfacpos : (0 : ℝ) < (Nat.factorial (d - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (d - 1)
  have hClowpos : (0 : ℝ) < Clow := by
    rw [hClow]
    positivity
  set Chigh : ℝ := 8 * 3 ^ d * greenConst d * 2 ^ ((d : ℝ) / 2) * C₁ with hChigh
  have hChighnn : (0 : ℝ) ≤ Chigh := by
    rw [hChigh]
    have h1 : (0 : ℝ) ≤ 8 * 3 ^ d := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hgc) h2) hC₁pos.le
  refine ⟨Clow + Chigh, by linarith, ?_⟩
  intro m x
  have hRnn : (0 : ℝ) ≤ (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := Real.rpow_nonneg (by positivity) _
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hz0 : gR (2 * 0) x - 2 * srwGreen d 0 x = 0 := by
      norm_num [gR]
    rw [hz0, abs_zero]
    exact mul_nonneg (by linarith) hRnn
  rcases Nat.lt_or_ge (graphNorm x) (2 * m) with hNlt | hNge
  · -- the main case
    have hkey : ∀ k ∈ Finset.range (2 * m),
        |(Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)) * srwHeat d k x|
          = |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)| * srwHeat d k x := by
      intro k _
      rw [abs_mul, abs_of_nonneg (srwHeat_nonneg k x)]
    rw [gR_sub_two_srwGreen]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.sum_congr rfl hkey]
    set h : ℕ := m / 2 with hh
    have hhm : h < m := by omega
    have hh2m : h + 1 ≤ 2 * m := by omega
    have hsplit : ∑ k ∈ Finset.range (2 * m),
          |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)| * srwHeat d k x
        = ∑ k ∈ Finset.range (h + 1),
            |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)| * srwHeat d k x
          + ∑ k ∈ Finset.Ico (h + 1) (2 * m),
            |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)| * srwHeat d k x := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le (h + 1)) hh2m]
    rw [hsplit]
    -- the part below the window
    have hlow : ∑ k ∈ Finset.range (h + 1),
          |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)| * srwHeat d k x
        ≤ 8 / 3 * (25 / 32 : ℝ) ^ m := by
      refine le_trans (Finset.sum_le_sum fun k hk => ?_) (deficit_tail_le m)
      have hkm : k < m := by
        have := Finset.mem_range.mp hk
        omega
      rw [if_pos hkm, abs_of_nonpos (by linarith [Aw_le_two (2 * m) k])]
      have h1 : srwHeat d k x ≤ 1 := srwHeat_le_one hd0 k x
      have h2 : (0 : ℝ) ≤ 2 - Aw (2 * m) k := by linarith [Aw_le_two (2 * m) k]
      nlinarith [srwHeat_nonneg k x]
    -- the part inside the window
    have hPbound : ∀ k ∈ Finset.Ico (h + 1) (2 * m), srwHeat d k x
        ≤ 3 ^ d * greenConst d * (((m : ℝ)) / 2) ^ (-(d : ℝ) / 2)
            * Real.exp (-((graphNorm x : ℝ) ^ 2) / (16 * (1 + (d : ℝ)) * m)) := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
      have hk1' : 1 ≤ k := by omega
      have hg := srwHeat_gaussian (d := d) hd0 hk1' x
      refine le_trans hg ?_
      have hmk : ((m : ℝ)) / 2 ≤ (k : ℝ) := by
        have hnat : m < 2 * (m / 2 + 1) := by omega
        have hcast : (m : ℝ) < 2 * ((h : ℝ) + 1) := by
          rw [hh]
          exact_mod_cast hnat
        have hkc : ((h : ℝ) + 1) ≤ (k : ℝ) := by
          have : (h + 1 : ℕ) ≤ k := hk1
          exact_mod_cast this
        linarith
      have hmpos : (0 : ℝ) < (m : ℝ) / 2 := by
        have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      have hpow : (k : ℝ) ^ (-(d : ℝ) / 2) ≤ ((m : ℝ) / 2) ^ (-(d : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos hmpos hmk (by linarith)
      have hexpmono : Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((k : ℝ) + 2 * d)))
          ≤ Real.exp (-((graphNorm x : ℝ) ^ 2) / (16 * (1 + (d : ℝ)) * m)) := by
        refine Real.exp_le_exp.mpr ?_
        have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hkR : (k : ℝ) ≤ 2 * (m : ℝ) := by
          have : (k : ℝ) < 2 * (m : ℝ) := by exact_mod_cast hk2
          linarith
        have hA : (0 : ℝ) < 8 * ((k : ℝ) + 2 * d) := by positivity
        have hB : (0 : ℝ) < 16 * (1 + (d : ℝ)) * m := by positivity
        have hAB : 8 * ((k : ℝ) + 2 * d) ≤ 16 * (1 + (d : ℝ)) * m := by nlinarith
        have hNsq : (0 : ℝ) ≤ (graphNorm x : ℝ) ^ 2 := by positivity
        have hneg1 : -((graphNorm x : ℝ)) ^ 2 / (8 * ((k : ℝ) + 2 * d))
            = -(((graphNorm x : ℝ) ^ 2) / (8 * ((k : ℝ) + 2 * d))) := by ring
        have hneg2 : -((graphNorm x : ℝ) ^ 2) / (16 * (1 + (d : ℝ)) * m)
            = -(((graphNorm x : ℝ) ^ 2) / (16 * (1 + (d : ℝ)) * m)) := by ring
        rw [hneg1, hneg2, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left hNsq hA hAB
      have hcnn : (0 : ℝ) ≤ 3 ^ d * greenConst d := mul_nonneg (by positivity) hgc
      have h1 : (0 : ℝ) ≤ (k : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
      have h2 : (0 : ℝ) ≤ Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((k : ℝ) + 2 * d))) :=
        (Real.exp_pos _).le
      have h3 : (0 : ℝ) ≤ ((m : ℝ) / 2) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hmpos.le _
      have hstep1 : 3 ^ d * greenConst d * (k : ℝ) ^ (-(d : ℝ) / 2)
          ≤ 3 ^ d * greenConst d * ((m : ℝ) / 2) ^ (-(d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hpow hcnn
      exact mul_le_mul hstep1 hexpmono h2 (mul_nonneg hcnn h3)
    -- the low part against the target
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have h1d : (1 : ℕ) ≤ d := by omega
      push_cast [Nat.cast_sub h1d]
      ring
    have hQpos : (0 : ℝ) < (2 * (m : ℝ)) ^ (d - 1) := by positivity
    have hQeq : (2 * (m : ℝ)) ^ (1 - (d : ℝ)) = ((2 * (m : ℝ)) ^ (d - 1))⁻¹ := by
      rw [← Real.rpow_natCast (2 * (m : ℝ)) (d - 1), hcast,
        ← Real.rpow_neg (by positivity)]
      congr 1
      ring
    have hexpm : (25 / 32 : ℝ) ^ m = Real.exp (-(c * m)) := by
      have hval : Real.exp (-c) = 25 / 32 := by
        rw [hcdef, ← Real.log_inv, Real.exp_log (by norm_num)]
        norm_num
      rw [← hval, ← Real.exp_nat_mul]
      congr 1
      ring
    have hlowfinal : 8 / 3 * (25 / 32 : ℝ) ^ m
        ≤ Clow * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
      have hle : (1 : ℝ) + (graphNorm x : ℝ) ≤ 2 * (m : ℝ) := by
        have h' : graphNorm x + 1 ≤ 2 * m := by omega
        have : ((graphNorm x + 1 : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast h'
        push_cast at this
        linarith
      have hbase : (2 * (m : ℝ)) ^ (1 - (d : ℝ))
          ≤ (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hbase hClowpos.le)
      rw [hQeq, ← div_eq_mul_inv, le_div_iff₀ hQpos, hexpm]
      have hcm : (0 : ℝ) < c * m := by positivity
      have hfac := exp_neg_le_factorial_div (d - 1) hcm
      have hratio : (2 * (m : ℝ)) ^ (d - 1) / (c * m) ^ (d - 1) = (2 / c) ^ (d - 1) := by
        rw [← div_pow]
        congr 1
        field_simp
      have hstep : Real.exp (-(c * m)) * (2 * (m : ℝ)) ^ (d - 1)
          ≤ (Nat.factorial (d - 1) : ℝ) * (2 / c) ^ (d - 1) := by
        have h1 : Real.exp (-(c * m)) * (2 * (m : ℝ)) ^ (d - 1)
            ≤ ((Nat.factorial (d - 1) : ℝ) / (c * m) ^ (d - 1)) * (2 * (m : ℝ)) ^ (d - 1) :=
          mul_le_mul_of_nonneg_right hfac hQpos.le
        refine le_trans h1 (le_of_eq ?_)
        have heq : ((Nat.factorial (d - 1) : ℝ) / (c * m) ^ (d - 1)) * (2 * (m : ℝ)) ^ (d - 1)
            = (Nat.factorial (d - 1) : ℝ) * ((2 * (m : ℝ)) ^ (d - 1) / (c * m) ^ (d - 1)) := by
          ring
        rw [heq, hratio]
      rw [hClow]
      nlinarith [hstep, hfacpos, hQpos]
    -- the high part
    set P : ℝ := 3 ^ d * greenConst d * ((m : ℝ) / 2) ^ (-(d : ℝ) / 2)
        * Real.exp (-((graphNorm x : ℝ) ^ 2) / (16 * (1 + (d : ℝ)) * m)) with hP
    have hPnn : (0 : ℝ) ≤ P := by
      rw [hP]
      have h1 : (0 : ℝ) ≤ 3 ^ d * greenConst d := mul_nonneg (by positivity) hgc
      have h2 : (0 : ℝ) ≤ ((m : ℝ) / 2) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
      exact mul_nonneg (mul_nonneg h1 h2) (Real.exp_pos _).le
    have hhigh : ∑ k ∈ Finset.Ico (h + 1) (2 * m),
          |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)| * srwHeat d k x
        ≤ 8 * Real.sqrt m * P := by
      have h1 : ∑ k ∈ Finset.Ico (h + 1) (2 * m),
            |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)| * srwHeat d k x
          ≤ ∑ k ∈ Finset.Ico (h + 1) (2 * m),
            |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)| * P :=
        Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left (hPbound k hk) (abs_nonneg _)
      have h2 : ∑ k ∈ Finset.Ico (h + 1) (2 * m),
            |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)| * P
          = (∑ k ∈ Finset.Ico (h + 1) (2 * m),
            |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)|) * P := by
        rw [Finset.sum_mul]
      have hsub : Finset.Ico (h + 1) (2 * m) ⊆ Finset.range (2 * m) := fun k hk => by
        have := (Finset.mem_Ico.mp hk).2
        exact Finset.mem_range.mpr this
      have h3 : ∑ k ∈ Finset.Ico (h + 1) (2 * m),
            |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)|
          ≤ ∑ k ∈ Finset.range (2 * m),
            |Aw (2 * m) k - (if k < m then (2 : ℝ) else 0)| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => abs_nonneg _
      have h4 := sum_abs_profile_le m hm
      refine le_trans h1 (le_trans (le_of_eq h2) ?_)
      exact mul_le_mul_of_nonneg_right (le_trans h3 h4) hPnn
    have hident : Real.sqrt (m : ℝ) * ((m : ℝ) / 2) ^ (-(d : ℝ) / 2)
        = (m : ℝ) ^ ((1 - (d : ℝ)) / 2) * 2 ^ ((d : ℝ) / 2) := by
      have e1 : ((m : ℝ) / 2) ^ (-(d : ℝ) / 2)
          = (m : ℝ) ^ (-(d : ℝ) / 2) * 2 ^ ((d : ℝ) / 2) := by
        rw [Real.div_rpow hm0.le (by norm_num), div_eq_mul_inv,
          ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        congr 2
        ring
      have e2 : Real.sqrt (m : ℝ) = (m : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
      rw [e1, e2, ← mul_assoc, ← Real.rpow_add hm0]
      congr 2
      ring
    have hhighfinal : 8 * Real.sqrt m * P
        ≤ Chigh * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
      have hcoef : (0 : ℝ) ≤ 8 * 3 ^ d * greenConst d * 2 ^ ((d : ℝ) / 2) := by
        have h1 : (0 : ℝ) ≤ 8 * 3 ^ d := by positivity
        have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
        exact mul_nonneg (mul_nonneg h1 hgc) h2
      have hrearr : 8 * Real.sqrt (m : ℝ) * P
          = (8 * 3 ^ d * greenConst d * 2 ^ ((d : ℝ) / 2))
            * ((m : ℝ) ^ ((1 - (d : ℝ)) / 2)
              * Real.exp (-((graphNorm x : ℝ) ^ 2) / (16 * (1 + (d : ℝ)) * m))) := by
        rw [hP]
        linear_combination (8 * (3 : ℝ) ^ d * greenConst d
          * Real.exp (-((graphNorm x : ℝ) ^ 2) / (16 * (1 + (d : ℝ)) * m))) * hident
      rw [hrearr, hChigh]
      have hg2 := hgauss m (graphNorm x) hm
      calc (8 * 3 ^ d * greenConst d * 2 ^ ((d : ℝ) / 2))
            * ((m : ℝ) ^ ((1 - (d : ℝ)) / 2)
              * Real.exp (-((graphNorm x : ℝ) ^ 2) / (16 * (1 + (d : ℝ)) * m)))
          ≤ (8 * 3 ^ d * greenConst d * 2 ^ ((d : ℝ) / 2))
            * (C₁ * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ))) :=
            mul_le_mul_of_nonneg_left hg2 hcoef
        _ = 8 * 3 ^ d * greenConst d * 2 ^ ((d : ℝ) / 2) * C₁
            * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by ring
    have hsum : (Clow + Chigh) * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ))
        = Clow * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ))
          + Chigh * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by ring
    rw [hsum]
    exact add_le_add (le_trans hlow hlowfinal) (le_trans hhigh hhighfinal)
  · -- the kernel vanishes on the whole range
    have hzero : gR (2 * m) x - 2 * srwGreen d m x = 0 := by
      rw [gR_sub_two_srwGreen]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' : k < 2 * m := Finset.mem_range.mp hk
      rw [srwHeat_eq_zero_of_lt (by omega), mul_zero]
    rw [hzero, abs_zero]
    have : (0 : ℝ) ≤ (Clow + Chigh) * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
      have : (0 : ℝ) ≤ Clow + Chigh := by linarith
      exact mul_nonneg this hRnn
    exact this

/-! ### The gradient -/

/-- Two neighbouring sites differ in graph norm by at most one. -/
theorem graphNorm_le_of_mem_nbrFinset {y z : Site d} (h : z ∈ nbrFinset y) :
    graphNorm y ≤ graphNorm z + 1 := by
  rcases exists_dir_of_mem_nbrFinset h with ⟨i, hi⟩ | ⟨i, hi⟩
  · subst hi
    exact graphNorm_le_succ_of_add_dirVec y _
  · rw [hi]
    calc graphNorm (z + dirVec ((i, true) : Dir d))
        ≤ graphNorm z + graphNorm (dirVec ((i, true) : Dir d)) := graphNorm_add_le _ _
      _ = graphNorm z + 1 := by rw [graphNorm_dirVec]

/-- **The gradient of the truncated Green function of the simple random walk**,
uniformly in the truncation: for neighbouring `y` and `z` and every `m`,
`|g_m(0,y) - g_m(0,z)| ≤ C (1 + |y|)^{1-d}` in dimension two and above.  This is
`eq:green-gradient` in the finite-horizon form, which the infinite-horizon
statement does not give in dimensions one and two, where the Green function
diverges, and which a sum over horizons needs. -/
theorem exists_srwGreen_gradient (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (y z : Site d), z ∈ nbrFinset y →
      |srwGreen d m y - srwGreen d m z| ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) := by
  obtain ⟨C₂, hC₂, hgrad⟩ := exists_gR_gradient d hd
  obtain ⟨C₃, hC₃, herr⟩ := exists_window_error_le d hd
  have hd0 : 0 < d := by omega
  have hpow : (0 : ℝ) < 2 ^ ((d : ℝ) - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hgen : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
      _ ≤ |a| + |-b| := abs_add_le _ _
      _ = |a| + |b| := by rw [abs_neg]
  refine ⟨C₂ + C₃ + C₃ * 2 ^ ((d : ℝ) - 1), by positivity, ?_⟩
  intro m y z hz
  have hW : (0 : ℝ) ≤ (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have h1 := hgrad (2 * m) y z hz
  have h2 := herr m y
  have h3 := herr m z
  have h4 : (1 + (graphNorm z : ℝ)) ^ (1 - (d : ℝ))
      ≤ 2 ^ ((d : ℝ) - 1) * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) :=
    rpow_shift_le hd0 (graphNorm_le_of_mem_nbrFinset hz)
  have hid : 2 * (srwGreen d m y - srwGreen d m z)
      = (gR (2 * m) y - gR (2 * m) z)
        - ((gR (2 * m) y - 2 * srwGreen d m y) - (gR (2 * m) z - 2 * srwGreen d m z)) := by
    ring
  have habs : |2 * (srwGreen d m y - srwGreen d m z)|
      ≤ |gR (2 * m) y - gR (2 * m) z|
        + (|gR (2 * m) y - 2 * srwGreen d m y| + |gR (2 * m) z - 2 * srwGreen d m z|) := by
    rw [hid]
    refine le_trans (hgen _ _) ?_
    have := hgen (gR (2 * m) y - 2 * srwGreen d m y) (gR (2 * m) z - 2 * srwGreen d m z)
    linarith
  have habs2 : |2 * (srwGreen d m y - srwGreen d m z)|
      = 2 * |srwGreen d m y - srwGreen d m z| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [habs2] at habs
  have hC₃nn : (0 : ℝ) ≤ C₃ := hC₃.le
  have h5 : C₃ * (1 + (graphNorm z : ℝ)) ^ (1 - (d : ℝ))
      ≤ C₃ * (2 ^ ((d : ℝ) - 1) * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ))) :=
    mul_le_mul_of_nonneg_left h4 hC₃nn
  have hnn := abs_nonneg (srwGreen d m y - srwGreen d m z)
  nlinarith [habs, h1, h2, h3, h5, hW, hnn]

end LatticeProb
