/-
The one-dimensional total-variation gradient of the simple random walk kernel.

`∑_k |p_m(k) - p_m(k+2)| = 2(p_m(0) + p_m(1)) = O(m^{-1/2})`.  The two-step
shift is the smallest one that preserves the parity class the kernel lives on,
and it is the shift that the same-parity gradient of the lattice walk reduces
to.

The proof is a telescoping sum, and what makes it available is that the kernel
is unimodal on its parity class.  That is proved here by a five-line induction on
the time and not from the binomial coefficients: the difference at time `m+1`
between `k` and `k+2` is HALF the difference at time `m` between `k-1` and
`k+3`, and two applications of the inductive hypothesis close it, with the
symmetry of the kernel covering the one case `k = 0` where `k - 1` is negative.
-/
import Mathlib
import LatticeProb.Walk.SRWDecomp
import LatticeProb.Walk.SRWSup
import LatticeProb.Walk.SRWDiag

noncomputable section

namespace LatticeProb

open Finset

/-! ### Symmetry and unimodality -/

theorem vecCons_neg (k : ℤ) : (-(![k] : Site 1)) = ![-k] := by
  funext i
  fin_cases i
  simp

theorem S1_neg (n : ℕ) (k : ℤ) : S1 n (-k) = S1 n k := by
  rw [S1, S1, ← vecCons_neg, srwHeat_neg]

/-- **The one-dimensional kernel is unimodal on its parity class**: on the
nonnegative integers it does not increase in steps of two. -/
theorem S1_anti (n : ℕ) : ∀ k : ℤ, 0 ≤ k → S1 n (k + 2) ≤ S1 n k := by
  induction n with
  | zero =>
      intro k hk
      rw [S1_zero, S1_zero, if_neg (by omega)]
      split
      · norm_num
      · exact le_refl 0
  | succ n ih =>
      intro k hk
      rw [S1_succ, S1_succ]
      have hkey : S1 n (k + 2 + 1) ≤ S1 n (k - 1) := by
        rcases eq_or_lt_of_le hk with h0 | h1
        · -- `k = 0`: use the symmetry to replace `k - 1 = -1` by `1`
          rw [← h0]
          have h1 : S1 n ((0 : ℤ) - 1) = S1 n 1 := by
            rw [show ((0 : ℤ) - 1) = -(1 : ℤ) from by ring, S1_neg]
          rw [h1]
          have := ih 1 (by norm_num)
          simpa using this
        · have hk1 : (0 : ℤ) ≤ k - 1 := by omega
          have h1 := ih (k - 1) hk1
          have h2 := ih (k + 1) (by omega)
          have e1 : k - 1 + 2 = k + 1 := by ring
          have e2 : k + 1 + 2 = k + 2 + 1 := by ring
          rw [e1] at h1
          rw [e2] at h2
          linarith
      have e3 : k + 2 - 1 = k + 1 := by ring
      rw [e3]
      linarith

/-! ### The telescoping sum -/

theorem sum_range_S1_sub (n N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), (S1 n (j : ℤ) - S1 n ((j : ℤ) + 2))
      = S1 n 0 + S1 n 1 - S1 n ((N : ℤ) + 1) - S1 n ((N : ℤ) + 2) := by
  induction N with
  | zero =>
      rw [Finset.sum_range_one]
      push_cast
      ring
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem sum_Icc_zero_le (n M : ℕ) :
    ∑ k ∈ Finset.Icc (0 : ℤ) (M : ℤ), |S1 n k - S1 n (k + 2)| ≤ S1 n 0 + S1 n 1 := by
  have hterm : ∀ k ∈ Finset.Icc (0 : ℤ) (M : ℤ),
      |S1 n k - S1 n (k + 2)| = S1 n k - S1 n (k + 2) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact abs_of_nonneg (by linarith [S1_anti n k hk.1])
  rw [Finset.sum_congr rfl hterm]
  have hbij : ∑ k ∈ Finset.Icc (0 : ℤ) (M : ℤ), (S1 n k - S1 n (k + 2))
      = ∑ j ∈ Finset.range (M + 1), (S1 n (j : ℤ) - S1 n ((j : ℤ) + 2)) := by
    refine (Finset.sum_nbij' (i := fun j : ℕ => (j : ℤ))
      (j := fun k : ℤ => k.toNat) ?_ ?_ ?_ ?_ ?_).symm
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc]
      exact ⟨by positivity, by exact_mod_cast Nat.lt_succ_iff.mp hj⟩
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_range]
      omega
    · intro j _
      exact Int.toNat_natCast j
    · intro k hk
      rw [Finset.mem_Icc] at hk
      omega
    · intro j _
      rfl
  rw [hbij, sum_range_S1_sub]
  have h1 : 0 ≤ S1 n ((M : ℤ) + 1) := S1_nonneg _ _
  have h2 : 0 ≤ S1 n ((M : ℤ) + 2) := S1_nonneg _ _
  linarith

theorem sum_Icc_neg_le (n M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ) - 2) (-1), |S1 n k - S1 n (k + 2)|
      ≤ S1 n 0 + S1 n 1 := by
  have hbij : ∑ k ∈ Finset.Icc (-(M : ℤ) - 2) (-1), |S1 n k - S1 n (k + 2)|
      = ∑ j ∈ Finset.Icc (-1 : ℤ) (M : ℤ), |S1 n j - S1 n (j + 2)| := by
    refine Finset.sum_nbij' (i := fun k : ℤ => -2 - k)
      (j := fun j : ℤ => -2 - j) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj ⊢
      omega
    · intro k _; omega
    · intro j _; omega
    · intro k _
      have e1 : S1 n (-2 - k) = S1 n (k + 2) := by
        rw [show (-2 - k : ℤ) = -(k + 2) from by ring, S1_neg]
      have e2 : S1 n (-2 - k + 2) = S1 n k := by
        rw [show (-2 - k + 2 : ℤ) = -k from by ring, S1_neg]
      rw [e1, e2, abs_sub_comm]
  rw [hbij]
  have hins : Finset.Icc (-1 : ℤ) (M : ℤ) = insert (-1 : ℤ) (Finset.Icc (0 : ℤ) (M : ℤ)) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnotmem : (-1 : ℤ) ∉ Finset.Icc (0 : ℤ) (M : ℤ) := by
    rw [Finset.mem_Icc]
    omega
  rw [hins, Finset.sum_insert hnotmem]
  have hzero : |S1 n (-1) - S1 n (-1 + 2)| = 0 := by
    have : S1 n (-1) = S1 n 1 := by
      rw [show (-1 : ℤ) = -(1 : ℤ) from by ring, S1_neg]
    rw [this]
    norm_num
  rw [hzero, zero_add]
  exact sum_Icc_zero_le n M

/-- **The one-dimensional total-variation gradient**, in the explicit form
`∑_k |p_m(k) - p_m(k+2)| ≤ 2(p_m(0) + p_m(1))`. -/
theorem tsum_abs_S1_shift_le (n : ℕ) :
    ∑' k : ℤ, |S1 n k - S1 n (k + 2)| ≤ 2 * (S1 n 0 + S1 n 1) := by
  refine Real.tsum_le_of_sum_le (fun k => abs_nonneg _) fun F => ?_
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ k ∈ F, k ∈ Finset.Icc (-(M : ℤ) - 2) (M : ℤ) := by
    classical
    refine ⟨(F.image (fun k : ℤ => k.natAbs)).sup id, fun k hk => ?_⟩
    have h : k.natAbs ≤ (F.image (fun k : ℤ => k.natAbs)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hk)
    rw [Finset.mem_Icc]
    omega
  have hsub : F ⊆ Finset.Icc (-(M : ℤ) - 2) (M : ℤ) := hM
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => abs_nonneg _).trans ?_
  have hsplit : Finset.Icc (-(M : ℤ) - 2) (M : ℤ)
      = Finset.Icc (-(M : ℤ) - 2) (-1) ∪ Finset.Icc (0 : ℤ) (M : ℤ) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc (-(M : ℤ) - 2) (-1)) (Finset.Icc (0 : ℤ) (M : ℤ)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    rw [Finset.mem_Icc] at hk hk'
    omega
  rw [hsplit, Finset.sum_union hdisj]
  linarith [sum_Icc_neg_le n M, sum_Icc_zero_le n M]

/-- The one-dimensional kernel is at most `C m^{-1/2}`, the `d = 1` case of the
sup bound. -/
theorem S1_le_sqrt {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    S1 n k ≤ Real.sqrt 2 * greenConst 1 / Real.sqrt (n : ℝ) := by
  have h := srwHeat_sup_bound (d := 1) (by norm_num) hn ![k]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrp : ((n : ℝ)) ^ (-((1 : ℕ) : ℝ) / 2) = (Real.sqrt (n : ℝ))⁻¹ := by
    rw [neg_div, Real.rpow_neg hnpos.le]
    congr 1
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [hrp] at h
  simpa [S1, div_eq_mul_inv] using h

/-- **The one-dimensional total-variation gradient decays like `m^{-1/2}`.**
This is the estimate the same-parity gradient of the lattice walk reduces to,
once the two moving coordinates are rotated to `z_i + z_j` and `z_i - z_j`. -/
theorem exists_tsum_abs_S1_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∑' k : ℤ, |S1 n k - S1 n (k + 2)| ≤ C / Real.sqrt (n : ℝ) := by
  refine ⟨4 * (Real.sqrt 2 * greenConst 1) + 1, ?_, fun n hn => ?_⟩
  · have := greenConst_nonneg 1
    have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    positivity
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    refine (tsum_abs_S1_shift_le n).trans ?_
    have h0 := S1_le_sqrt hn 0
    have h1 := S1_le_sqrt hn 1
    have hg := greenConst_nonneg 1
    have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    rw [le_div_iff₀ hsn]
    rw [le_div_iff₀ hsn] at h0 h1
    nlinarith [h0, h1, hsn]

end LatticeProb
