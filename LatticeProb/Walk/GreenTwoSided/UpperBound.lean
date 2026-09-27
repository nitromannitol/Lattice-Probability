import LatticeProb.Site
import LatticeProb.Graph.Zd
import LatticeProb.Graph.ExitDecomp
import LatticeProb.Network.Killed
import LatticeProb.Network.KilledGreen
import LatticeProb.Walk.SRWGaussBound
import LatticeProb.Walk.GreenIdentity
import LatticeProb.Walk.Decomp
import LatticeProb.Walk.LocalCLTOne
import LatticeProb.Walk.SRWOneDim
import LatticeProb.Walk.LocalCLT
import LatticeProb.Walk.ExitBox
import LatticeProb.Walk.GreenTwoSided.Kernels
import LatticeProb.Walk.GreenTwoSided.PointwiseBounds

/-!
# The upper bound

The upper bound for the killed Green function of a set contained in a box: for `B ⊆ box d L` and
`x ≠ y`, `g_B(x,y) ≤ C(L+1)^2 (r^{-d} + (L+1)^{-d})` with `r = graphNorm (x-y)`, proved in the
time domain from the pointwise heat-kernel bounds of `PointwiseBounds` by splitting the Green
series into a short head sum and a survival-controlled tail. This file proves the module's first
main public result, `killedGreenReal_le_box`.
-/

open Finset
open scoped Classical

namespace LatticeProb

namespace GreenTwoSided

variable {d : ℕ}

-- Finset.card_le_card into originBox d L (membership: originBox, Fintype.mem_piFinset,
-- Finset.mem_Icc, abs_le from `z ∈ box d L`), card_originBox'; Nat.cast_le, push_cast.
/-- A set contained in `box d L` has at most `(2L + 1) ^ d` elements. -/
private theorem card_le_two_mul_add_one_pow (L : ℕ) (B : Finset (Site d))
    (hB : ∀ z ∈ B, z ∈ box d L) :
    (B.card : ℝ) ≤ (2 * (L : ℝ) + 1) ^ d := by
  refine le_trans (Nat.cast_le.mpr ((Finset.card_le_card ?_).trans (le_of_eq (card_originBox' L))))
      (le_of_eq ?_)
  · intro z hz
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr (abs_le.mp (hB z hz i))
  · push_cast
    rfl


-- unfold Network.survival; Finset.sum_le_sum with killedHeat_le_srwHeat_sub and
-- srwHeat_le_mul_rpow_neg_half (k ≥ 1);
-- Finset.sum_const, nsmul_eq_mul.
/-- The survival probability at time `k ≥ 1` is at most `|B| * (C * k ^ (-d/2))`, given the
on-diagonal heat-kernel bound with constant `C`. -/
private theorem survival_le_card_mul_rpow_neg_half (_unused_hd : 1 ≤ d) (C : ℝ)
    (hC : ∀ (k : ℕ), 1 ≤ k → ∀ w : Site d, srwHeat d k w ≤ C * (k : ℝ) ^ (-(d : ℝ) / 2))
    (B : Finset (Site d)) (k : ℕ) (hk : 1 ≤ k) (x : Site d) :
    Network.survival (lattice d) B k x ≤ (B.card : ℝ) * (C * (k : ℝ) ^ (-(d : ℝ) / 2)) := by
  rw [Network.survival]
  exact le_trans
      (Finset.sum_le_sum (fun v _ => le_trans (killedHeat_le_srwHeat_sub (B : Set (Site d)) k x v)
          (hC k hk (x - v))))
    (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))


-- Arithmetic: choose K with (K:ℝ)^{d/2} ≥ 2 · 3^d · C (e.g. K := ⌈(2·3^d·C)^2⌉₊ + 1, so
-- K^{d/2} ≥ K^{1/2} ≥ 2·3^d·C as d ≥ 1).  Then ((K (L+1)^2 : ℕ) : ℝ)^{-d/2}
-- = K^{-d/2} (L+1)^{-d} (Real.mul_rpow, Real.rpow_natCast, Real.rpow_mul), and
-- (2L+1)^d ≤ 3^d (L+1)^d.  SPLIT?
/-- There is `K ≥ 1` with `(2 * 3^d * C) * K ^ (-d/2) ≤ 1`, the arithmetic input to the
survival-below-a-half bound. -/
private theorem exists_nat_rpow_neg_half_mul_le_one (hd : 1 ≤ d) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℕ, 1 ≤ K ∧ (2 * 3 ^ d * C) * (K : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 := by
  have hA0 : (0 : ℝ) ≤ 2 * 3 ^ d * C :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num : (0:ℝ) ≤ 3) d)) hC.le
  obtain ⟨m, hm⟩ := exists_nat_ge ((2 * 3 ^ d * C) ^ 2)
  refine ⟨m + 1, by omega, ?_⟩
  have hK1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 m
  have hKpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := lt_of_lt_of_le one_pos hK1
  have hm1 : ((m : ℕ) : ℝ) ≤ (((m + 1 : ℕ)) : ℝ) := by push_cast; linarith
  have hsq : (2 * 3 ^ d * C) ^ 2 ≤ ((m + 1 : ℕ) : ℝ) := by linarith
  have hstep1 : 2 * 3 ^ d * C ≤ Real.sqrt (((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.sqrt_sq hA0]
    exact Real.sqrt_le_sqrt hsq
  have hstep2 : Real.sqrt (((m + 1 : ℕ) : ℝ)) ≤ ((m + 1 : ℕ) : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hK1
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hKge : 2 * 3 ^ d * C ≤ ((m + 1 : ℕ) : ℝ) ^ ((d : ℝ) / 2) := le_trans hstep1 hstep2
  have ht_nonneg : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (-(d : ℝ) / 2) :=
    Real.rpow_nonneg hKpos.le _
  calc (2 * 3 ^ d * C) * ((m + 1 : ℕ) : ℝ) ^ (-(d : ℝ) / 2)
      ≤ (((m + 1 : ℕ) : ℝ) ^ ((d : ℝ) / 2)) * ((m + 1 : ℕ) : ℝ) ^ (-(d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hKge ht_nonneg
    _ = 1 := by
        rw [← Real.rpow_add hKpos ((d : ℝ) / 2) (-(d : ℝ) / 2)]
        rw [show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero]

/-- Once `K` satisfies the bound from `exists_nat_rpow_neg_half_mul_le_one`, `(2L+1)^d * (C *
(K(L+1)^2) ^ (-d/2)) ≤ 1/2` for every `L`. -/
private theorem two_mul_add_one_pow_mul_rpow_neg_half_le_half (C : ℝ) (K : ℕ) (hK : 1 ≤ K)
    (hC : 0 < C)
    (hKineq : (2 * 3 ^ d * C) * (K : ℝ) ^ (-(d : ℝ) / 2) ≤ 1) :
    ∀ L : ℕ, (2 * (L : ℝ) + 1) ^ d
      * (C * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2)) ≤ 1 / 2 := by
  intro L
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hPpos : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hPpowpos : (0 : ℝ) < ((L : ℝ) + 1) ^ d := pow_pos hPpos d
  have hPnn : (0 : ℝ) ≤ 2 * (L : ℝ) + 1 := by positivity
  have h2L : 2 * (L : ℝ) + 1 ≤ 3 * ((L : ℝ) + 1) := by linarith
  have hratio : (2 * (L : ℝ) + 1) ^ d * ((L : ℝ) + 1) ^ (-(d : ℝ)) ≤ 3 ^ d := by
    rw [Real.rpow_neg hPpos.le d, Real.rpow_natCast]
    calc (2 * (L : ℝ) + 1) ^ d * (((L : ℝ) + 1) ^ d)⁻¹
        ≤ (3 * ((L : ℝ) + 1)) ^ d * (((L : ℝ) + 1) ^ d)⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hPnn h2L d) (inv_nonneg.2 hPpowpos.le)
      _ = 3 ^ d := by
          rw [mul_pow, mul_assoc, mul_inv_cancel₀ (ne_of_gt hPpowpos), mul_one]
  have hcast : (((K * (L + 1) ^ 2 : ℕ) : ℝ)) = (K : ℝ) * ((L : ℝ) + 1) ^ 2 := by
    push_cast; ring
  have htK : (0 : ℝ) ≤ C * (K : ℝ) ^ (-(d : ℝ) / 2) :=
    mul_nonneg hC.le (Real.rpow_nonneg hKpos.le _)
  rw [hcast]
  have hdec : ((K : ℝ) * ((L : ℝ) + 1) ^ 2) ^ (-(d : ℝ) / 2)
      = (K : ℝ) ^ (-(d : ℝ) / 2) * ((L : ℝ) + 1) ^ (-(d : ℝ)) := by
    rw [Real.mul_rpow hKpos.le (pow_nonneg hPpos.le 2)]
    rw [← Real.rpow_natCast ((L : ℝ) + 1) 2]
    rw [← Real.rpow_mul hPpos.le]
    rw [show ((2 : ℕ) : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) by push_cast; ring]
  rw [hdec]
  calc (2 * (L : ℝ) + 1) ^ d * (C * ((K : ℝ) ^ (-(d : ℝ) / 2) * ((L : ℝ) + 1) ^ (-(d : ℝ))))
      = ((2 * (L : ℝ) + 1) ^ d * ((L : ℝ) + 1) ^ (-(d : ℝ)))
          * (C * (K : ℝ) ^ (-(d : ℝ) / 2)) := by ring
    _ ≤ 3 ^ d * (C * (K : ℝ) ^ (-(d : ℝ) / 2)) := mul_le_mul_of_nonneg_right hratio htK
    _ = ((2 * 3 ^ d * C) * (K : ℝ) ^ (-(d : ℝ) / 2)) / 2 := by ring
    _ ≤ 1 / 2 := div_le_div_of_nonneg_right hKineq (by norm_num)

/-- There is `K ≥ 1` such that `(2L+1)^d * (C * (K(L+1)^2) ^ (-d/2)) ≤ 1/2` for every `L`,
combining `exists_nat_rpow_neg_half_mul_le_one` and
`two_mul_add_one_pow_mul_rpow_neg_half_le_half`. -/
private theorem exists_nat_survival_bound_le_half (hd : 1 ≤ d) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ L : ℕ,
      (2 * (L : ℝ) + 1) ^ d * (C * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2)) ≤ 1 / 2 := by
  obtain ⟨K, hKn, hKineq⟩ := exists_nat_rpow_neg_half_mul_le_one hd C hC
  exact ⟨K, hKn, two_mul_add_one_pow_mul_rpow_neg_half_le_half C K hKn hC hKineq⟩


-- srwHeat_le_mul_rpow_neg_half, exists_nat_survival_bound_le_half,
-- survival_le_card_mul_rpow_neg_half at k = K (L+1)^2 (≥ 1), card_le_two_mul_add_one_pow,
-- mul_le_mul_of_nonneg_right.
/-- There is `K ≥ 1` such that the survival probability at time `K(L+1)^2` is at most `1/2` for
every box radius `L` and every set `B ⊆ box d L`. -/
private theorem exists_nat_survival_le_half (hd : 1 ≤ d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (L : ℕ) (B : Finset (Site d)), (∀ z ∈ B, z ∈ box d L) → ∀ x : Site d,
      Network.survival (lattice d) B (K * (L + 1) ^ 2) x ≤ 1 / 2 := by
  obtain ⟨C, hCpos, hC⟩ := srwHeat_le_mul_rpow_neg_half hd
  obtain ⟨K', hK'1, hK'⟩ := exists_nat_survival_bound_le_half hd C hCpos
  refine ⟨K', hK'1, ?_⟩
  intro L B hB x
  have h1 : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow 2 (L + 1) (Nat.succ_pos L)
  have hKL : 1 ≤ K' * (L + 1) ^ 2 := Nat.mul_le_mul hK'1 h1
  have h15 := survival_le_card_mul_rpow_neg_half hd C hC B (K' * (L + 1) ^ 2) hKL x
  have h14 := card_le_two_mul_add_one_pow L B hB
  have h16 := hK' L
  have hnn : 0 ≤ C * (((K' * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2) :=
    mul_nonneg (le_of_lt hCpos) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc Network.survival (lattice d) B (K' * (L + 1) ^ 2) x
      ≤ (B.card : ℝ) * (C * (((K' * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2)) := h15
    _ ≤ (2 * (L : ℝ) + 1) ^ d
          * (C * (((K' * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right h14 hnn
    _ ≤ 1 / 2 := h16


-- Network.sum_range_survival_le (hN : 0 < N) (θ := 1/2): N / (1 - 1/2) = 2N (norm_num).
/-- If the survival probability at time `N > 0` is uniformly at most `1/2`, then the partial sums
of survival over any range are at most `2N`, by `Network.sum_range_survival_le`. -/
private theorem sum_range_survival_le_two_mul (B : Finset (Site d)) (N : ℕ) (hN : 0 < N)
    (h : ∀ x : Site d, Network.survival (lattice d) B N x ≤ 1 / 2) (x : Site d) (n : ℕ) :
    ∑ k ∈ Finset.range n, Network.survival (lattice d) B k x ≤ 2 * (N : ℝ) := by
  have h1 := Network.sum_range_survival_le (G := lattice d) (C := B) (N := N)
      (θ := (1/2 : ℝ)) hN (by norm_num) (by norm_num) h x n
  rw [show ((N : ℝ)) / (1 - (1/2 : ℝ)) = 2 * ((N : ℝ)) by ring] at h1
  exact h1


-- Tail: termwise killedHeat_add_le_survival_mul with S := C N^{-d/2} (hS from
-- killedHeat_le_srwHeat_sub + hC at N),
-- ← Finset.sum_mul, sum_range_survival_le_two_mul, mul_le_mul_of_nonneg_right (S ≥ 0:
-- Real.rpow_nonneg).
/-- The tail sum `∑_{k<n} killedHeat (k+N) x y` is at most `2N * (C * N ^ (-d/2))`, given the
on-diagonal bound and the survival bound at time `N`. -/
private theorem sum_range_killedHeat_add_le_two_mul_rpow_neg_half (_unused_hd : 1 ≤ d) (C : ℝ)
    (hC : ∀ (k : ℕ), 1 ≤ k → ∀ w : Site d, srwHeat d k w ≤ C * (k : ℝ) ^ (-(d : ℝ) / 2))
    (B : Finset (Site d)) (N : ℕ) (hN : 0 < N)
    (h : ∀ x : Site d, Network.survival (lattice d) B N x ≤ 1 / 2) (x y : Site d) (n : ℕ) :
    ∑ k ∈ Finset.range n, Graph.killedHeat (lattice d) (B : Set (Site d)) (k + N) x y
      ≤ 2 * (N : ℝ) * (C * (N : ℝ) ^ (-(d : ℝ) / 2)) := by
  have hN1 : 1 ≤ N := hN
  have hCnn : (0 : ℝ) ≤ C :=
    le_trans (srwHeat_nonneg (d := d) 1 x) (by simpa using hC 1 le_rfl x)
  have hSnn : 0 ≤ C * (N : ℝ) ^ (-(d : ℝ) / 2) :=
    mul_nonneg hCnn (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hS : ∀ z ∈ B, Graph.killedHeat (lattice d) (B : Set (Site d)) N z y
      ≤ C * (N : ℝ) ^ (-(d : ℝ) / 2) := fun z _ =>
    le_trans (killedHeat_le_srwHeat_sub (B : Set (Site d)) N z y) (hC N hN1 (z - y))
  exact le_trans
    (le_trans
      (Finset.sum_le_sum fun k _ => killedHeat_add_le_survival_mul B k N x y _ (fun z hz => hS z
          hz))
      (le_of_eq (Finset.sum_mul _ _ _).symm))
    (mul_le_mul_of_nonneg_right (sum_range_survival_le_two_mul B N hN h x n) hSnn)


-- Head: termwise killedHeat_le_srwHeat_sub and the off-diagonal hC with r := graphNorm (x - y)
-- (≥ 1 by graphNorm_eq_zero_iff, sub_eq_zero); Finset.sum_le_card_nsmul / sum_const, card_range.
/-- The head sum `∑_{k<N} killedHeat k x y` is at most `N * (C / graphNorm (x - y) ^ d)`, from
the off-diagonal heat-kernel bound. -/
private theorem sum_range_killedHeat_le_mul_div_pow (C : ℝ)
    (hC : ∀ (k : ℕ) (w : Site d) (r : ℕ), 1 ≤ r → r ≤ graphNorm w → srwHeat d k w ≤ C / (r : ℝ) ^ d)
    (B : Finset (Site d)) (N : ℕ) (x y : Site d) (hxy : x ≠ y) :
    ∑ k ∈ Finset.range N, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
      ≤ (N : ℝ) * (C / (graphNorm (x - y) : ℝ) ^ d) := by
  refine le_trans (b := ∑ k ∈ Finset.range N, C / (graphNorm (x - y) : ℝ) ^ d) ?_ ?_
  · exact Finset.sum_le_sum
      (fun k _ => le_trans (killedHeat_le_srwHeat_sub (B : Set (Site d)) k x y)
      (hC k (x - y) (graphNorm (x - y))
        (Nat.one_le_iff_ne_zero.mpr (fun h => sub_ne_zero.mpr hxy (graphNorm_eq_zero_iff.mp h)))
        le_rfl))
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


-- NeZero d; q ∉ B from Infinite.exists_notMem_finset (Graph.Zd.latticeInfinite);
-- Network.killedGreenReal_eq_tsum (Graph.Zd.latticeConnected d) B hq x y; Graph.Zd.degree_eq,
-- push_cast.
/-- The killed Green function equals the total mass of `killedHeat` divided by `2d`:
`killedGreenReal B x y = (∑' k, killedHeat k x y) / (2d)`. -/
theorem killedGreenReal_eq_tsum_killedHeat_div (hd : 1 ≤ d) (B : Finset (Site d))
    (x y : Site d) :
    Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
      = (∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) / (2 * (d : ℝ)) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset B
  rw [Network.killedGreenReal_eq_tsum (Graph.Zd.latticeConnected d) B hq x y]
  rw [Graph.Zd.degree_eq]
  push_cast
  ring


-- Real.tsum_le_of_sum_range_le (Network.killedHeat_nonneg): for each n, the range-n partial sum
-- ≤ range (N + n) partial sum (Finset.sum_le_sum_of_subset_of_nonneg, range_mono) and
-- Finset.sum_range_add splits it into head + ∑_{k<n} killedHeat (N + k) (add_comm to k + N).
/-- If the head sum up to `N` is at most `H` and every tail sum from `N` is at most `T`, the full
series `∑' k, killedHeat k x y` is at most `H + T`. -/
private theorem tsum_killedHeat_le_add_of_sum_range_le (B : Finset (Site d)) (N : ℕ) (x y : Site d)
    (H T : ℝ)
    (hH : ∑ k ∈ Finset.range N, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y ≤ H)
    (hT : ∀ n, ∑ k ∈ Finset.range n, Graph.killedHeat (lattice d) (B : Set (Site d)) (k + N) x y ≤
        T) :
    ∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y ≤ H + T := by
  refine Real.tsum_le_of_sum_range_le
    (fun k => Network.killedHeat_nonneg (B : Set (Site d)) k x y) (fun n => ?_)
  have hT0 : (0:ℝ) ≤ T := (by simpa using hT 0)
  by_cases hn : n ≤ N
  · have h1 : ∑ k ∈ Finset.range n, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
        ≤ ∑ k ∈ Finset.range N, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
        (fun i _ _ => Network.killedHeat_nonneg (B : Set (Site d)) i x y)
    linarith
  · have hle : N ≤ n := Nat.le_of_not_le hn
    have hsplit : ∑ k ∈ Finset.range n, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y
        = (∑ k ∈ Finset.range N, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y)
          + (∑ k ∈ Finset.range (n - N),
              Graph.killedHeat (lattice d) (B : Set (Site d)) (k + N) x y) := (by
      nth_rewrite 1 [← Nat.add_sub_of_le hle]
      rw [Finset.sum_range_add]
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [Nat.add_comm]))
    linarith [hH, hT (n - N)]


-- Arithmetic with N = K (L+1)^2:  N · C₁ / r^d ≤ K C₁ (L+1)^2 / r^d  and
-- 2 N · C₂ N^{-d/2} = 2 C₂ K^{1-d/2} (L+1)^{2-d} ≤ 2 C₂ K (L+1)^2 / (L+1)^d  (K ≥ 1,
-- Real.rpow_natCast, Real.mul_rpow, Real.rpow_le_rpow_of_exponent_le).  SPLIT?
/-- Arithmetic combination of the head and tail bounds at `N = K(L+1)^2` into the single estimate
`K(C₁+2C₂)(L+1)^2 (1/r^d + 1/(L+1)^d)`. -/
private theorem two_mul_add_one_sq_mul_rpow_neg_half_le (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (K L : ℕ) (hK : 1 ≤ K)
    (r : ℝ) (hr : 0 < r) :
    ((K * (L + 1) ^ 2 : ℕ) : ℝ) * (C₁ / r ^ d)
        + 2 * ((K * (L + 1) ^ 2 : ℕ) : ℝ)
          * (C₂ * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2))
      ≤ (K : ℝ) * (C₁ + 2 * C₂) * ((L : ℝ) + 1) ^ 2 * (1 / r ^ d + 1 / ((L : ℝ) + 1) ^ d) := by
  set N : ℝ := ((K * (L + 1) ^ 2 : ℕ) : ℝ) with hNdef
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hK1 : (1:ℝ) ≤ (K:ℝ) :=by exact_mod_cast hK
  have hL1 : (0:ℝ) < (L:ℝ) + 1 :=by
    have hL0 : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
    linarith
  have hbase2 : (0:ℝ) ≤ ((L:ℝ)+1)^2 := pow_nonneg (le_of_lt hL1) 2
  have hN : N = (K:ℝ) * ((L:ℝ)+1)^2 :=by rw [hNdef]; push_cast; ring
  have hNnn : 0 ≤ N :=by rw [hN]; exact mul_nonneg hK0 hbase2
  have hpowd : 0 < ((L:ℝ)+1)^d := pow_pos hL1 d
  have hdivpos : 0 < 1 / ((L:ℝ)+1)^d := one_div_pos.mpr hpowd
  have hz : -(d:ℝ)/2 ≤ 0 :=by
    have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  have hkey : N ^ (-(d:ℝ)/2) ≤ 1 / ((L:ℝ)+1)^d :=by
    rw [hN, Real.mul_rpow hK0 hbase2]
    have hKle : (K:ℝ)^(-(d:ℝ)/2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK1 hz
    have h2 : (((L:ℝ)+1)^2)^(-(d:ℝ)/2) = 1 / ((L:ℝ)+1)^d :=by
      have e1 : (((L:ℝ)+1)^2)^(-(d:ℝ)/2) = (((L:ℝ)+1)^((2:ℕ):ℝ))^(-(d:ℝ)/2) :=by
        rw [Real.rpow_natCast]
      rw [e1, ← Real.rpow_mul (le_of_lt hL1) ((2:ℕ):ℝ) (-(d:ℝ)/2)]
      rw [show (((2:ℕ):ℝ) * (-(d:ℝ)/2)) = -(d:ℝ) by push_cast; ring]
      rw [Real.rpow_neg (le_of_lt hL1), Real.rpow_natCast, one_div]
    rw [h2]
    calc (K:ℝ)^(-(d:ℝ)/2) * (1/((L:ℝ)+1)^d)
        ≤ 1 * (1/((L:ℝ)+1)^d) := mul_le_mul_of_nonneg_right hKle (le_of_lt hdivpos)
      _ = 1 / ((L:ℝ)+1)^d := one_mul _
  have h1 : N * (C₁ / r^d) ≤ (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/r^d) :=by
    have hC : C₁ / r^d ≤ (C₁ + 2*C₂) * (1/r^d) :=by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt (pow_pos hr d))
    calc N * (C₁ / r^d) = (K:ℝ) * ((L:ℝ)+1)^2 * (C₁/r^d) :=by rw [hN]
      _ ≤ (K:ℝ) * ((L:ℝ)+1)^2 * ((C₁+2*C₂) * (1/r^d)) :=
          mul_le_mul_of_nonneg_left hC (mul_nonneg hK0 hbase2)
      _ = (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/r^d) :=by ring
  have h2' : 2 * N * (C₂ * N ^ (-(d:ℝ)/2))
      ≤ (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/((L:ℝ)+1)^d) :=by
    have hS : C₂ * N ^ (-(d:ℝ)/2) ≤ C₂ * (1/((L:ℝ)+1)^d) :=
      mul_le_mul_of_nonneg_left hkey (le_of_lt hC₂)
    calc 2 * N * (C₂ * N ^ (-(d:ℝ)/2))
        ≤ 2 * N * (C₂ * (1/((L:ℝ)+1)^d)) :=
          mul_le_mul_of_nonneg_left hS (mul_nonneg (by norm_num) hNnn)
      _ = (K:ℝ) * ((L:ℝ)+1)^2 * (1/((L:ℝ)+1)^d) * (2*C₂) :=by rw [hN]; ring
      _ ≤ (K:ℝ) * ((L:ℝ)+1)^2 * (1/((L:ℝ)+1)^d) * (C₁+2*C₂) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (mul_nonneg hK0 hbase2) (le_of_lt hdivpos))
      _ = (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/((L:ℝ)+1)^d) :=by ring
  calc N * (C₁ / r^d) + 2 * N * (C₂ * N ^ (-(d:ℝ)/2))
      ≤ (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/r^d)
        + (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/((L:ℝ)+1)^d) := add_le_add h1 h2'
    _ = (K:ℝ) * (C₁ + 2*C₂) * ((L:ℝ)+1)^2 * (1/r^d + 1/((L:ℝ)+1)^d) :=by ring


-- C := K (C₁ + 2 C₂) / (2d) with C₁ from srwHeat_le_div_pow_of_le_graphNorm, C₂ from
-- srwHeat_le_mul_rpow_neg_half, K from exists_nat_survival_le_half;
-- killedGreenReal_eq_tsum_killedHeat_div, tsum_killedHeat_le_add_of_sum_range_le with
-- sum_range_killedHeat_le_mul_div_pow (N := K (L+1)^2) and
-- sum_range_killedHeat_add_le_two_mul_rpow_neg_half, two_mul_add_one_sq_mul_rpow_neg_half_le,
-- div_le_div_of_nonneg_right.
/-- For `B` contained in `box d L` and `x ≠ y`, the killed Green function satisfies `g_B(x,y) ≤
C(L+1)^2 (r^{-d} + (L+1)^{-d})` with `r = graphNorm (x-y)`, uniformly in `d ≥ 1`. -/
theorem killedGreenReal_le_box (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (B : Finset (Site d)), (∀ z ∈ B, z ∈ box d L) →
      ∀ x y : Site d, x ≠ y →
        Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
          ≤ C * ((L : ℝ) + 1) ^ 2 * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := srwHeat_le_div_pow_of_le_graphNorm hd
  obtain ⟨C₂, hC₂pos, hC₂⟩ := srwHeat_le_mul_rpow_neg_half hd
  obtain ⟨K, hK1, hK⟩ := exists_nat_survival_le_half hd
  have hd0 : 0 < d := hd
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd0
  have hd2pos : (0 : ℝ) < 2 * (d : ℝ) := mul_pos (by norm_num) hdpos
  have hK0 : 0 < K := hK1
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK0
  have hSum : (0 : ℝ) < C₁ + 2 * C₂ := add_pos hC₁pos (mul_pos (by norm_num) hC₂pos)
  refine ⟨(K : ℝ) * (C₁ + 2 * C₂) / (2 * (d : ℝ)), div_pos (mul_pos hKpos hSum) hd2pos, ?_⟩
  intro L B hB x y hxy
  have hNpos : 0 < K * (L + 1) ^ 2 := Nat.mul_pos hK0 (pow_pos (Nat.succ_pos L) 2)
  have hsurv : ∀ x : Site d, Network.survival (lattice d) B (K * (L + 1) ^ 2) x ≤ 1 / 2 :=
    fun x => hK L B hB x
  have hH := sum_range_killedHeat_le_mul_div_pow C₁ hC₁ B (K * (L + 1) ^ 2) x y hxy
  have hT : ∀ n, ∑ k ∈ Finset.range n,
      Graph.killedHeat (lattice d) (B : Set (Site d)) (k + K * (L + 1) ^ 2) x y
        ≤ 2 * ((K * (L + 1) ^ 2 : ℕ) : ℝ)
            * (C₂ * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2)) :=
    fun n => sum_range_killedHeat_add_le_two_mul_rpow_neg_half hd C₂ hC₂ B (K * (L + 1) ^ 2) hNpos
        hsurv x y n
  have htsum := tsum_killedHeat_le_add_of_sum_range_le B (K * (L + 1) ^ 2) x y _ _ hH hT
  have hgn0 : 0 < graphNorm (x - y) := (by
    rcases Nat.eq_zero_or_pos (graphNorm (x - y)) with h | h
    · exact absurd (graphNorm_eq_zero_iff.mp h) (sub_ne_zero.mpr hxy)
    · exact h)
  have hr : (0 : ℝ) < (graphNorm (x - y) : ℝ) := Nat.cast_pos.mpr hgn0
  have h23 := two_mul_add_one_sq_mul_rpow_neg_half_le (d := d) C₁ C₂ hC₁pos hC₂pos K L hK1
      (graphNorm (x - y) : ℝ) hr
  have hgr : Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
      ≤ ((K : ℝ) * (C₁ + 2 * C₂) / (2 * (d : ℝ))) * ((L : ℝ) + 1) ^ 2
          * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d) := (by
    rw [killedGreenReal_eq_tsum_killedHeat_div hd B x y]
    calc (∑' k : ℕ, Graph.killedHeat (lattice d) (B : Set (Site d)) k x y) / (2 * (d : ℝ))
        ≤ (((K * (L + 1) ^ 2 : ℕ) : ℝ) * (C₁ / (graphNorm (x - y) : ℝ) ^ d)
            + 2 * ((K * (L + 1) ^ 2 : ℕ) : ℝ)
                * (C₂ * (((K * (L + 1) ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2))) / (2 * (d : ℝ)) :=
          div_le_div_of_nonneg_right htsum (le_of_lt hd2pos)
      _ ≤ ((K : ℝ) * (C₁ + 2 * C₂) * ((L : ℝ) + 1) ^ 2
              * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d)) / (2 * (d : ℝ)) :=
          div_le_div_of_nonneg_right h23 (le_of_lt hd2pos)
      _ = ((K : ℝ) * (C₁ + 2 * C₂) / (2 * (d : ℝ))) * ((L : ℝ) + 1) ^ 2
            * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d) := (by ring_nf))
  exact hgr

end GreenTwoSided

end LatticeProb
