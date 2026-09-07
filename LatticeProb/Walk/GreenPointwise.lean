/-
The pointwise Green bound `G(0,z) ≤ C(1+|z|)^{2-d}` above dimension four.

The Green function is the kernel summed over time, and the sum is split at
`j = |z|^2`.  Past that time the kernel is below its on-diagonal value and the
tail of `∑ j^{-d/2}` is `O(|z|^{2-d})`, which is `sum_Ico_srwHeat_high_le`.
Before it the Gaussian factor does the work, and the way to use it is not a
sharper kernel estimate but the elementary `exp(-u) ≤ (K/u)^K`, read at the
INTEGER exponent `K = d`: with `u ≍ |z|^2/j` the bound becomes `(Cj/|z|^2)^d`,
the `j^d` cancels the `j^{-d/2}` down to `√j^d ≤ |z|^d`, and the surviving
`|z|^{-2d} |z|^d` summed over the `|z|^2` times before the split is exactly
`|z|^{2-d}`.  Choosing `K = d` rather than the least admissible exponent is what
makes every power an integer power.

The norm here is the graph norm `|z|_1`, which is at least the Euclidean norm,
so this form of the bound is the stronger one.
-/
import Mathlib
import LatticeProb.Walk.Correlation
import LatticeProb.Walk.SimpleTransfer
import LatticeProb.Walk.Ball

noncomputable section

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### Two elementary inputs -/

/-- `exp(-u) ≤ (K/u)^K`: the exponential beats every integer power, written so
that both sides are integer powers.  From `exp(u) = (exp(u/K))^K` and
`u/K ≤ exp(u/K)`. -/
theorem exp_neg_le_pow_div {u : ℝ} (hu : 0 < u) (K : ℕ) :
    Real.exp (-u) ≤ ((K : ℝ) / u) ^ K := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simpa using hu.le
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hbase : u / K ≤ Real.exp (u / K) := by
    have := Real.add_one_le_exp (u / K)
    linarith
  have hnn : (0 : ℝ) ≤ u / K := by positivity
  have hpow : (u / K) ^ K ≤ Real.exp (u / K) ^ K := pow_le_pow_left₀ hnn hbase K
  have hexp : Real.exp (u / K) ^ K = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hexp] at hpow
  have hlow : (0 : ℝ) < (u / K) ^ K := by positivity
  rw [Real.exp_neg]
  rw [show ((K : ℝ) / u) ^ K = ((u / K) ^ K)⁻¹ by rw [← inv_pow, inv_div]]
  exact inv_anti₀ hlow hpow

/-- The Gaussian upper bound with the exponential kept, in the `√s ^ d` form of
`LatticeProb.srwHeat_diag_le`. -/
theorem srwHeat_gauss_sqrt (hd : 0 < d) {s : ℕ} (hs : 1 ≤ s) (y : Site d) :
    srwHeat d s y ≤ diagConst d / Real.sqrt s ^ d
      * Real.exp (-((graphNorm y : ℝ)) ^ 2 / (8 * ((s : ℝ) + 2 * d))) := by
  have h := srwHeat_gaussian (d := d) hd hs y
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hrp : ((s : ℝ)) ^ (-(d : ℝ) / 2) = (Real.sqrt (s : ℝ) ^ d)⁻¹ := by
    rw [neg_div, Real.rpow_neg hspos.le]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((s : ℝ) ^ ((1 : ℝ) / 2)) d,
      ← Real.rpow_mul hspos.le]
    ring_nf
  rw [hrp] at h
  refine h.trans ?_
  have hE : (0 : ℝ) < Real.exp (-((graphNorm y : ℝ)) ^ 2 / (8 * ((s : ℝ) + 2 * d))) :=
    Real.exp_pos _
  have hinv : (0 : ℝ) < (Real.sqrt (s : ℝ) ^ d)⁻¹ :=
    inv_pos.mpr (pow_pos (Real.sqrt_pos.mpr hspos) d)
  rw [show diagConst d / Real.sqrt (s : ℝ) ^ d = diagConst d * (Real.sqrt (s : ℝ) ^ d)⁻¹ from
    div_eq_mul_inv _ _]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hinv.le) hE.le
  have hg := greenConst_nonneg d
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  rw [diagConst]
  linarith

/-! ### The near-time bound -/

/-- The constant in the near-time estimate. -/
def nearConst (d : ℕ) : ℝ := diagConst d * (8 * (d : ℝ) * (1 + 2 * (d : ℝ))) ^ d

theorem nearConst_pos (hd : 0 < d) : 0 < nearConst d := by
  have h1 : (0 : ℝ) < 8 * (d : ℝ) * (1 + 2 * (d : ℝ)) := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  exact mul_pos (diagConst_pos d) (pow_pos h1 d)

/-- **The kernel before the split time.**  For `1 ≤ j ≤ |z|^2` the kernel at
`z` is at most `nearConst d / |z|^d`. -/
theorem srwHeat_near_le (hd : 0 < d) {z : Site d} (hz : 1 ≤ graphNorm z) {j : ℕ}
    (hj : 1 ≤ j) (hjle : j ≤ graphNorm z ^ 2) :
    srwHeat d j z ≤ nearConst d / (graphNorm z : ℝ) ^ d := by
  set n : ℝ := (graphNorm z : ℝ) with hn
  have hnpos : (0 : ℝ) < n := by
    rw [hn]; exact_mod_cast hz
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  set S : ℝ := Real.sqrt (j : ℝ) with hS
  have hSpos : 0 < S := Real.sqrt_pos.mpr hjpos
  have hSsq : S * S = (j : ℝ) := Real.mul_self_sqrt hjpos.le
  have hSn : S ≤ n := by
    have hjn : (j : ℝ) ≤ n ^ 2 := by
      rw [hn]
      have : (j : ℝ) ≤ ((graphNorm z ^ 2 : ℕ) : ℝ) := by exact_mod_cast hjle
      simpa [pow_two] using this
    rw [hS, show n = Real.sqrt (n ^ 2) from (Real.sqrt_sq hnpos.le).symm]
    exact Real.sqrt_le_sqrt hjn
  -- the exponential factor
  set u : ℝ := n ^ 2 / (8 * ((j : ℝ) + 2 * (d : ℝ))) with hu
  have hden : (0 : ℝ) < 8 * ((j : ℝ) + 2 * (d : ℝ)) := by positivity
  have hupos : 0 < u := by rw [hu]; positivity
  have hexp1 : Real.exp (-u) ≤ ((d : ℝ) / u) ^ d := exp_neg_le_pow_div hupos d
  have hdu : (d : ℝ) / u = (d : ℝ) * (8 * ((j : ℝ) + 2 * (d : ℝ))) / n ^ 2 := by
    rw [hu]
    field_simp
  have hkey : (d : ℝ) / u ≤ 8 * (d : ℝ) * (1 + 2 * (d : ℝ)) * (j : ℝ) / n ^ 2 := by
    rw [hdu]
    have hnum : (d : ℝ) * (8 * ((j : ℝ) + 2 * (d : ℝ)))
        ≤ 8 * (d : ℝ) * (1 + 2 * (d : ℝ)) * (j : ℝ) := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ 16 * (d : ℝ) ^ 2 by positivity)
        (show (0:ℝ) ≤ (j : ℝ) - 1 by linarith)]
    exact div_le_div_of_nonneg_right hnum (by positivity) |>.trans_eq rfl
  have hexp2 : Real.exp (-u)
      ≤ (8 * (d : ℝ) * (1 + 2 * (d : ℝ)) * (j : ℝ) / n ^ 2) ^ d := by
    refine hexp1.trans (pow_le_pow_left₀ ?_ hkey d)
    rw [hdu]; positivity
  -- the kernel bound
  have hgauss := srwHeat_gauss_sqrt hd hj z
  have hEeq : -((graphNorm z : ℝ)) ^ 2 / (8 * ((j : ℝ) + 2 * (d : ℝ))) = -u := by
    rw [hu, ← hn]; ring
  rw [hEeq] at hgauss
  refine hgauss.trans ?_
  have hstep : diagConst d / S ^ d
      * Real.exp (-u)
      ≤ diagConst d / S ^ d
        * (8 * (d : ℝ) * (1 + 2 * (d : ℝ)) * (j : ℝ) / n ^ 2) ^ d := by
    exact mul_le_mul_of_nonneg_left hexp2
      (div_nonneg (diagConst_pos d).le (by positivity))
  refine hstep.trans ?_
  have h1 : (8 * (d : ℝ) * (1 + 2 * (d : ℝ)) * (j : ℝ) / n ^ 2) ^ d
      = (8 * (d : ℝ) * (1 + 2 * (d : ℝ))) ^ d * (j : ℝ) ^ d / (n ^ 2) ^ d := by
    rw [div_pow, mul_pow (8 * (d : ℝ) * (1 + 2 * (d : ℝ))) ((j : ℝ)) d]
  have h2 : ((j : ℝ)) ^ d = S ^ d * S ^ d := by rw [← mul_pow, hSsq]
  have h3 : ((n : ℝ) ^ 2) ^ d = n ^ d * n ^ d := by rw [← pow_mul, two_mul, pow_add]
  have hSdne : (S : ℝ) ^ d ≠ 0 := by positivity
  have hndne : (n : ℝ) ^ d ≠ 0 := by positivity
  have hrw : diagConst d / S ^ d
      * (8 * (d : ℝ) * (1 + 2 * (d : ℝ)) * (j : ℝ) / n ^ 2) ^ d
      = nearConst d * (S ^ d / (n ^ d * n ^ d)) := by
    rw [h1, h2, h3, nearConst]
    field_simp
  rw [hrw]
  have hSd : S ^ d ≤ n ^ d := pow_le_pow_left₀ hSpos.le hSn d
  have hnd : (0 : ℝ) < n ^ d := pow_pos hnpos d
  have hfrac : S ^ d / (n ^ d * n ^ d) ≤ 1 / n ^ d := by
    rw [div_le_div_iff₀ (by positivity) hnd]
    nlinarith
  calc nearConst d * (S ^ d / (n ^ d * n ^ d))
      ≤ nearConst d * (1 / n ^ d) :=
        mul_le_mul_of_nonneg_left hfrac (nearConst_pos hd).le
    _ = nearConst d / n ^ d := by rw [mul_one_div]

/-! ### The pointwise Green bound -/

/-- The partial sums of the kernel at a site away from the origin, uniformly in
the horizon: `∑_{j<M} p_j(0,z) ≤ (nearConst + 2 diagConst)/|z|^{d-2}`.  The split
is at `j = |z|^2`; the near times use `srwHeat_near_le` and the far times the
time tail `sum_Ico_srwHeat_high_le`. -/
theorem sum_range_srwHeat_le {k : ℕ} {z : Site (k + 4)} (hz : 1 ≤ graphNorm z) (M : ℕ) :
    ∑ j ∈ Finset.range M, srwHeat (k + 4) j z
      ≤ (nearConst (k + 4) + 2 * diagConst (k + 4)) / (graphNorm z : ℝ) ^ (k + 2) := by
  have hd : 0 < k + 4 := by omega
  have hnpos : (0 : ℝ) < ((graphNorm z : ℕ) : ℝ) := by exact_mod_cast hz
  have hzne : z ≠ 0 := fun h => by simp [h] at hz
  have hm1 : 1 ≤ graphNorm z ^ 2 + 1 := by omega
  have hmM' : graphNorm z ^ 2 + 1 ≤ max M (graphNorm z ^ 2 + 1) := le_max_right _ _
  have hMM' : M ≤ max M (graphNorm z ^ 2 + 1) := le_max_left _ _
  -- pass to the larger horizon
  have hstep1 : ∑ j ∈ Finset.range M, srwHeat (k + 4) j z
      ≤ ∑ j ∈ Finset.range (max M (graphNorm z ^ 2 + 1)), srwHeat (k + 4) j z :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hMM'))
      fun j _ _ => srwHeat_nonneg j z
  -- split the larger horizon
  have hsplit : ∑ j ∈ Finset.range (max M (graphNorm z ^ 2 + 1)), srwHeat (k + 4) j z
      = ∑ j ∈ Finset.Ico 0 1, srwHeat (k + 4) j z
        + ∑ j ∈ Finset.Ico 1 (graphNorm z ^ 2 + 1), srwHeat (k + 4) j z
        + ∑ j ∈ Finset.Ico (graphNorm z ^ 2 + 1) (max M (graphNorm z ^ 2 + 1)),
            srwHeat (k + 4) j z := by
    rw [Finset.sum_Ico_consecutive _ (by omega : (0:ℕ) ≤ 1) hm1,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) hmM', Finset.range_eq_Ico]
  have hzero : ∑ j ∈ Finset.Ico 0 1, srwHeat (k + 4) j z = 0 := by
    rw [Nat.Ico_zero_eq_range, Finset.sum_range_one, srwHeat_zero, if_neg hzne]
  -- the near times
  have hnear : ∑ j ∈ Finset.Ico 1 (graphNorm z ^ 2 + 1), srwHeat (k + 4) j z
      ≤ nearConst (k + 4) / ((graphNorm z : ℕ) : ℝ) ^ (k + 2) := by
    have hterm : ∀ j ∈ Finset.Ico 1 (graphNorm z ^ 2 + 1),
        srwHeat (k + 4) j z ≤ nearConst (k + 4) / ((graphNorm z : ℕ) : ℝ) ^ (k + 4) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      exact srwHeat_near_le hd hz hj.1 (by omega)
    have hcard : (Finset.Ico 1 (graphNorm z ^ 2 + 1)).card = graphNorm z ^ 2 := by
      rw [Nat.card_Ico]; omega
    have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [hcard, nsmul_eq_mul] at hsum
    refine hsum.trans ?_
    have hcast : (((graphNorm z ^ 2 : ℕ) : ℝ)) = ((graphNorm z : ℕ) : ℝ) ^ 2 := by
      push_cast; ring
    rw [hcast]
    have hpow : ((graphNorm z : ℕ) : ℝ) ^ (k + 4)
        = ((graphNorm z : ℕ) : ℝ) ^ (k + 2) * ((graphNorm z : ℕ) : ℝ) ^ 2 := by
      rw [← pow_add]
    have hne : ((graphNorm z : ℕ) : ℝ) ≠ 0 := ne_of_gt hnpos
    rw [hpow]
    rw [show ((graphNorm z : ℕ) : ℝ) ^ 2
        * (nearConst (k + 4)
          / (((graphNorm z : ℕ) : ℝ) ^ (k + 2) * ((graphNorm z : ℕ) : ℝ) ^ 2))
        = nearConst (k + 4) / ((graphNorm z : ℕ) : ℝ) ^ (k + 2) from by
      field_simp]
  -- the far times
  have hfar : ∑ j ∈ Finset.Ico (graphNorm z ^ 2 + 1) (max M (graphNorm z ^ 2 + 1)),
        srwHeat (k + 4) j z
      ≤ 2 * diagConst (k + 4) / ((graphNorm z : ℕ) : ℝ) ^ (k + 2) := by
    have h := sum_Ico_srwHeat_high_le (k := k) (m := graphNorm z ^ 2 + 1) hm1
      (max M (graphNorm z ^ 2 + 1)) z
    refine h.trans ?_
    have hmge : (((graphNorm z : ℕ) : ℝ)) ^ 2 ≤ ((graphNorm z ^ 2 + 1 : ℕ) : ℝ) := by
      push_cast; nlinarith
    have hmpos : (0 : ℝ) < ((graphNorm z ^ 2 + 1 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((graphNorm z ^ 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hm1
      linarith
    have hsq : ((graphNorm z : ℕ) : ℝ) ≤ Real.sqrt ((graphNorm z ^ 2 + 1 : ℕ) : ℝ) := by
      rw [show ((graphNorm z : ℕ) : ℝ)
          = Real.sqrt (((graphNorm z : ℕ) : ℝ) ^ 2) from (Real.sqrt_sq hnpos.le).symm]
      exact Real.sqrt_le_sqrt hmge
    have hk : ((graphNorm z : ℕ) : ℝ) ^ k
        ≤ Real.sqrt ((graphNorm z ^ 2 + 1 : ℕ) : ℝ) ^ k :=
      pow_le_pow_left₀ hnpos.le hsq k
    have hmn : ((graphNorm z : ℕ) : ℝ) ^ (k + 2)
        ≤ ((graphNorm z ^ 2 + 1 : ℕ) : ℝ)
          * Real.sqrt ((graphNorm z ^ 2 + 1 : ℕ) : ℝ) ^ k := by
      calc ((graphNorm z : ℕ) : ℝ) ^ (k + 2)
          = ((graphNorm z : ℕ) : ℝ) ^ 2 * ((graphNorm z : ℕ) : ℝ) ^ k := by ring
        _ ≤ ((graphNorm z ^ 2 + 1 : ℕ) : ℝ)
              * Real.sqrt ((graphNorm z ^ 2 + 1 : ℕ) : ℝ) ^ k := by
            refine mul_le_mul hmge hk (by positivity) hmpos.le
    have hden : (0 : ℝ) < ((graphNorm z ^ 2 + 1 : ℕ) : ℝ)
        * Real.sqrt ((graphNorm z ^ 2 + 1 : ℕ) : ℝ) ^ k := by
      have : (0 : ℝ) < Real.sqrt ((graphNorm z ^ 2 + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hmpos
      positivity
    have hnnpos : (0 : ℝ) < ((graphNorm z : ℕ) : ℝ) ^ (k + 2) := by positivity
    rw [mul_div_assoc']
    rw [div_le_div_iff₀ hden hnnpos]
    nlinarith [(diagConst_pos (k + 4)).le, hmn, hnnpos, hden]
  rw [hsplit, hzero, zero_add] at hstep1
  refine hstep1.trans ?_
  have hcomb : nearConst (k + 4) / ((graphNorm z : ℕ) : ℝ) ^ (k + 2)
      + 2 * diagConst (k + 4) / ((graphNorm z : ℕ) : ℝ) ^ (k + 2)
      = (nearConst (k + 4) + 2 * diagConst (k + 4))
        / ((graphNorm z : ℕ) : ℝ) ^ (k + 2) := by ring
  linarith [hnear, hfar]

/-- **The pointwise Green bound above dimension four**:
`G(0,z) ≤ C (1+|z|_1)^{2-d}`, with `|z|_1` the graph norm, which is at least the
Euclidean norm, so this is the stronger form of the bound. -/
theorem exists_srwGreenInf_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Site (k + 4),
      srwGreenInf (k + 4) z ≤ C / (1 + (graphNorm z : ℝ)) ^ (k + 2) := by
  have hd3 : 3 ≤ k + 4 := by omega
  set A : ℝ := nearConst (k + 4) + 2 * diagConst (k + 4) with hA
  have hApos : 0 < A := by
    have := nearConst_pos (d := k + 4) (by omega)
    have := diagConst_pos (k + 4)
    rw [hA]; linarith
  set C₀ : ℝ := 1 + 3 * (Real.sqrt 2 ^ (k + 4) * greenConst (k + 4)) with hC₀
  have hC₀pos : 0 < C₀ := by
    have := srwGreenConst_nonneg (k + 4)
    rw [hC₀]; linarith
  refine ⟨2 ^ (k + 2) * A + C₀, by positivity, fun z => ?_⟩
  rcases Nat.eq_zero_or_pos (graphNorm z) with hz | hz
  · -- the origin
    have hz0 : z = 0 := graphNorm_eq_zero_iff.mp hz
    subst hz0
    have hbound : ∀ M : ℕ, ∑ j ∈ Finset.range M, srwHeat (k + 4) j (0 : Site (k + 4)) ≤ C₀ := by
      intro M
      rcases Nat.eq_zero_or_pos M with rfl | hM
      · simpa using hC₀pos.le
      · exact srwGreen_high_dim_le hd3 M hM (0 : Site (k + 4))
    have := Real.tsum_le_of_sum_range_le (fun j => srwHeat_nonneg j (0 : Site (k + 4))) hbound
    have hgn : ((graphNorm (0 : Site (k + 4)) : ℕ) : ℝ) = 0 := by simp
    rw [srwGreenInf, hgn]
    simpa using this.trans (by nlinarith [hApos, (by positivity : (0:ℝ) < (2:ℝ) ^ (k + 2))])
  · -- away from the origin
    have hnpos : (0 : ℝ) < ((graphNorm z : ℕ) : ℝ) := by exact_mod_cast hz
    have hsum := Real.tsum_le_of_sum_range_le (fun j => srwHeat_nonneg j z)
      (fun M => sum_range_srwHeat_le hz M)
    refine hsum.trans ?_
    have h1n : (1 : ℝ) + ((graphNorm z : ℕ) : ℝ) ≤ 2 * ((graphNorm z : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((graphNorm z : ℕ) : ℝ) := by exact_mod_cast hz
      linarith
    have hpow : (1 + ((graphNorm z : ℕ) : ℝ)) ^ (k + 2)
        ≤ 2 ^ (k + 2) * ((graphNorm z : ℕ) : ℝ) ^ (k + 2) := by
      have := pow_le_pow_left₀ (by positivity) h1n (k + 2)
      rwa [mul_pow] at this
    have hdenpos : (0 : ℝ) < (1 + ((graphNorm z : ℕ) : ℝ)) ^ (k + 2) := by positivity
    have hnnpos : (0 : ℝ) < ((graphNorm z : ℕ) : ℝ) ^ (k + 2) := by positivity
    rw [div_le_div_iff₀ hnnpos hdenpos]
    have hC₀nn : 0 ≤ C₀ := hC₀pos.le
    nlinarith [hpow, hApos, hnnpos, hdenpos, hC₀nn,
      mul_nonneg hC₀nn hnnpos.le, mul_nonneg hApos.le hnnpos.le]

/-! ### The Euclidean form, and square summability -/

/-- The Euclidean norm is at most the graph norm. -/
theorem euclidNorm_le_graphNorm (x : Site d) : euclidNorm x ≤ ((graphNorm x : ℕ) : ℝ) := by
  have habs : ((graphNorm x : ℕ) : ℝ) = ∑ i : Fin d, |((x i : ℤ) : ℝ)| := by
    rw [graphNorm]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by
      rw [Nat.cast_natAbs, Int.cast_abs]
  have hsq : ∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2
      ≤ (∑ i : Fin d, |((x i : ℤ) : ℝ)|) ^ 2 := by
    have := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset (Fin d))) (f := fun i => |((x i : ℤ) : ℝ)|)
      (fun i _ => abs_nonneg _)
    simpa [sq_abs] using this
  have hnn : (0 : ℝ) ≤ ∑ i : Fin d, |((x i : ℤ) : ℝ)| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [euclidNorm, habs]
  calc Real.sqrt (∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2)
      ≤ Real.sqrt ((∑ i : Fin d, |((x i : ℤ) : ℝ)|) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ i : Fin d, |((x i : ℤ) : ℝ)| := Real.sqrt_sq hnn

/-- The pointwise Green bound in the Euclidean norm of the notation section. -/
theorem exists_srwGreenInf_euclid_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Site (k + 4),
      srwGreenInf (k + 4) z ≤ C / (1 + euclidNorm z) ^ (k + 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_srwGreenInf_le k
  refine ⟨C, hC, fun z => ?_⟩
  refine (hbound z).trans ?_
  have h1 : (0 : ℝ) < 1 + euclidNorm z := by linarith [euclidNorm_nonneg z]
  have h2 : (1 : ℝ) + euclidNorm z ≤ 1 + ((graphNorm z : ℕ) : ℝ) := by
    linarith [euclidNorm_le_graphNorm z]
  exact div_le_div_of_nonneg_left hC.le (by positivity)
    (pow_le_pow_left₀ h1.le h2 (k + 2))

/-- **The Green function is square summable above dimension four**, which is
`eq:dgt4-green-l2`. -/
theorem summable_srwGreenInf_sq (k : ℕ) :
    Summable fun z : Site (k + 5) => srwGreenInf (k + 5) z ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_srwGreenInf_euclid_le (k + 1)
  have hdim : (((k + 5 : ℕ)) : ℝ) < 2 * (k : ℝ) + 6 := by push_cast; linarith
  have hsum := (summable_one_add_euclidNorm_rpow (k + 5) hdim).mul_left (C ^ 2)
  refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_) hsum
  have h1 : (0 : ℝ) < 1 + euclidNorm z := by linarith [euclidNorm_nonneg z]
  have hb : srwGreenInf (k + 5) z ≤ C / (1 + euclidNorm z) ^ (k + 3) := hbound z
  have hnn : 0 ≤ srwGreenInf (k + 5) z :=
    tsum_nonneg fun j => srwHeat_nonneg j z
  have hsq : srwGreenInf (k + 5) z ^ 2 ≤ (C / (1 + euclidNorm z) ^ (k + 3)) ^ 2 := by
    exact pow_le_pow_left₀ hnn hb 2
  refine hsq.trans (le_of_eq ?_)
  rw [div_pow, ← pow_mul]
  rw [show C ^ 2 * (1 + euclidNorm z) ^ (-(2 * (k : ℝ) + 6))
      = C ^ 2 / (1 + euclidNorm z) ^ (2 * (k : ℝ) + 6) from by
    rw [Real.rpow_neg h1.le, div_eq_mul_inv]]
  congr 1
  rw [show ((k + 3) * 2 : ℕ) = ((2 * k + 6 : ℕ)) from by ring,
    ← Real.rpow_natCast (1 + euclidNorm z) (2 * k + 6)]
  congr 1
  push_cast
  ring

/-! ### The time-weighted kernel sum -/

/-- `∑_{m ≤ s < N} (√s)^{-(k+2)} ≤ 6 (√m)^{-k}` for `k ≥ 1`: the extra `k-1`
powers of `√s` are estimated at `s = m` and what is left is the `3/2` series. -/
theorem sum_Ico_inv_sqrt_pow_le' {k : ℕ} (hk : 1 ≤ k) {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ s ∈ Finset.Ico m N, (Real.sqrt (s : ℝ) ^ (k + 2))⁻¹
      ≤ 6 / Real.sqrt (m : ℝ) ^ k := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  have hterm : ∀ s ∈ Finset.Ico m N,
      (Real.sqrt (s : ℝ) ^ (k + 2))⁻¹
        ≤ (Real.sqrt (m : ℝ) ^ (k - 1))⁻¹ * (((s : ℝ)) * Real.sqrt (s : ℝ))⁻¹ := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hs1 : 1 ≤ s := le_trans hm hs.1
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
    have hss : (m : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs.1
    have hsps : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hspos
    have hmono : Real.sqrt (m : ℝ) ^ (k - 1) ≤ Real.sqrt (s : ℝ) ^ (k - 1) :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hss) (k - 1)
    have hfac : Real.sqrt (s : ℝ) ^ (k + 2)
        = Real.sqrt (s : ℝ) ^ (k - 1) * ((s : ℝ) * Real.sqrt (s : ℝ)) := by
      have h3 : Real.sqrt (s : ℝ) ^ 3 = (s : ℝ) * Real.sqrt (s : ℝ) := by
        rw [pow_succ, Real.sq_sqrt hspos.le]
      rw [← h3, ← pow_add]
      congr 1
      omega
    rw [hfac, mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact inv_anti₀ (by positivity) hmono
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h := sum_Ico_inv_mul_sqrt_le hm N
  have hkm : Real.sqrt (m : ℝ) ^ (k - 1) * Real.sqrt (m : ℝ) = Real.sqrt (m : ℝ) ^ k := by
    rw [← pow_succ]
    congr 1
    omega
  calc (Real.sqrt (m : ℝ) ^ (k - 1))⁻¹
        * ∑ s ∈ Finset.Ico m N, (((s : ℝ)) * Real.sqrt (s : ℝ))⁻¹
      ≤ (Real.sqrt (m : ℝ) ^ (k - 1))⁻¹ * (6 / Real.sqrt (m : ℝ)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 6 / Real.sqrt (m : ℝ) ^ k := by
        rw [← hkm]
        field_simp

/-- The weighted kernel past the split time: `(s+1) p_s(v) ≤ 2C (√s)^{-(k+3)}`,
uniformly in the site. -/
theorem weighted_srwHeat_far_le (k : ℕ) {s : ℕ} (hs : 1 ≤ s) (v : Site (k + 5)) :
    ((s : ℝ) + 1) * srwHeat (k + 5) s v
      ≤ 2 * diagConst (k + 5) * (Real.sqrt (s : ℝ) ^ ((k + 1) + 2))⁻¹ := by
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hsq : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hspos
  have hker := srwHeat_sup_le (d := k + 5) (by omega) hs v
  have hnn : 0 ≤ srwHeat (k + 5) s v := srwHeat_nonneg s v
  have hsplit : (s : ℝ) + 1 ≤ 2 * (s : ℝ) := by linarith
  have hstep : ((s : ℝ) + 1) * srwHeat (k + 5) s v
      ≤ 2 * (s : ℝ) * (diagConst (k + 5) / Real.sqrt (s : ℝ) ^ (k + 5)) := by
    have h1 : ((s : ℝ) + 1) * srwHeat (k + 5) s v ≤ 2 * (s : ℝ) * srwHeat (k + 5) s v :=
      mul_le_mul_of_nonneg_right hsplit hnn
    refine h1.trans (mul_le_mul_of_nonneg_left hker (by linarith))
  refine hstep.trans (le_of_eq ?_)
  have hpow : Real.sqrt (s : ℝ) ^ (k + 5)
      = Real.sqrt (s : ℝ) ^ ((k + 1) + 2) * (s : ℝ) := by
    rw [show (k + 5) = ((k + 1) + 2) + 2 from by omega, pow_add, Real.sq_sqrt hspos.le]
  rw [hpow]
  have h1 : Real.sqrt (s : ℝ) ^ ((k + 1) + 2) ≠ 0 := by positivity
  field_simp

/-- **The time-weighted kernel sum at the origin.** -/
theorem sum_range_weighted_zero (k : ℕ) (M : ℕ) :
    ∑ s ∈ Finset.range M, ((s : ℝ) + 1) * srwHeat (k + 5) s (0 : Site (k + 5))
      ≤ 1 + 12 * diagConst (k + 5) := by
  have hDpos : (0 : ℝ) < diagConst (k + 5) := diagConst_pos _
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [Finset.range_zero, Finset.sum_empty]
    linarith
  have hsplit : ∑ s ∈ Finset.range M, ((s : ℝ) + 1) * srwHeat (k + 5) s (0 : Site (k + 5))
      = ∑ s ∈ Finset.Ico (0 : ℕ) 1, ((s : ℝ) + 1) * srwHeat (k + 5) s (0 : Site (k + 5))
        + ∑ s ∈ Finset.Ico (1 : ℕ) M, ((s : ℝ) + 1) * srwHeat (k + 5) s (0 : Site (k + 5)) := by
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) hM, Finset.range_eq_Ico]
  have hfirst : ∑ s ∈ Finset.Ico (0 : ℕ) 1,
      ((s : ℝ) + 1) * srwHeat (k + 5) s (0 : Site (k + 5)) = 1 := by
    rw [Nat.Ico_zero_eq_range, Finset.sum_range_one, srwHeat_zero]
    norm_num
  have htail : ∑ s ∈ Finset.Ico (1 : ℕ) M,
      ((s : ℝ) + 1) * srwHeat (k + 5) s (0 : Site (k + 5)) ≤ 12 * diagConst (k + 5) := by
    have hterm : ∀ s ∈ Finset.Ico (1 : ℕ) M,
        ((s : ℝ) + 1) * srwHeat (k + 5) s (0 : Site (k + 5))
          ≤ 2 * diagConst (k + 5) * (Real.sqrt (s : ℝ) ^ ((k + 1) + 2))⁻¹ :=
      fun s hs => weighted_srwHeat_far_le k (Finset.mem_Ico.mp hs).1 _
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have h := sum_Ico_inv_sqrt_pow_le' (k := k + 1) (by omega) (m := 1) le_rfl M
    have hone : Real.sqrt (((1 : ℕ) : ℝ)) ^ (k + 1) = 1 := by norm_num
    rw [hone] at h
    calc 2 * diagConst (k + 5)
          * ∑ s ∈ Finset.Ico (1 : ℕ) M, (Real.sqrt (s : ℝ) ^ ((k + 1) + 2))⁻¹
        ≤ 2 * diagConst (k + 5) * (6 / 1) :=
          mul_le_mul_of_nonneg_left h (by linarith)
      _ = 12 * diagConst (k + 5) := by ring
  rw [hsplit, hfirst]
  linarith

/-- **The time-weighted kernel sum away from the origin**, uniformly in the
horizon: `∑_{s<M} (s+1) p_s(v) ≤ C |v|^{4-d}`.  The split is at `s = |v|^2`;
before it the weight is at most `2|v|^2` and the kernel is `nearConst/|v|^d`,
and after it the weight is absorbed into the exponent. -/
theorem sum_range_weighted_ne (k : ℕ) {v : Site (k + 5)} (hv : 1 ≤ graphNorm v) (M : ℕ) :
    ∑ s ∈ Finset.range M, ((s : ℝ) + 1) * srwHeat (k + 5) s v
      ≤ (2 * nearConst (k + 5) + 12 * diagConst (k + 5))
        / ((graphNorm v : ℕ) : ℝ) ^ (k + 1) := by
  have hd : 0 < k + 5 := by omega
  have hnpos : (0 : ℝ) < ((graphNorm v : ℕ) : ℝ) := by exact_mod_cast hv
  have hn1 : (1 : ℝ) ≤ ((graphNorm v : ℕ) : ℝ) := by exact_mod_cast hv
  have hvne : v ≠ 0 := fun h => by simp [h] at hv
  have hm1 : 1 ≤ graphNorm v ^ 2 + 1 := by omega
  have hMM' : M ≤ max M (graphNorm v ^ 2 + 1) := le_max_left _ _
  have hmM' : graphNorm v ^ 2 + 1 ≤ max M (graphNorm v ^ 2 + 1) := le_max_right _ _
  have hstep1 : ∑ s ∈ Finset.range M, ((s : ℝ) + 1) * srwHeat (k + 5) s v
      ≤ ∑ s ∈ Finset.range (max M (graphNorm v ^ 2 + 1)),
          ((s : ℝ) + 1) * srwHeat (k + 5) s v :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hMM'))
      fun s _ _ => mul_nonneg (by positivity) (srwHeat_nonneg s v)
  have hsplit : ∑ s ∈ Finset.range (max M (graphNorm v ^ 2 + 1)),
        ((s : ℝ) + 1) * srwHeat (k + 5) s v
      = ∑ s ∈ Finset.Ico (0 : ℕ) 1, ((s : ℝ) + 1) * srwHeat (k + 5) s v
        + ∑ s ∈ Finset.Ico (1 : ℕ) (graphNorm v ^ 2 + 1),
            ((s : ℝ) + 1) * srwHeat (k + 5) s v
        + ∑ s ∈ Finset.Ico (graphNorm v ^ 2 + 1) (max M (graphNorm v ^ 2 + 1)),
            ((s : ℝ) + 1) * srwHeat (k + 5) s v := by
    rw [Finset.sum_Ico_consecutive _ (by omega : (0:ℕ) ≤ 1) hm1,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) hmM', Finset.range_eq_Ico]
  have hzero : ∑ s ∈ Finset.Ico (0 : ℕ) 1, ((s : ℝ) + 1) * srwHeat (k + 5) s v = 0 := by
    rw [Nat.Ico_zero_eq_range, Finset.sum_range_one, srwHeat_zero, if_neg hvne]
    ring
  -- the near times
  have hnear : ∑ s ∈ Finset.Ico (1 : ℕ) (graphNorm v ^ 2 + 1),
        ((s : ℝ) + 1) * srwHeat (k + 5) s v
      ≤ 2 * nearConst (k + 5) / ((graphNorm v : ℕ) : ℝ) ^ (k + 1) := by
    have hterm : ∀ s ∈ Finset.Ico (1 : ℕ) (graphNorm v ^ 2 + 1),
        ((s : ℝ) + 1) * srwHeat (k + 5) s v
          ≤ 2 * ((graphNorm v : ℕ) : ℝ) ^ 2
            * (nearConst (k + 5) / ((graphNorm v : ℕ) : ℝ) ^ (k + 5)) := by
      intro s hs
      rw [Finset.mem_Ico] at hs
      have hker := srwHeat_near_le hd hv hs.1 (by omega)
      have hsle : ((s : ℝ) + 1) ≤ 2 * ((graphNorm v : ℕ) : ℝ) ^ 2 := by
        have : (s : ℝ) ≤ ((graphNorm v ^ 2 : ℕ) : ℝ) := by
          have : s ≤ graphNorm v ^ 2 := by omega
          exact_mod_cast this
        have hcast : (((graphNorm v ^ 2 : ℕ)) : ℝ) = ((graphNorm v : ℕ) : ℝ) ^ 2 := by
          push_cast; ring
        rw [hcast] at this
        nlinarith
      have hnn : 0 ≤ srwHeat (k + 5) s v := srwHeat_nonneg s v
      calc ((s : ℝ) + 1) * srwHeat (k + 5) s v
          ≤ 2 * ((graphNorm v : ℕ) : ℝ) ^ 2 * srwHeat (k + 5) s v :=
            mul_le_mul_of_nonneg_right hsle hnn
        _ ≤ 2 * ((graphNorm v : ℕ) : ℝ) ^ 2
              * (nearConst (k + 5) / ((graphNorm v : ℕ) : ℝ) ^ (k + 5)) :=
            mul_le_mul_of_nonneg_left hker (by positivity)
    have hcard : (Finset.Ico (1 : ℕ) (graphNorm v ^ 2 + 1)).card = graphNorm v ^ 2 := by
      rw [Nat.card_Ico]; omega
    have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [hcard, nsmul_eq_mul] at hsum
    refine hsum.trans (le_of_eq ?_)
    have hcast : (((graphNorm v ^ 2 : ℕ)) : ℝ) = ((graphNorm v : ℕ) : ℝ) ^ 2 := by
      push_cast; ring
    rw [hcast]
    have hpow : ((graphNorm v : ℕ) : ℝ) ^ (k + 5)
        = ((graphNorm v : ℕ) : ℝ) ^ (k + 1) * ((graphNorm v : ℕ) : ℝ) ^ 2
          * ((graphNorm v : ℕ) : ℝ) ^ 2 := by
      rw [← pow_add, ← pow_add]
    rw [hpow]
    have hne : ((graphNorm v : ℕ) : ℝ) ≠ 0 := ne_of_gt hnpos
    field_simp
  -- the far times
  have hfar : ∑ s ∈ Finset.Ico (graphNorm v ^ 2 + 1) (max M (graphNorm v ^ 2 + 1)),
        ((s : ℝ) + 1) * srwHeat (k + 5) s v
      ≤ 12 * diagConst (k + 5) / ((graphNorm v : ℕ) : ℝ) ^ (k + 1) := by
    have hterm : ∀ s ∈ Finset.Ico (graphNorm v ^ 2 + 1) (max M (graphNorm v ^ 2 + 1)),
        ((s : ℝ) + 1) * srwHeat (k + 5) s v
          ≤ 2 * diagConst (k + 5) * (Real.sqrt (s : ℝ) ^ ((k + 1) + 2))⁻¹ := by
      intro s hs
      exact weighted_srwHeat_far_le k (by have := (Finset.mem_Ico.mp hs).1; omega) v
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have h := sum_Ico_inv_sqrt_pow_le' (k := k + 1) (by omega) hm1
      (max M (graphNorm v ^ 2 + 1))
    have hmge : ((graphNorm v : ℕ) : ℝ) ^ 2 ≤ ((graphNorm v ^ 2 + 1 : ℕ) : ℝ) := by
      push_cast; nlinarith
    have hmpos : (0 : ℝ) < ((graphNorm v ^ 2 + 1 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((graphNorm v ^ 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hm1
      linarith
    have hsq : ((graphNorm v : ℕ) : ℝ) ≤ Real.sqrt ((graphNorm v ^ 2 + 1 : ℕ) : ℝ) := by
      rw [show ((graphNorm v : ℕ) : ℝ)
          = Real.sqrt (((graphNorm v : ℕ) : ℝ) ^ 2) from (Real.sqrt_sq hnpos.le).symm]
      exact Real.sqrt_le_sqrt hmge
    have hk1 : ((graphNorm v : ℕ) : ℝ) ^ (k + 1)
        ≤ Real.sqrt ((graphNorm v ^ 2 + 1 : ℕ) : ℝ) ^ (k + 1) :=
      pow_le_pow_left₀ hnpos.le hsq (k + 1)
    have hpos1 : (0 : ℝ) < ((graphNorm v : ℕ) : ℝ) ^ (k + 1) := by positivity
    have hpos2 : (0 : ℝ) < Real.sqrt ((graphNorm v ^ 2 + 1 : ℕ) : ℝ) ^ (k + 1) := by
      have : (0 : ℝ) < Real.sqrt ((graphNorm v ^ 2 + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hmpos
      positivity
    have hdiv : (6 : ℝ) / Real.sqrt ((graphNorm v ^ 2 + 1 : ℕ) : ℝ) ^ (k + 1)
        ≤ 6 / ((graphNorm v : ℕ) : ℝ) ^ (k + 1) :=
      div_le_div_of_nonneg_left (by norm_num) hpos1 hk1
    calc 2 * diagConst (k + 5)
          * ∑ s ∈ Finset.Ico (graphNorm v ^ 2 + 1) (max M (graphNorm v ^ 2 + 1)),
              (Real.sqrt (s : ℝ) ^ ((k + 1) + 2))⁻¹
        ≤ 2 * diagConst (k + 5)
            * (6 / Real.sqrt ((graphNorm v ^ 2 + 1 : ℕ) : ℝ) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left h (by linarith [(diagConst_pos (k + 5)).le])
      _ ≤ 2 * diagConst (k + 5) * (6 / ((graphNorm v : ℕ) : ℝ) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hdiv (by linarith [(diagConst_pos (k + 5)).le])
      _ = 12 * diagConst (k + 5) / ((graphNorm v : ℕ) : ℝ) ^ (k + 1) := by ring
  rw [hsplit, hzero, zero_add] at hstep1
  refine hstep1.trans ?_
  have : 2 * nearConst (k + 5) / ((graphNorm v : ℕ) : ℝ) ^ (k + 1)
      + 12 * diagConst (k + 5) / ((graphNorm v : ℕ) : ℝ) ^ (k + 1)
      = (2 * nearConst (k + 5) + 12 * diagConst (k + 5))
        / ((graphNorm v : ℕ) : ℝ) ^ (k + 1) := by ring
  linarith [hnear, hfar]

/-- **The time-weighted kernel sum**, `∑_s (s+1) p_s(v) ≤ C (1+|v|)^{4-d}` in
dimension `d = k+5`, with its summability. -/
theorem exists_tsum_weighted_srwHeat_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Site (k + 5),
      (Summable fun s : ℕ => ((s : ℝ) + 1) * srwHeat (k + 5) s v) ∧
        (∑' s : ℕ, ((s : ℝ) + 1) * srwHeat (k + 5) s v)
          ≤ C / (1 + ((graphNorm v : ℕ) : ℝ)) ^ (k + 1) := by
  have hDpos : (0 : ℝ) < diagConst (k + 5) := diagConst_pos _
  have hNpos : (0 : ℝ) < nearConst (k + 5) := nearConst_pos (by omega)
  set A : ℝ := 2 * nearConst (k + 5) + 12 * diagConst (k + 5) with hA
  have hApos : 0 < A := by rw [hA]; linarith
  set B : ℝ := 1 + 12 * diagConst (k + 5) with hB
  have hBpos : 0 < B := by rw [hB]; linarith
  refine ⟨2 ^ (k + 1) * A + B, by positivity, fun v => ?_⟩
  have hnn : ∀ s : ℕ, 0 ≤ ((s : ℝ) + 1) * srwHeat (k + 5) s v :=
    fun s => mul_nonneg (by positivity) (srwHeat_nonneg s v)
  rcases Nat.eq_zero_or_pos (graphNorm v) with hz | hz
  · have hv0 : v = 0 := graphNorm_eq_zero_iff.mp hz
    subst hv0
    have hbound : ∀ M : ℕ,
        ∑ s ∈ Finset.range M, ((s : ℝ) + 1) * srwHeat (k + 5) s (0 : Site (k + 5)) ≤ B :=
      fun M => sum_range_weighted_zero k M
    refine ⟨summable_of_sum_range_le hnn hbound, ?_⟩
    have hgn : ((graphNorm (0 : Site (k + 5)) : ℕ) : ℝ) = 0 := by simp
    rw [hgn]
    have := Real.tsum_le_of_sum_range_le hnn hbound
    have h2 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    simpa using this.trans (by nlinarith)
  · have hnpos : (0 : ℝ) < ((graphNorm v : ℕ) : ℝ) := by exact_mod_cast hz
    have hbound : ∀ M : ℕ,
        ∑ s ∈ Finset.range M, ((s : ℝ) + 1) * srwHeat (k + 5) s v
          ≤ A / ((graphNorm v : ℕ) : ℝ) ^ (k + 1) :=
      fun M => sum_range_weighted_ne k hz M
    refine ⟨summable_of_sum_range_le hnn hbound, ?_⟩
    refine (Real.tsum_le_of_sum_range_le hnn hbound).trans ?_
    have h1n : (1 : ℝ) + ((graphNorm v : ℕ) : ℝ) ≤ 2 * ((graphNorm v : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((graphNorm v : ℕ) : ℝ) := by exact_mod_cast hz
      linarith
    have hpow : (1 + ((graphNorm v : ℕ) : ℝ)) ^ (k + 1)
        ≤ 2 ^ (k + 1) * ((graphNorm v : ℕ) : ℝ) ^ (k + 1) := by
      have := pow_le_pow_left₀ (by positivity) h1n (k + 1)
      rwa [mul_pow] at this
    have hdenpos : (0 : ℝ) < (1 + ((graphNorm v : ℕ) : ℝ)) ^ (k + 1) := by positivity
    have hnnpos : (0 : ℝ) < ((graphNorm v : ℕ) : ℝ) ^ (k + 1) := by positivity
    rw [div_le_div_iff₀ hnnpos hdenpos]
    nlinarith [hpow, hApos, hnnpos, hdenpos, hBpos, mul_nonneg hBpos.le hnnpos.le]

/-! ### The intersection estimate `∑_z G(x,z) G(y,z)` -/

/-- The shifted `ℓ²` pairing of two kernels:
`∑_z p_a(0,z) p_b(0,z+u) = p_{a+b}(0,u)`. -/
theorem tsum_srwHeat_mul_shift (a b : ℕ) (u : Site d) :
    ∑' z : Site d, srwHeat d a z * srwHeat d b (z + u) = srwHeat d (a + b) u := by
  rw [← srwHeat_neg (a + b) u, srwHeat_add a b (-u)]
  refine tsum_congr fun y => ?_
  rw [show (-u : Site d) - y = -(y + u) by abel, srwHeat_neg]

theorem summable_srwGreen_mul (m : ℕ) (f : Site d → ℝ) :
    Summable fun z : Site d => srwGreen d m z * f z := by
  have hrw : (fun z : Site d => srwGreen d m z * f z)
      = fun z : Site d => ∑ a ∈ Finset.range m, srwHeat d a z * f z := by
    funext z
    rw [srwGreen, Finset.sum_mul]
  rw [hrw]
  exact summable_sum fun a _ => summable_srwHeat_mul a f

/-- **The shifted correlation of two truncated Green functions.** -/
theorem tsum_srwGreen_mul_shift (m n : ℕ) (u : Site d) :
    ∑' z : Site d, srwGreen d m z * srwGreen d n (z + u)
      = ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n, srwHeat d (a + b) u := by
  have h1 : ∀ z : Site d, srwGreen d m z * srwGreen d n (z + u)
      = ∑ a ∈ Finset.range m, srwHeat d a z * srwGreen d n (z + u) := by
    intro z; rw [srwGreen, Finset.sum_mul]
  rw [tsum_congr h1,
    Summable.tsum_finsetSum
      (fun a _ => summable_srwHeat_mul a fun z => srwGreen d n (z + u))]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : ∀ z : Site d, srwHeat d a z * srwGreen d n (z + u)
      = ∑ b ∈ Finset.range n, srwHeat d a z * srwHeat d b (z + u) := by
    intro z; rw [srwGreen, Finset.mul_sum]
  rw [tsum_congr h2,
    Summable.tsum_finsetSum
      (fun b _ => summable_srwHeat_mul a fun z => srwHeat d b (z + u))]
  exact Finset.sum_congr rfl fun b _ => tsum_srwHeat_mul_shift a b u

/-- The truncated Green function converges to the Green function, in dimension
three and above. -/
theorem tendsto_srwGreen (hd : 3 ≤ d) (z : Site d) :
    Filter.Tendsto (fun m : ℕ => srwGreen d m z) Filter.atTop
      (nhds (srwGreenInf d z)) :=
  (summable_srwHeat hd z).hasSum.tendsto_sum_nat

/-- **The intersection estimate in Green form**:
`∑_z G(0,z) G(u,z) ≤ C (1+|u|)^{4-d}`, with its summability.  The identity
behind it is that the `ℓ²` pairing of two Green functions is the time-weighted
return probability `∑_s (s+1) p_s(u)`, which is the theorem above. -/
theorem exists_tsum_srwGreenInf_mul_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Site (k + 5),
      (Summable fun z : Site (k + 5) =>
          srwGreenInf (k + 5) z * srwGreenInf (k + 5) (z + u)) ∧
        (∑' z : Site (k + 5), srwGreenInf (k + 5) z * srwGreenInf (k + 5) (z + u))
          ≤ C / (1 + ((graphNorm u : ℕ) : ℝ)) ^ (k + 1) := by
  obtain ⟨C, hC, hW⟩ := exists_tsum_weighted_srwHeat_le k
  have hd3 : 3 ≤ k + 5 := by omega
  refine ⟨C, hC, fun u => ?_⟩
  set c : ℝ := C / (1 + ((graphNorm u : ℕ) : ℝ)) ^ (k + 1) with hc
  have hGnn : ∀ z : Site (k + 5), 0 ≤ srwGreenInf (k + 5) z :=
    fun z => tsum_nonneg fun j => srwHeat_nonneg j z
  have hnn : ∀ z : Site (k + 5),
      0 ≤ srwGreenInf (k + 5) z * srwGreenInf (k + 5) (z + u) :=
    fun z => mul_nonneg (hGnn z) (hGnn _)
  -- every finite partial sum is below the bound
  have hF : ∀ F : Finset (Site (k + 5)),
      ∑ z ∈ F, srwGreenInf (k + 5) z * srwGreenInf (k + 5) (z + u) ≤ c := by
    intro F
    have hlim : Filter.Tendsto
        (fun m : ℕ => ∑ z ∈ F, srwGreen (k + 5) m z * srwGreen (k + 5) m (z + u))
        Filter.atTop
        (nhds (∑ z ∈ F, srwGreenInf (k + 5) z * srwGreenInf (k + 5) (z + u))) :=
      tendsto_finsetSum _ fun z _ =>
        (tendsto_srwGreen hd3 z).mul (tendsto_srwGreen hd3 (z + u))
    refine le_of_tendsto hlim (Filter.Eventually.of_forall fun m => ?_)
    have hsub : ∑ z ∈ F, srwGreen (k + 5) m z * srwGreen (k + 5) m (z + u)
        ≤ ∑' z : Site (k + 5), srwGreen (k + 5) m z * srwGreen (k + 5) m (z + u) :=
      Summable.sum_le_tsum F
        (fun z _ => mul_nonneg (srwGreen_nonneg m z) (srwGreen_nonneg m _))
        (summable_srwGreen_mul m fun z => srwGreen (k + 5) m (z + u))
    refine hsub.trans ?_
    rw [tsum_srwGreen_mul_shift, sum_sum_add_eq m m (fun s => srwHeat (k + 5) s u)]
    have hstep : ∑ s ∈ Finset.range (m + m),
          (pairCount m m s : ℝ) * srwHeat (k + 5) s u
        ≤ ∑ s ∈ Finset.range (m + m), ((s : ℝ) + 1) * srwHeat (k + 5) s u := by
      refine Finset.sum_le_sum fun s _ => ?_
      refine mul_le_mul_of_nonneg_right ?_ (srwHeat_nonneg s u)
      have := pairCount_le m m s
      have hle : (pairCount m m s : ℝ) ≤ ((min (s + 1) m : ℕ) : ℝ) := by exact_mod_cast this
      refine hle.trans ?_
      have : ((min (s + 1) m : ℕ) : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.min_le_left _ _
      simp
    refine hstep.trans ?_
    exact (Summable.sum_le_tsum _ (fun s _ =>
      mul_nonneg (by positivity) (srwHeat_nonneg s u)) (hW u).1).trans (hW u).2
  exact ⟨summable_of_sum_le hnn hF, Real.tsum_le_of_sum_le hnn hF⟩

end LatticeProb
