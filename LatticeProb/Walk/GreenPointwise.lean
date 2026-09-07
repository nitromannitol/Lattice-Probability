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

end LatticeProb
