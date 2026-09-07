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

/-! ### The radial tail of the squared Green function -/

/-- A nonnegative radial function summed over a finite set of sites all outside
the box of radius `M-1` is at most its shell sum from `M` on. -/
theorem sum_finset_radial_tail_le {d : ℕ} (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) {M : ℕ}
    (hM : 1 ≤ M) (F : Finset (Site d)) (hF : ∀ z ∈ F, M ≤ supNorm z) :
    ∑ z ∈ F, f (supNorm z)
      ≤ ∑ j ∈ Finset.Icc M (F.sup supNorm), (shellCard d j : ℝ) * f j := by
  classical
  set n : ℕ := F.sup supNorm with hn
  rcases Finset.eq_empty_or_nonempty F with rfl | hne
  · simp
    exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hf j)
  obtain ⟨z₀, hz₀⟩ := hne
  have hMn : M ≤ n := le_trans (hF z₀ hz₀) (Finset.le_sup hz₀)
  have hsub : F ⊆ (boxFinset (0 : Site d) n) \ (boxFinset (0 : Site d) (M - 1)) := by
    intro z hz
    rw [Finset.mem_sdiff, mem_boxFinset_zero_iff, mem_boxFinset_zero_iff]
    exact ⟨Finset.le_sup hz, by have := hF z hz; omega⟩
  have hstep : ∑ z ∈ F, f (supNorm z)
      ≤ ∑ z ∈ (boxFinset (0 : Site d) n) \ (boxFinset (0 : Site d) (M - 1)),
          f (supNorm z) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hf _
  refine hstep.trans (le_of_eq ?_)
  have hbox : (boxFinset (0 : Site d) (M - 1)) ⊆ boxFinset (0 : Site d) n :=
    boxFinset_zero_subset (by omega)
  have hsplit : ∑ z ∈ (boxFinset (0 : Site d) n) \ (boxFinset (0 : Site d) (M - 1)),
        f (supNorm z)
      = (∑ z ∈ boxFinset (0 : Site d) n, f (supNorm z))
        - ∑ z ∈ boxFinset (0 : Site d) (M - 1), f (supNorm z) := by
    rw [eq_sub_iff_add_eq, Finset.sum_sdiff hbox]
  rw [hsplit, sum_box_radial, sum_box_radial]
  have hIcc : ∑ j ∈ Finset.Icc 1 n, (shellCard d j : ℝ) * f j
      = (∑ j ∈ Finset.Icc 1 (M - 1), (shellCard d j : ℝ) * f j)
        + ∑ j ∈ Finset.Icc M n, (shellCard d j : ℝ) * f j := by
    rw [← Finset.sum_union]
    · congr 1
      ext j
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    · rw [Finset.disjoint_left]
      intro j hj hj'
      rw [Finset.mem_Icc] at hj hj'
      omega
  rw [hIcc]
  ring

/-- **The radial tail of the squared Green function.**  For every finite set of
sites outside the box of radius `M-1`, `∑ G(0,z)^2 ≤ C M^{4-d}`. -/
theorem exists_sum_srwGreenInf_sq_tail_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ F : Finset (Site (k + 5)),
      (∀ z ∈ F, M ≤ supNorm z) →
        ∑ z ∈ F, srwGreenInf (k + 5) z ^ 2 ≤ C / (M : ℝ) ^ (k + 1) := by
  obtain ⟨C₀, hC₀, hpt⟩ := exists_srwGreenInf_le (k + 1)
  refine ⟨C₀ ^ 2 * (2 * ((k : ℝ) + 5) * 3 ^ (k + 4)) * 2, by positivity,
    fun M hM F hF => ?_⟩
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  set f : ℕ → ℝ := fun j => C₀ ^ 2 / (1 + (j : ℝ)) ^ (2 * k + 6) with hf
  have hfnn : ∀ j, 0 ≤ f j := fun j => by rw [hf]; positivity
  -- the pointwise bound in the sup norm
  have hterm : ∀ z : Site (k + 5), srwGreenInf (k + 5) z ^ 2 ≤ f (supNorm z) := by
    intro z
    have h1 : (0 : ℝ) < 1 + ((supNorm z : ℕ) : ℝ) := by positivity
    have hsg : ((supNorm z : ℕ) : ℝ) ≤ ((graphNorm z : ℕ) : ℝ) := by
      exact_mod_cast supNorm_le_graphNorm z
    have hb : srwGreenInf (k + 5) z ≤ C₀ / (1 + ((supNorm z : ℕ) : ℝ)) ^ (k + 3) := by
      refine (hpt z).trans ?_
      exact div_le_div_of_nonneg_left hC₀.le (by positivity)
        (pow_le_pow_left₀ h1.le (by linarith) (k + 3))
    have hnn : 0 ≤ srwGreenInf (k + 5) z := tsum_nonneg fun j => srwHeat_nonneg j z
    have := pow_le_pow_left₀ hnn hb 2
    refine this.trans (le_of_eq ?_)
    rw [hf, div_pow, ← pow_mul]
    congr 2
    omega
  refine (Finset.sum_le_sum fun z _ => hterm z).trans ?_
  refine (sum_finset_radial_tail_le f hfnn hM F hF).trans ?_
  -- the shell sum
  have hshell : ∀ j ∈ Finset.Icc M (F.sup supNorm),
      (shellCard (k + 5) j : ℝ) * f j
        ≤ C₀ ^ 2 * (2 * ((k : ℝ) + 5) * 3 ^ (k + 4))
          * ((M : ℝ) ^ k)⁻¹ * (((j : ℝ)) ^ 2)⁻¹ := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : 1 ≤ j := le_trans hM hj.1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hjM : (M : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hsc : (shellCard (k + 5) j : ℝ) ≤ 2 * ((k : ℝ) + 5) * (2 * (j : ℝ) + 1) ^ (k + 4) := by
      have h := shellCard_le (k + 5) hj1
      have hd1 : ((k + 5) - 1 : ℕ) = k + 4 := by omega
      rw [hd1] at h
      refine h.trans (le_of_eq ?_)
      push_cast
      ring
    have h3 : (2 * (j : ℝ) + 1) ^ (k + 4) ≤ 3 ^ (k + 4) * (1 + (j : ℝ)) ^ (k + 4) := by
      rw [← mul_pow]
      have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hfj : f j = C₀ ^ 2 / (1 + (j : ℝ)) ^ (2 * k + 6) := rfl
    have hkey : (1 + (j : ℝ)) ^ (k + 4) / (1 + (j : ℝ)) ^ (2 * k + 6)
        ≤ ((M : ℝ) ^ k)⁻¹ * (((j : ℝ)) ^ 2)⁻¹ := by
      have hsplitp : (1 + (j : ℝ)) ^ (2 * k + 6)
          = (1 + (j : ℝ)) ^ (k + 4) * ((1 + (j : ℝ)) ^ k * (1 + (j : ℝ)) ^ 2) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      rw [hsplitp]
      have hpos1 : (0 : ℝ) < (1 + (j : ℝ)) ^ (k + 4) := by positivity
      rw [show (1 + (j : ℝ)) ^ (k + 4) / ((1 + (j : ℝ)) ^ (k + 4)
          * ((1 + (j : ℝ)) ^ k * (1 + (j : ℝ)) ^ 2))
          = ((1 + (j : ℝ)) ^ k * (1 + (j : ℝ)) ^ 2)⁻¹ from by
        rw [div_eq_iff (by positivity)]
        field_simp]
      have hMk : ((M : ℝ)) ^ k ≤ (1 + (j : ℝ)) ^ k :=
        pow_le_pow_left₀ hMpos.le (by linarith) k
      have hj2 : ((j : ℝ)) ^ 2 ≤ (1 + (j : ℝ)) ^ 2 := by nlinarith
      rw [mul_inv]
      refine mul_le_mul (inv_anti₀ (by positivity) hMk) (inv_anti₀ (by positivity) hj2)
        (by positivity) (by positivity)
    calc (shellCard (k + 5) j : ℝ) * f j
        ≤ 2 * ((k : ℝ) + 5) * (3 ^ (k + 4) * (1 + (j : ℝ)) ^ (k + 4)) * f j := by
          refine mul_le_mul_of_nonneg_right (hsc.trans ?_) (hfnn j)
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = C₀ ^ 2 * (2 * ((k : ℝ) + 5) * 3 ^ (k + 4))
            * ((1 + (j : ℝ)) ^ (k + 4) / (1 + (j : ℝ)) ^ (2 * k + 6)) := by
          rw [hfj]; ring
      _ ≤ C₀ ^ 2 * (2 * ((k : ℝ) + 5) * 3 ^ (k + 4))
            * (((M : ℝ) ^ k)⁻¹ * (((j : ℝ)) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = C₀ ^ 2 * (2 * ((k : ℝ) + 5) * 3 ^ (k + 4))
            * ((M : ℝ) ^ k)⁻¹ * (((j : ℝ)) ^ 2)⁻¹ := by ring
  refine (Finset.sum_le_sum hshell).trans ?_
  rw [← Finset.mul_sum]
  have hIco : Finset.Icc M (F.sup supNorm) = Finset.Ico M (F.sup supNorm + 1) :=
    (Finset.Ico_add_one_right_eq_Icc M (F.sup supNorm)).symm
  rw [hIco]
  have hser := sum_Ico_inv_sq_le hM (F.sup supNorm + 1)
  have hAnn : (0 : ℝ) ≤ C₀ ^ 2 * (2 * ((k : ℝ) + 5) * 3 ^ (k + 4)) * ((M : ℝ) ^ k)⁻¹ := by
    positivity
  refine (mul_le_mul_of_nonneg_left hser hAnn).trans (le_of_eq ?_)
  rw [div_eq_mul_inv, pow_succ]
  field_simp
  ring

/-- **The Green tail bound** `∑_{|z| ≥ r} G(0,z)^2 ≤ C r^{4-d}` above dimension
four, in the Euclidean norm, with its summability. -/
theorem exists_tsum_srwGreenInf_sq_tail_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r →
      (Summable fun z : {z : Site (k + 5) // (r : ℝ) ≤ euclidNorm z} =>
          srwGreenInf (k + 5) (z : Site (k + 5)) ^ 2) ∧
        (∑' z : {z : Site (k + 5) // (r : ℝ) ≤ euclidNorm z},
            srwGreenInf (k + 5) (z : Site (k + 5)) ^ 2)
          ≤ C / (r : ℝ) ^ (k + 1) := by
  classical
  obtain ⟨C₁, hC₁, htail⟩ := exists_sum_srwGreenInf_sq_tail_le k
  have hsd : (0 : ℝ) < Real.sqrt ((k + 5 : ℕ) : ℝ) := by
    refine Real.sqrt_pos.mpr ?_
    positivity
  refine ⟨C₁ * Real.sqrt ((k + 5 : ℕ) : ℝ) ^ (k + 1), by positivity, fun r hr => ?_⟩
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  set M : ℕ := ⌈(r : ℝ) / Real.sqrt ((k + 5 : ℕ) : ℝ)⌉₊ with hMdef
  have hMge : (r : ℝ) / Real.sqrt ((k + 5 : ℕ) : ℝ) ≤ (M : ℝ) := Nat.le_ceil _
  have hM1 : 1 ≤ M := by
    rw [hMdef, Nat.one_le_ceil_iff]
    positivity
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hsup : ∀ z : Site (k + 5), (r : ℝ) ≤ euclidNorm z → M ≤ supNorm z := by
    intro z hz
    rw [hMdef, Nat.ceil_le]
    rw [div_le_iff₀ hsd]
    have h := euclidNorm_le_sqrt_mul_supNorm z
    have hcast : Real.sqrt ((k + 5 : ℕ) : ℝ) = Real.sqrt ((k + 5 : ℕ) : ℝ) := rfl
    calc (r : ℝ) ≤ euclidNorm z := hz
      _ ≤ Real.sqrt ((k + 5 : ℕ) : ℝ) * ((supNorm z : ℕ) : ℝ) := h
      _ = ((supNorm z : ℕ) : ℝ) * Real.sqrt ((k + 5 : ℕ) : ℝ) := by ring
  set c : ℝ := C₁ * Real.sqrt ((k + 5 : ℕ) : ℝ) ^ (k + 1) / (r : ℝ) ^ (k + 1) with hc
  have hnn : ∀ z : {z : Site (k + 5) // (r : ℝ) ≤ euclidNorm z},
      0 ≤ srwGreenInf (k + 5) (z : Site (k + 5)) ^ 2 := fun z => sq_nonneg _
  have hF : ∀ F : Finset {z : Site (k + 5) // (r : ℝ) ≤ euclidNorm z},
      ∑ z ∈ F, srwGreenInf (k + 5) (z : Site (k + 5)) ^ 2 ≤ c := by
    intro F
    have himg : ∑ z ∈ F, srwGreenInf (k + 5) (z : Site (k + 5)) ^ 2
        = ∑ z ∈ F.image (Subtype.val), srwGreenInf (k + 5) z ^ 2 := by
      rw [Finset.sum_image fun a _ b _ h => Subtype.ext h]
    rw [himg]
    have hmem : ∀ z ∈ F.image (Subtype.val : _ → Site (k + 5)), M ≤ supNorm z := by
      intro z hz
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hz
      exact hsup _ w.2
    refine (htail M hM1 _ hmem).trans ?_
    rw [hc]
    have hMk : ((r : ℝ) / Real.sqrt ((k + 5 : ℕ) : ℝ)) ^ (k + 1) ≤ (M : ℝ) ^ (k + 1) :=
      pow_le_pow_left₀ (by positivity) hMge (k + 1)
    have hden : (0 : ℝ) < ((r : ℝ) / Real.sqrt ((k + 5 : ℕ) : ℝ)) ^ (k + 1) := by positivity
    have hstep : C₁ / (M : ℝ) ^ (k + 1)
        ≤ C₁ / ((r : ℝ) / Real.sqrt ((k + 5 : ℕ) : ℝ)) ^ (k + 1) :=
      div_le_div_of_nonneg_left hC₁.le hden hMk
    refine hstep.trans (le_of_eq ?_)
    rw [div_pow]
    field_simp
  exact ⟨summable_of_sum_le hnn hF, Real.tsum_le_of_sum_le hnn hF⟩

/-- **The Green sup bound** `sup_{|z| ≥ r} G(0,z) ≤ C r^{2-d}`, in the
Euclidean norm. -/
theorem exists_srwGreenInf_sup_tail_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r → ∀ z : Site (k + 5), (r : ℝ) ≤ euclidNorm z →
      srwGreenInf (k + 5) z ≤ C / (r : ℝ) ^ (k + 3) := by
  obtain ⟨C, hC, hpt⟩ := exists_srwGreenInf_euclid_le (k + 1)
  refine ⟨C, hC, fun r hr z hz => ?_⟩
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  refine (hpt z).trans ?_
  refine div_le_div_of_nonneg_left hC.le (by positivity) ?_
  exact pow_le_pow_left₀ hrpos.le (by linarith) (k + 3)

/-! ### The time tail of the kernel -/

/-- The index equivalence `{j // m ≤ j} ≃ ℕ`. -/
def geEquiv (m : ℕ) : {j : ℕ // m ≤ j} ≃ ℕ where
  toFun j := (j : ℕ) - m
  invFun i := ⟨m + i, Nat.le_add_right _ _⟩
  left_inv := fun j => Subtype.ext (by simp; omega)
  right_inv := by intro i; simp

theorem tsum_subtype_ge (m : ℕ) (f : ℕ → ℝ) :
    ∑' j : {j : ℕ // m ≤ j}, f (j : ℕ) = ∑' i : ℕ, f (m + i) := by
  rw [← (geEquiv m).symm.tsum_eq (fun j : {j : ℕ // m ≤ j} => f (j : ℕ))]
  rfl

theorem summable_subtype_ge {m : ℕ} {f : ℕ → ℝ} (hf : Summable f) :
    Summable fun j : {j : ℕ // m ≤ j} => f (j : ℕ) :=
  hf.subtype {j : ℕ | m ≤ j}

/-- The tail of the kernel in time, `∑_{j ≥ m} p_j(0,y)`. -/
noncomputable def srwTimeTail (d : ℕ) (m : ℕ) (y : Site d) : ℝ :=
  ∑' j : {j : ℕ // m ≤ j}, srwHeat d (j : ℕ) y

theorem srwTimeTail_nonneg (d m : ℕ) (y : Site d) : 0 ≤ srwTimeTail d m y :=
  tsum_nonneg fun _ => srwHeat_nonneg _ y

/-- The partial sums of the tail converge to it. -/
theorem tendsto_sum_Ico_srwTimeTail (hd : 3 ≤ d) (m : ℕ) (y : Site d) :
    Filter.Tendsto (fun N : ℕ => ∑ s ∈ Finset.Ico m (m + N), srwHeat d s y)
      Filter.atTop (nhds (srwTimeTail d m y)) := by
  have hsum : Summable fun i : ℕ => srwHeat d (m + i) y :=
    (summable_srwHeat hd y).comp_injective (add_right_injective m)
  have h := hsum.hasSum.tendsto_sum_nat
  rw [srwTimeTail, tsum_subtype_ge m (fun j => srwHeat d j y)]
  refine h.congr fun N => ?_
  rw [Finset.sum_Ico_eq_sum_range]
  simp

/-- **The time tail of the kernel**, uniformly in the site:
`∑_{j ≥ m} p_j(0,y) ≤ C m^{(2-d)/2}`. -/
theorem exists_srwTimeTail_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ y : Site (k + 5),
      srwTimeTail (k + 5) m y ≤ C / Real.sqrt (m : ℝ) ^ (k + 3) := by
  refine ⟨2 * diagConst (k + 5), by linarith [diagConst_pos (k + 5)], fun m hm y => ?_⟩
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  refine le_of_tendsto (tendsto_sum_Ico_srwTimeTail (by omega) m y)
    (Filter.Eventually.of_forall fun N => ?_)
  have h := sum_Ico_srwHeat_high_le (k := k + 1) hm (m + N) y
  refine h.trans (le_of_eq ?_)
  have hpow : Real.sqrt (m : ℝ) ^ (k + 3)
      = (m : ℝ) * Real.sqrt (m : ℝ) ^ (k + 1) := by
    rw [show (k + 3) = (k + 1) + 2 from by omega, pow_add, Real.sq_sqrt hmpos.le]
    ring
  rw [hpow]
  field_simp

/-- A double sum over a product of finite sets of times, grouped by the sum of
the indices: the fibre over `s` has at most `s+1` elements. -/
theorem sum_pair_add_le (S T U : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ s, 0 ≤ f s)
    (hU : ∀ a ∈ S, ∀ b ∈ T, a + b ∈ U) :
    ∑ a ∈ S, ∑ b ∈ T, f (a + b) ≤ ∑ s ∈ U, ((s : ℝ) + 1) * f s := by
  classical
  have hmaps : ∀ p ∈ S ×ˢ T, p.1 + p.2 ∈ U := by
    intro p hp
    rw [Finset.mem_product] at hp
    exact hU p.1 hp.1 p.2 hp.2
  have hfib := Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + p.2)
    (f := fun p : ℕ × ℕ => f (p.1 + p.2)) hmaps
  rw [← Finset.sum_product', ← hfib]
  refine Finset.sum_le_sum fun s _ => ?_
  have hcongr : ∀ p ∈ ((S ×ˢ T).filter fun p : ℕ × ℕ => p.1 + p.2 = s),
      f (p.1 + p.2) = f s := fun p hp => by rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hf s)
  have hcard : (((S ×ˢ T).filter fun p : ℕ × ℕ => p.1 + p.2 = s)).card ≤ s + 1 := by
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1)
        (((S ×ˢ T).filter fun p : ℕ × ℕ => p.1 + p.2 = s)) := by
      intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : p.1 = q.1 := hpq
      exact Prod.ext h1 (by omega)
    calc (((S ×ˢ T).filter fun p : ℕ × ℕ => p.1 + p.2 = s)).card
        ≤ (Finset.range (s + 1)).card := by
          refine Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1) ?_ hinj
          intro p hp
          have hs : p.1 + p.2 = s := (Finset.mem_filter.mp hp).2
          refine Finset.mem_range.mpr ?_
          show p.1 < s + 1
          omega
      _ = s + 1 := Finset.card_range _
  have := (Nat.cast_le (α := ℝ)).mpr hcard
  push_cast at this
  exact this

theorem summable_finsetSum_srwHeat_mul (S : Finset ℕ) (f : Site d → ℝ) :
    Summable fun y : Site d => (∑ s ∈ S, srwHeat d s y) * f y := by
  have hrw : (fun y : Site d => (∑ s ∈ S, srwHeat d s y) * f y)
      = fun y : Site d => ∑ s ∈ S, srwHeat d s y * f y := by
    funext y; rw [Finset.sum_mul]
  rw [hrw]
  exact summable_sum fun s _ => summable_srwHeat_mul s f

/-- **The `ℓ²` norm of the time tail**:
`∑_y (∑_{j ≥ m} p_j(0,y))^2 ≤ C m^{(4-d)/2}`, with its summability. -/
theorem exists_tsum_srwTimeTail_sq_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      (Summable fun y : Site (k + 5) => srwTimeTail (k + 5) m y ^ 2) ∧
        (∑' y : Site (k + 5), srwTimeTail (k + 5) m y ^ 2)
          ≤ C / Real.sqrt (m : ℝ) ^ (k + 1) := by
  refine ⟨12 * diagConst (k + 5), by linarith [diagConst_pos (k + 5)], fun m hm => ?_⟩
  have hd3 : 3 ≤ k + 5 := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  set c : ℝ := 12 * diagConst (k + 5) / Real.sqrt (m : ℝ) ^ (k + 1) with hc
  have hnn : ∀ y : Site (k + 5), 0 ≤ srwTimeTail (k + 5) m y ^ 2 := fun y => sq_nonneg _
  have hF : ∀ F : Finset (Site (k + 5)),
      ∑ y ∈ F, srwTimeTail (k + 5) m y ^ 2 ≤ c := by
    intro F
    have hlim : Filter.Tendsto
        (fun N : ℕ => ∑ y ∈ F, (∑ s ∈ Finset.Ico m (m + N), srwHeat (k + 5) s y) ^ 2)
        Filter.atTop (nhds (∑ y ∈ F, srwTimeTail (k + 5) m y ^ 2)) :=
      tendsto_finsetSum _ fun y _ =>
        ((tendsto_sum_Ico_srwTimeTail hd3 m y).pow 2)
    refine le_of_tendsto hlim (Filter.Eventually.of_forall fun N => ?_)
    have hsq : ∀ y : Site (k + 5),
        (∑ s ∈ Finset.Ico m (m + N), srwHeat (k + 5) s y) ^ 2
          = (∑ s ∈ Finset.Ico m (m + N), srwHeat (k + 5) s y)
            * (∑ s ∈ Finset.Ico m (m + N), srwHeat (k + 5) s y) := fun y => sq _
    have hsub : ∑ y ∈ F, (∑ s ∈ Finset.Ico m (m + N), srwHeat (k + 5) s y) ^ 2
        ≤ ∑' y : Site (k + 5), (∑ s ∈ Finset.Ico m (m + N), srwHeat (k + 5) s y) ^ 2 := by
      refine Summable.sum_le_tsum F (fun y _ => sq_nonneg _) ?_
      simp only [hsq]
      exact summable_finsetSum_srwHeat_mul _ _
    refine hsub.trans ?_
    simp only [hsq]
    rw [tsum_sum_srwHeat_mul]
    -- group by the total time
    have hU : ∀ a ∈ Finset.Ico m (m + N), ∀ b ∈ Finset.Ico m (m + N),
        a + b ∈ Finset.Ico (2 * m) (2 * (m + N)) := by
      intro a ha b hb
      rw [Finset.mem_Ico] at ha hb ⊢
      omega
    refine (sum_pair_add_le _ _ _ (fun s => srwHeat (k + 5) s 0)
      (fun s => srwHeat_nonneg s 0) hU).trans ?_
    have hterm : ∀ s ∈ Finset.Ico (2 * m) (2 * (m + N)),
        ((s : ℝ) + 1) * srwHeat (k + 5) s (0 : Site (k + 5))
          ≤ 2 * diagConst (k + 5) * (Real.sqrt (s : ℝ) ^ ((k + 1) + 2))⁻¹ := by
      intro s hs
      exact weighted_srwHeat_far_le k (by have := (Finset.mem_Ico.mp hs).1; omega) _
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hm2 : 1 ≤ 2 * m := by omega
    have h := sum_Ico_inv_sqrt_pow_le' (k := k + 1) (by omega) hm2 (2 * (m + N))
    have hsm2 : Real.sqrt (m : ℝ) ≤ Real.sqrt ((2 * m : ℕ) : ℝ) := by
      refine Real.sqrt_le_sqrt ?_
      push_cast
      linarith
    have hpow2 : Real.sqrt (m : ℝ) ^ (k + 1) ≤ Real.sqrt ((2 * m : ℕ) : ℝ) ^ (k + 1) :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hsm2 (k + 1)
    have hp1 : (0 : ℝ) < Real.sqrt (m : ℝ) ^ (k + 1) := by positivity
    have hdiv : (6 : ℝ) / Real.sqrt ((2 * m : ℕ) : ℝ) ^ (k + 1)
        ≤ 6 / Real.sqrt (m : ℝ) ^ (k + 1) :=
      div_le_div_of_nonneg_left (by norm_num) hp1 hpow2
    rw [hc]
    calc 2 * diagConst (k + 5)
          * ∑ s ∈ Finset.Ico (2 * m) (2 * (m + N)),
              (Real.sqrt (s : ℝ) ^ ((k + 1) + 2))⁻¹
        ≤ 2 * diagConst (k + 5) * (6 / Real.sqrt ((2 * m : ℕ) : ℝ) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left h (by linarith [(diagConst_pos (k + 5)).le])
      _ ≤ 2 * diagConst (k + 5) * (6 / Real.sqrt (m : ℝ) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hdiv (by linarith [(diagConst_pos (k + 5)).le])
      _ = 12 * diagConst (k + 5) / Real.sqrt (m : ℝ) ^ (k + 1) := by ring
  exact ⟨summable_of_sum_le hnn hF, Real.tsum_le_of_sum_le hnn hF⟩

end LatticeProb
