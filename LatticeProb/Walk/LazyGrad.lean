/-
The gradient of the lazy random walk kernel.

The lazy walk has no parity obstruction: a one-step shift of the site changes
one one-dimensional factor of the coordinate decomposition from `P1 N k` to
`P1 N (k+1)`, and those two do not sit in disjoint parity classes, so their
difference genuinely cancels.  The one-dimensional gradient
`|P1 m k - P1 m (k+1)| ≤ 8 (m+1)^{-1} exp(-k^2/(8(m+1)))` of
`LatticeProb/Walk/P1Grad.lean` is a full power of `m` better than the peak
bound, and averaging it over schedules with the sharper estimate of
`LatticeProb/Walk/SchedExtra.lean` gives `R^{-(d+1)/2}` in place of `R^{-d/2}`,
with the Gaussian factor in the `l1` norm preserved.
-/
import Mathlib
import LatticeProb.Walk.SchedExtra
import LatticeProb.Walk.SRWGauss
import LatticeProb.Walk.OneDimGauss
import LatticeProb.Walk.Decomp
import LatticeProb.Walk.P1Grad
import LatticeProb.Walk.LazyBox

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-- The product over the coordinates of one-dimensional Gaussian factors, for
arbitrary positive weights. -/
theorem prod_exp_le_gen (x : Site d) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) :
    ∏ i, Real.exp (-((x i : ℝ)) ^ 2 / (8 * w i))
      ≤ Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * (∑ i, w i))) := by
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  have hw8 : ∀ i : Fin d, (0 : ℝ) < 8 * w i := fun i => by have := hw i; positivity
  have h := graphNorm_sq_div_le_of_pos x (fun i => 8 * w i) hw8
  have hsum : ∑ i, (8 * w i) = 8 * (∑ i, w i) := by rw [Finset.mul_sum]
  rw [hsum] at h
  have hrw : ∀ i : Fin d,
      -((x i : ℝ)) ^ 2 / (8 * w i) = -(((x i : ℝ)) ^ 2 / (8 * w i)) := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => hrw i, Finset.sum_neg_distrib]
  have hgn : -((graphNorm x : ℝ)) ^ 2 / (8 * (∑ i, w i))
      = -(((graphNorm x : ℝ)) ^ 2 / (8 * (∑ i, w i))) := by ring
  rw [hgn]
  exact neg_le_neg h

/-- The total weight of a schedule of length `r`, with one added per coordinate. -/
theorem sum_cnt_add_one {r : ℕ} (c : Fin r → Fin d) :
    ∑ i, ((cnt c i : ℝ) + 1) = (r : ℝ) + d := by
  rw [Finset.sum_add_distrib]
  have h1 : ∑ i, ((cnt c i : ℕ) : ℝ) = (r : ℝ) := by rw [← Nat.cast_sum, sum_cnt]
  rw [h1]
  simp

/-- The one-dimensional lazy kernel against its peak and a Gaussian factor. -/
theorem P1_le_gauss (m : ℕ) (k : ℤ) :
    P1 m k ≤ (1 : ℝ) / Real.sqrt ((m : ℝ) + 1)
      * Real.exp (-((k : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) := by
  have h1 := P1_gaussian m k
  have h2 := P1_zero_le_inv_sqrt m
  have hexp : Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1)))
      ≤ Real.exp (-((k : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) := by
    refine Real.exp_le_exp.mpr ?_
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hk : (0 : ℝ) ≤ ((k : ℝ)) ^ 2 := sq_nonneg _
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc P1 m k ≤ P1 m 0 * Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))) := h1
    _ ≤ (1 / Real.sqrt ((m : ℝ) + 1))
          * Real.exp (-((k : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) := by
        refine mul_le_mul h2 hexp (Real.exp_pos _).le ?_
        positivity

/-- The termwise gradient bound for a single schedule. -/
theorem K_gradient_term (n : Fin d → ℕ) (x : Site d) (i₀ : Fin d) :
    |K n x - K n (x + dirVec ((i₀, true) : Dir d))|
      ≤ 8 * ((1 : ℝ) / Real.sqrt ((n i₀ : ℝ) + 1))
          * (∏ j, (1 : ℝ) / Real.sqrt ((n j : ℝ) + 1))
          * ∏ j, Real.exp (-((x j : ℝ)) ^ 2 / (8 * ((n j : ℝ) + 1))) := by
  classical
  set G : Fin d → ℝ := fun j => (1 : ℝ) / Real.sqrt ((n j : ℝ) + 1) with hG
  set H : Fin d → ℝ := fun j => Real.exp (-((x j : ℝ)) ^ 2 / (8 * ((n j : ℝ) + 1))) with hH
  have hGnn : ∀ j, (0 : ℝ) ≤ G j := fun j => by simp only [hG]; positivity
  have hHnn : ∀ j, (0 : ℝ) ≤ H j := fun j => (Real.exp_pos _).le
  have hfac : K n x - K n (x + dirVec ((i₀, true) : Dir d))
      = (P1 (n i₀) (x i₀) - P1 (n i₀) (x i₀ + 1))
        * ∏ j ∈ Finset.univ.erase i₀, P1 (n j) (x j) := by
    rw [K_eq_mul_erase n x i₀, K_shift_pos n x i₀, ← sub_mul]
  rw [hfac, abs_mul]
  have hprodabs : |∏ j ∈ Finset.univ.erase i₀, P1 (n j) (x j)|
      = ∏ j ∈ Finset.univ.erase i₀, P1 (n j) (x j) :=
    abs_of_nonneg (Finset.prod_nonneg fun j _ => P1_nonneg _ _)
  rw [hprodabs]
  have hone : |P1 (n i₀) (x i₀) - P1 (n i₀) (x i₀ + 1)|
      ≤ 8 / ((n i₀ : ℝ) + 1) * H i₀ := P1_gradient (n i₀) (x i₀)
  have htail : (∏ j ∈ Finset.univ.erase i₀, P1 (n j) (x j))
      ≤ ∏ j ∈ Finset.univ.erase i₀, (G j * H j) :=
    Finset.prod_le_prod (fun j _ => P1_nonneg _ _) (fun j _ => P1_le_gauss (n j) (x j))
  have hstep : |P1 (n i₀) (x i₀) - P1 (n i₀) (x i₀ + 1)|
        * (∏ j ∈ Finset.univ.erase i₀, P1 (n j) (x j))
      ≤ (8 / ((n i₀ : ℝ) + 1) * H i₀) * ∏ j ∈ Finset.univ.erase i₀, (G j * H j) := by
    refine mul_le_mul hone htail (Finset.prod_nonneg fun j _ => P1_nonneg _ _) ?_
    have : (0 : ℝ) ≤ 8 / ((n i₀ : ℝ) + 1) := by positivity
    exact mul_nonneg this (hHnn i₀)
  refine hstep.trans ?_
  have hsq : G i₀ * G i₀ = 1 / ((n i₀ : ℝ) + 1) := by
    simp only [hG]
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]
  have hsplit : (8 / ((n i₀ : ℝ) + 1) * H i₀) * ∏ j ∈ Finset.univ.erase i₀, (G j * H j)
      = 8 * G i₀ * ∏ j, (G j * H j) := by
    have hprod : ∏ j, (G j * H j) = (G i₀ * H i₀) * ∏ j ∈ Finset.univ.erase i₀, (G j * H j) :=
      (Finset.mul_prod_erase Finset.univ (fun j => G j * H j) (Finset.mem_univ i₀)).symm
    rw [hprod]
    have h8 : (8 : ℝ) / ((n i₀ : ℝ) + 1) = 8 * (G i₀ * G i₀) := by rw [hsq]; ring
    rw [h8]
    ring
  rw [hsplit, Finset.prod_mul_distrib]
  simp only [hG, hH]
  exact le_of_eq (by ring)

/-- **The gradient of the lazy kernel**: shifting the site by one unit step
costs a factor `R^{-1/2}` against the sup bound, with the Gaussian factor
preserved. -/
theorem iterate_delta0_gradient (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) (x : Site d)
    (i₀ : Fin d) :
    |Q^[R] (delta0 : Site d → ℝ) x - Q^[R] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))|
      ≤ 8 * gradConst d * (R : ℝ) ^ (-((d : ℝ) + 1) / 2)
        * Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((R : ℝ) + d))) := by
  classical
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdRpow : (0 : ℝ) < (d : ℝ) ^ R := by positivity
  set E : ℝ := Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((R : ℝ) + d))) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hterm : ∀ c : Fin R → Fin d,
      |K (cnt c) x - K (cnt c) (x + dirVec ((i₀, true) : Dir d))|
        ≤ 8 * ((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
            * (∏ j, (1 : ℝ) / Real.sqrt ((cnt c j : ℝ) + 1)) * E := by
    intro c
    refine (K_gradient_term (cnt c) x i₀).trans ?_
    have hgauss : (∏ j, Real.exp (-((x j : ℝ)) ^ 2 / (8 * ((cnt c j : ℝ) + 1)))) ≤ E := by
      have := prod_exp_le_gen x (fun j => ((cnt c j : ℝ) + 1)) (fun j => by positivity)
      rwa [sum_cnt_add_one c] at this
    refine mul_le_mul_of_nonneg_left hgauss ?_
    have h1 : (0 : ℝ) ≤ (1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1) := by positivity
    have h2 : (0 : ℝ) ≤ ∏ j, (1 : ℝ) / Real.sqrt ((cnt c j : ℝ) + 1) :=
      Finset.prod_nonneg fun j _ => by positivity
    have : (0 : ℝ) ≤ 8 * ((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1)) := by positivity
    exact mul_nonneg this h2
  have hdecomp : Q^[R] (delta0 : Site d → ℝ) x
        - Q^[R] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))
      = (∑ c : Fin R → Fin d,
          (K (cnt c) x - K (cnt c) (x + dirVec ((i₀, true) : Dir d)))) / (d : ℝ) ^ R := by
    rw [iterate_delta0_eq hd R x, iterate_delta0_eq hd R _, ← sub_div, Finset.sum_sub_distrib]
  rw [hdecomp, abs_div, abs_of_pos hdRpow]
  rw [div_le_iff₀ hdRpow]
  have hsum : |∑ c : Fin R → Fin d,
        (K (cnt c) x - K (cnt c) (x + dirVec ((i₀, true) : Dir d)))|
      ≤ 8 * E * (∑ c : Fin R → Fin d,
          ((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
            * ∏ j, (1 : ℝ) / Real.sqrt ((cnt c j : ℝ) + 1)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    refine (hterm c).trans_eq ?_
    ring
  have havg := sched_avg_extra_le (d := d) hd hR i₀
  rw [div_le_iff₀ hdRpow] at havg
  calc |∑ c : Fin R → Fin d,
        (K (cnt c) x - K (cnt c) (x + dirVec ((i₀, true) : Dir d)))|
      ≤ 8 * E * (∑ c : Fin R → Fin d,
          ((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
            * ∏ j, (1 : ℝ) / Real.sqrt ((cnt c j : ℝ) + 1)) := hsum
    _ ≤ 8 * E * (gradConst d * (R : ℝ) ^ (-((d : ℝ) + 1) / 2) * (d : ℝ) ^ R) := by
        refine mul_le_mul_of_nonneg_left havg ?_
        positivity
    _ = 8 * gradConst d * (R : ℝ) ^ (-((d : ℝ) + 1) / 2) * E * (d : ℝ) ^ R := by ring

end LatticeProb
