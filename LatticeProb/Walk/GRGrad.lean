/-
The gradient of the truncated lazy Green function.

Summing the kernel gradient of `LatticeProb/Walk/LazyGrad.lean` over time
against its own Gaussian factor turns the time decay `r^{-(d+1)/2}` into the
space decay `(1 + |x|)^{1-d}`, uniformly in the horizon: that is the summation
estimate of `LatticeProb/Walk/GaussSeries.lean`.  The zero-step term of the sum
vanishes off the two sites next to the origin and so costs only a constant.
-/
import Mathlib
import LatticeProb.Walk.LazyGrad
import LatticeProb.Walk.GaussSeries
import LatticeProb.Walk.SimpleTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-- The zero-step term of the Green sum already obeys the gradient bound: it
vanishes unless the site is within one step of the origin. -/
theorem delta0_gradient (hd : 1 ≤ d) (x : Site d) (i₀ : Fin d) :
    |(delta0 : Site d → ℝ) x - (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))|
      ≤ 2 ^ ((d : ℝ) - 1) * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
  by_cases hn : 2 ≤ graphNorm x
  · have hx : x ≠ 0 := by
      intro h
      rw [h] at hn
      simp at hn
    have hx' : x + dirVec ((i₀, true) : Dir d) ≠ 0 := by
      intro h
      have := graphNorm_le_succ_of_add_dirVec x ((i₀, true) : Dir d)
      rw [h] at this
      simp at this
      omega
    simp only [delta0, if_neg hx, if_neg hx']
    have : (0 : ℝ) ≤ 2 ^ ((d : ℝ) - 1) * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
      refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by positivity) _)
    simpa using this
  · have hle : (1 + (graphNorm x : ℝ)) ≤ 2 := by
      have : graphNorm x ≤ 1 := by omega
      have : ((graphNorm x : ℕ) : ℝ) ≤ 1 := by exact_mod_cast this
      linarith
    have hpos : (0 : ℝ) < 1 + (graphNorm x : ℝ) := by positivity
    have hexp : (1 : ℝ) - (d : ℝ) ≤ 0 := by
      have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have hmono : (2 : ℝ) ^ (1 - (d : ℝ)) ≤ (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hpos hle hexp
    have hprod : (1 : ℝ) ≤ 2 ^ ((d : ℝ) - 1) * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
      have hkey : (2 : ℝ) ^ ((d : ℝ) - 1) * 2 ^ (1 - (d : ℝ)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]
        norm_num
      calc (1 : ℝ) = 2 ^ ((d : ℝ) - 1) * 2 ^ (1 - (d : ℝ)) := hkey.symm
        _ ≤ 2 ^ ((d : ℝ) - 1) * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
            refine mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg (by norm_num) _)
    refine le_trans ?_ hprod
    have hb : ∀ y : Site d, (0 : ℝ) ≤ (delta0 : Site d → ℝ) y ∧ (delta0 : Site d → ℝ) y ≤ 1 := by
      intro y
      by_cases h : y = 0 <;> simp [delta0, h]
    have h1 := hb x
    have h2 := hb (x + dirVec ((i₀, true) : Dir d))
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The gradient of the truncated lazy Green function, given the summation
estimate. -/
theorem gR_gradient_of {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hS : ∀ (R n : ℕ), ∑ r ∈ Finset.Ico 1 R, (r : ℝ) ^ (-((d : ℝ) + 1) / 2)
            * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))
          ≤ C₀ * (1 + (n : ℝ)) ^ (1 - (d : ℝ)))
    (hd : 0 < d) (R : ℕ) (x : Site d) (i₀ : Fin d) :
    |gR R x - gR R (x + dirVec ((i₀, true) : Dir d))|
      ≤ (8 * gradConst d * C₀ + 2 ^ ((d : ℝ) - 1))
        * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
  classical
  have hsplit : Finset.range R = if R = 0 then ∅ else insert 0 (Finset.Ico 1 R) := by
    by_cases hR : R = 0
    · simp [hR]
    · rw [if_neg hR]
      ext t
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
  have hdiff : gR R x - gR R (x + dirVec ((i₀, true) : Dir d))
      = ∑ r ∈ Finset.range R,
          (Q^[r] (delta0 : Site d → ℝ) x
            - Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))) := by
    rw [gR, gR, Finset.sum_sub_distrib]
  have hterm : ∀ r ∈ Finset.Ico 1 R,
      |Q^[r] (delta0 : Site d → ℝ) x
        - Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))|
        ≤ 8 * gradConst d * ((r : ℝ) ^ (-((d : ℝ) + 1) / 2)
            * Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))) := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have := iterate_delta0_gradient hd hr.1 x i₀
    calc |Q^[r] (delta0 : Site d → ℝ) x
          - Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))|
        ≤ 8 * gradConst d * (r : ℝ) ^ (-((d : ℝ) + 1) / 2)
            * Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((r : ℝ) + d))) := this
      _ = 8 * gradConst d * ((r : ℝ) ^ (-((d : ℝ) + 1) / 2)
            * Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))) := by ring
  have hmain : ∑ r ∈ Finset.Ico 1 R,
      |Q^[r] (delta0 : Site d → ℝ) x
        - Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))|
      ≤ 8 * gradConst d * C₀ * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
    calc ∑ r ∈ Finset.Ico 1 R,
          |Q^[r] (delta0 : Site d → ℝ) x
            - Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))|
        ≤ ∑ r ∈ Finset.Ico 1 R, 8 * gradConst d * ((r : ℝ) ^ (-((d : ℝ) + 1) / 2)
            * Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))) :=
          Finset.sum_le_sum hterm
      _ = 8 * gradConst d * ∑ r ∈ Finset.Ico 1 R, ((r : ℝ) ^ (-((d : ℝ) + 1) / 2)
            * Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))) := by
          rw [Finset.mul_sum]
      _ ≤ 8 * gradConst d * (C₀ * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (hS R (graphNorm x)) ?_
          have := gradConst_nonneg d
          positivity
      _ = 8 * gradConst d * C₀ * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by ring
  have hzero := delta0_gradient (d := d) hd x i₀
  rw [hdiff]
  by_cases hR : R = 0
  · subst hR
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
    have : (0 : ℝ) ≤ (8 * gradConst d * C₀ + 2 ^ ((d : ℝ) - 1))
        * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
      have h1 := gradConst_nonneg d
      have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) - 1) := Real.rpow_nonneg (by norm_num) _
      have h3 : (0 : ℝ) ≤ (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have h4 : (0 : ℝ) ≤ 8 * gradConst d * C₀ := by positivity
      positivity
    exact this
  · rw [hsplit, if_neg hR, Finset.sum_insert (by simp)]
    refine (abs_add_le _ _).trans ?_
    have hle2 : |∑ r ∈ Finset.Ico 1 R,
        (Q^[r] (delta0 : Site d → ℝ) x
          - Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d)))|
        ≤ 8 * gradConst d * C₀ * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) hmain
    have hle1 : |Q^[0] (delta0 : Site d → ℝ) x
        - Q^[0] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))|
        ≤ 2 ^ ((d : ℝ) - 1) * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
      simpa using hzero
    calc |Q^[0] (delta0 : Site d → ℝ) x
          - Q^[0] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))|
        + |∑ r ∈ Finset.Ico 1 R,
            (Q^[r] (delta0 : Site d → ℝ) x
              - Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d)))|
        ≤ 2 ^ ((d : ℝ) - 1) * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ))
          + 8 * gradConst d * C₀ * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by
          linarith
      _ = (8 * gradConst d * C₀ + 2 ^ ((d : ℝ) - 1))
            * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := by ring

end LatticeProb

namespace LatticeProb

open Finset

/-- Every neighbour of a site is one unit step away, in one of the two signs. -/
theorem exists_dir_of_mem_nbrFinset {d : ℕ} {y z : Site d} (h : z ∈ nbrFinset y) :
    (∃ i : Fin d, z = y + dirVec ((i, true) : Dir d)) ∨
      (∃ i : Fin d, y = z + dirVec ((i, true) : Dir d)) := by
  classical
  rw [nbrFinset, Finset.mem_biUnion] at h
  obtain ⟨i, _, hi⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with hi | hi
  · exact Or.inl ⟨i, by rw [hi, dirVec_eq_unit]⟩
  · refine Or.inr ⟨i, ?_⟩
    rw [hi, dirVec_eq_unit]
    abel

/-- Shifting the base point by one step costs at most a factor `2^{d-1}` in the
weight `(1 + |y|)^{1-d}`. -/
theorem rpow_shift_le {d : ℕ} (hd : 0 < d) {y z : Site d}
    (h : graphNorm y ≤ graphNorm z + 1) :
    (1 + (graphNorm z : ℝ)) ^ (1 - (d : ℝ))
      ≤ 2 ^ ((d : ℝ) - 1) * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) := by
  have hzpos : (0 : ℝ) < 1 + (graphNorm z : ℝ) := by positivity
  have hypos : (0 : ℝ) < 1 + (graphNorm y : ℝ) := by positivity
  have hcast : ((graphNorm y : ℕ) : ℝ) ≤ ((graphNorm z : ℕ) : ℝ) + 1 := by exact_mod_cast h
  have hle : (1 + (graphNorm y : ℝ)) / 2 ≤ 1 + (graphNorm z : ℝ) := by
    have : (0 : ℝ) ≤ (graphNorm z : ℝ) := Nat.cast_nonneg _
    linarith
  have hexp : (1 : ℝ) - (d : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hmono : (1 + (graphNorm z : ℝ)) ^ (1 - (d : ℝ))
      ≤ ((1 + (graphNorm y : ℝ)) / 2) ^ (1 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hle hexp
  refine hmono.trans_eq ?_
  rw [Real.div_rpow (le_of_lt hypos) (by norm_num)]
  have h2 : (2 : ℝ) ^ (1 - (d : ℝ)) = ((2 : ℝ) ^ ((d : ℝ) - 1))⁻¹ := by
    rw [show (1 : ℝ) - (d : ℝ) = -((d : ℝ) - 1) by ring, Real.rpow_neg (by norm_num)]
  rw [h2, div_inv_eq_mul, mul_comm]

end LatticeProb

namespace LatticeProb

open Finset

/-- The gradient of the truncated lazy Green function between two neighbouring
sites, given the summation estimate. -/
theorem gR_gradient_nbr_of {d : ℕ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hS : ∀ (R n : ℕ), ∑ r ∈ Finset.Ico 1 R, (r : ℝ) ^ (-((d : ℝ) + 1) / 2)
            * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))
          ≤ C₀ * (1 + (n : ℝ)) ^ (1 - (d : ℝ)))
    (hd : 0 < d) (R : ℕ) (y z : Site d) (hz : z ∈ nbrFinset y) :
    |gR R y - gR R z|
      ≤ 2 ^ ((d : ℝ) - 1) * (8 * gradConst d * C₀ + 2 ^ ((d : ℝ) - 1))
        * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) := by
  set A : ℝ := 8 * gradConst d * C₀ + 2 ^ ((d : ℝ) - 1) with hA
  have hAnn : (0 : ℝ) ≤ A := by
    have h1 := gradConst_nonneg d
    have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) - 1) := Real.rpow_nonneg (by norm_num) _
    have h3 : (0 : ℝ) ≤ 8 * gradConst d * C₀ := by positivity
    simp only [hA]
    linarith
  have hpow : (0 : ℝ) ≤ 2 ^ ((d : ℝ) - 1) := Real.rpow_nonneg (by norm_num) _
  have hy : (0 : ℝ) ≤ (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hone : (1 : ℝ) ≤ 2 ^ ((d : ℝ) - 1) := by
    refine Real.one_le_rpow (by norm_num) ?_
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rcases exists_dir_of_mem_nbrFinset hz with ⟨i, hi⟩ | ⟨i, hi⟩
  · subst hi
    have h := gR_gradient_of hC₀ hS hd R y i
    calc |gR R y - gR R (y + dirVec ((i, true) : Dir d))|
        ≤ A * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) := h
      _ ≤ 2 ^ ((d : ℝ) - 1) * A * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) := by
          have : A ≤ 2 ^ ((d : ℝ) - 1) * A := by nlinarith
          exact mul_le_mul_of_nonneg_right this hy
  · have h := gR_gradient_of hC₀ hS hd R z i
    have hgn : graphNorm y ≤ graphNorm z + 1 := by
      rw [hi]
      calc graphNorm (z + dirVec ((i, true) : Dir d))
          ≤ graphNorm z + graphNorm (dirVec ((i, true) : Dir d)) := graphNorm_add_le _ _
        _ = graphNorm z + 1 := by rw [graphNorm_dirVec]
    have hshift := rpow_shift_le (d := d) hd hgn
    have heq : |gR R y - gR R z| = |gR R z - gR R (z + dirVec ((i, true) : Dir d))| := by
      rw [hi, abs_sub_comm]
    rw [heq]
    calc |gR R z - gR R (z + dirVec ((i, true) : Dir d))|
        ≤ A * (1 + (graphNorm z : ℝ)) ^ (1 - (d : ℝ)) := h
      _ ≤ A * (2 ^ ((d : ℝ) - 1) * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left hshift hAnn
      _ = 2 ^ ((d : ℝ) - 1) * A * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) := by ring

end LatticeProb

namespace LatticeProb

open Finset

/-- **The gradient of the truncated lazy Green function.**  Uniformly in the
horizon `R`, the truncated Green function of the lazy walk changes by at most
`C (1 + |y|)^{1-d}` between neighbouring sites. -/
theorem exists_gR_gradient (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℕ) (y z : Site d), z ∈ nbrFinset y →
      |gR R y - gR R z| ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) := by
  obtain ⟨C₀, hC₀pos, hS⟩ := exists_sum_rpow_exp_le d hd
  refine ⟨2 ^ ((d : ℝ) - 1) * (8 * gradConst d * C₀ + 2 ^ ((d : ℝ) - 1)), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 2 ^ ((d : ℝ) - 1) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) ≤ 8 * gradConst d * C₀ := by
      have := gradConst_nonneg d
      positivity
    nlinarith
  · exact fun R y z hz =>
      gR_gradient_nbr_of (le_of_lt hC₀pos) hS (by omega) R y z hz

/-- **The gradient of the Green function of the simple random walk**, in
dimension three and above: `|G(0,y) - G(0,z)| ≤ C (1 + |y|)^{1-d}` for
neighbouring `y` and `z`.  This is `eq:green-gradient` for the simple walk at
the infinite horizon, obtained from the lazy walk, which has no parity
obstruction, through the identity `G_lazy = 2 G_simple`. -/
theorem exists_srwGreenInf_gradient (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ y z : Site d, z ∈ nbrFinset y →
      |srwGreenInf d y - srwGreenInf d z|
        ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) := by
  obtain ⟨C, hCpos, hgrad⟩ := exists_gR_gradient d (by omega)
  refine ⟨C / 2, by positivity, fun y z hz => ?_⟩
  refine srwGreenInf_gradient_of (d := d) (C := C)
    (fun x => summable_iterate_delta0 hd x)
    (fun x => tsum_iterate_delta0_eq hd x) hgrad y z hz

end LatticeProb
