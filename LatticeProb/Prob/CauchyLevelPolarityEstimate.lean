import Mathlib
import LatticeProb.Prob.CauchyLevelFirstHit
import LatticeProb.Prob.CauchyLevelSmallBallLower

/-!
# Polarity estimate for the level process on a dyadic grid of levels

Let `Y = cauchyLevel` be the level process of two independent pairs of independent Brownian
paths, under `ν = (W ⊗ W) ⊗ (W ⊗ W)`. For `0 < α ≤ β`, a dyadic mesh `h = 2^{-n}` and
`h ≤ r ≤ 1/4`,

  `ν {∃ i, α + i h ∈ [α, β], |Y (α + i h)| ≤ r} ≤ C(α, β) / log (1 / r)`,

with a constant `C(α, β)` depending only on `α` and `β`.

The proof combines three inputs:
* the first-hit decomposition along the grid `a_k = α + k h`
  (`measure_exists_abs_cauchyLevel_le_mul_sum_le`):
  `ν {∃ k ≤ K, |Y a_k| ≤ r} * ∑_{i=1}^{M} ν {|Y (i h)| ≤ r} ≤ ∑_{j=0}^{K+M} ν {|Y a_j| ≤ 2 r}`;
* the small-ball upper bound at a fixed level (`measure_abs_cauchyLevel_le`):
  `ν {|Y a| ≤ r} ≤ C₁ r / a`, which bounds the right side by `C (β - α + 2) r / (α h)`;
* the small-ball lower bound at a fixed level (`le_measure_abs_cauchyLevel_le`):
  `ν {|Y a| ≤ r} ≥ c₂ min 1 (r / (√2 a))`, which bounds the harmonic sum on the left side, with
  `M h = 1`, below by `c (r / h) log (1 / r)`.

## Main results

* `log_sub_log_le_sum_div`, `div_mul_log_le_sum_min`: lower bounds for harmonic sums.
* `measure_exists_grid_abs_le_div_log`: the polarity estimate for any level process satisfying the
  three inputs above.
* `measure_exists_dyadicLevel_abs_cauchyLevel_le`: the polarity estimate for `cauchyLevel` with the
  explicit constant `cauchyLevelPolarityConst α β`.
* `exists_measure_dyadicLevel_abs_cauchyLevel_le_div_log`: the same estimate in the form
  `∃ C r₀ > 0, ∀ n r, 2^{-n} ≤ r ≤ r₀ → ν {…} ≤ C / log (1 / r)`.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

section HarmonicSum

/-- Telescoping lower bound for a harmonic sum: for `h, r > 0`,
`log ((M + 1) h + r) - log (h + r) ≤ ∑_{i=1}^{M} h / (i h + r)`. -/
theorem log_sub_log_le_sum_div {h r : ℝ} (hh : 0 < h) (hr : 0 < r) (M : ℕ) :
    Real.log (((M : ℝ) + 1) * h + r) - Real.log (h + r) ≤
      ∑ i ∈ Finset.Icc 1 M, h / ((i : ℝ) * h + r) := by
  induction M with
  | zero =>
    rw [Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by omega)]
    simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega)]
    have ha : 0 < ((M + 1 : ℕ) : ℝ) * h + r :=
      add_pos (mul_pos (Nat.cast_pos.2 (Nat.succ_pos M)) hh) hr
    have hx : 0 < (((M + 1 : ℕ) : ℝ) + 1) * h + r :=
      add_pos (mul_pos (by positivity) hh) hr
    have hstep : Real.log ((((M + 1 : ℕ) : ℝ) + 1) * h + r) -
        Real.log (((M + 1 : ℕ) : ℝ) * h + r) ≤ h / (((M + 1 : ℕ) : ℝ) * h + r) := by
      have hlog := Real.log_le_sub_one_of_pos (div_pos hx ha)
      rw [Real.log_div hx.ne' ha.ne', div_sub_one ha.ne'] at hlog
      refine hlog.trans_eq ?_
      congr 1
      ring
    push_cast at hstep ⊢
    linarith

/-- Lower bound for the sum of the small-ball profile `min 1 (r / (√2 i h))` over a grid of mesh
`h` covering `[h, 1]`: for `0 < h ≤ r ≤ 1/4` and `M h = 1`,
`(r / h) log (1 / r) / (2 √2) ≤ ∑_{i=1}^{M} min 1 (r / (√2 i h))`. -/
theorem div_mul_log_le_sum_min {h r : ℝ} (hh : 0 < h) (hhr : h ≤ r) (hr : r ≤ 1 / 4) {M : ℕ}
    (hM : (M : ℝ) * h = 1) :
    r / h * (Real.log (1 / r) / (2 * √2)) ≤
      ∑ i ∈ Finset.Icc 1 M, min 1 (r / (√2 * ((i : ℝ) * h))) := by
  have hr0 : 0 < r := hh.trans_le hhr
  have hs1 : 1 ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
  have hs0 : 0 < √2 := Real.sqrt_pos.2 two_pos
  have hterm : ∀ i ∈ Finset.Icc 1 M,
      r / (√2 * h) * (h / ((i : ℝ) * h + r)) ≤ min 1 (r / (√2 * ((i : ℝ) * h))) := by
    intro i hi
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Icc.1 hi).1
    have hih : 0 < (i : ℝ) * h := mul_pos (by linarith) hh
    have hden : 0 < √2 * ((i : ℝ) * h + r) := mul_pos hs0 (add_pos hih hr0)
    rw [div_mul_div_comm, mul_right_comm (√2) h, mul_div_mul_right _ _ hh.ne']
    refine le_min ?_ ?_
    · rw [div_le_iff₀ hden, one_mul]
      have := mul_le_mul_of_nonneg_right hs1 (add_pos hih hr0).le
      linarith
    · exact div_le_div_of_nonneg_left hr0.le (mul_pos hs0 hih)
        (mul_le_mul_of_nonneg_left (by linarith) hs0.le)
  have hlog := log_sub_log_le_sum_div hh hr0 M
  have h1 : 0 ≤ Real.log (((M : ℝ) + 1) * h + r) :=
    Real.log_nonneg (by rw [add_mul, hM]; linarith)
  have h2 : Real.log (h + r) ≤ Real.log (2 * r) :=
    Real.log_le_log (add_pos hh hr0) (by linarith)
  have h3 : Real.log (1 / r) / 2 ≤ -Real.log (2 * r) := by
    have hsq : Real.log ((2 * r) ^ 2) ≤ Real.log r :=
      Real.log_le_log (pow_pos (mul_pos two_pos hr0) 2)
        (by nlinarith [mul_le_mul_of_nonneg_left hr hr0.le])
    rw [Real.log_pow] at hsq
    push_cast at hsq
    rw [one_div, Real.log_inv]
    linarith
  have hc : 0 < r / (√2 * h) := div_pos hr0 (mul_pos hs0 hh)
  calc r / h * (Real.log (1 / r) / (2 * √2))
      = r / (√2 * h) * (Real.log (1 / r) / 2) := by ring
    _ ≤ r / (√2 * h) * (Real.log (((M : ℝ) + 1) * h + r) - Real.log (h + r)) :=
        mul_le_mul_of_nonneg_left (by linarith) hc.le
    _ ≤ r / (√2 * h) * ∑ i ∈ Finset.Icc 1 M, h / ((i : ℝ) * h + r) :=
        mul_le_mul_of_nonneg_left hlog hc.le
    _ = ∑ i ∈ Finset.Icc 1 M, r / (√2 * h) * (h / ((i : ℝ) * h + r)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.Icc 1 M, min 1 (r / (√2 * ((i : ℝ) * h))) := Finset.sum_le_sum hterm

end HarmonicSum

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {Y : ℝ → Ω → ℝ}

/-- **Polarity estimate on a dyadic grid of levels (abstract form).** Let `Y` be a process indexed
by levels such that, at every level `a > 0` and radius `r ≥ 0`,
`c₂ min 1 (r / (√2 a)) ≤ ν {|Y a| ≤ r} ≤ c₁ r / a`, and which satisfies the first-hit inequality
along arithmetic grids `a_k = α + k h`. Then for `0 < α ≤ β`, `h = 2^{-n}` and `h ≤ r ≤ 1/4`,
`ν {∃ i, α + i h ∈ [α, β], |Y (α + i h)| ≤ r} ≤ (4 √2 c₁ (β - α + 2) / (α c₂)) / log (1 / r)`.

The proof takes `K = ⌊(β - α) / h⌋` and `M = 2^n` (so `M h = 1`) in the first-hit inequality,
bounds its right side above by `2 c₁ (β - α + 2) r / (α h)` termwise, and its harmonic sum below by
`c₂ (r / h) log (1 / r) / (2 √2)` (`div_mul_log_le_sum_min`). -/
theorem measure_exists_grid_abs_le_div_log {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂)
    (hup : ∀ a : ℝ, 0 < a → ∀ r : ℝ, 0 ≤ r →
      ν {q | |Y a q| ≤ r} ≤ ENNReal.ofReal (c₁ * r / a))
    (hlow : ∀ a : ℝ, 0 < a → ∀ r : ℝ, 0 ≤ r →
      ENNReal.ofReal (c₂ * min 1 (r / (√2 * a))) ≤ ν {q | |Y a q| ≤ r})
    (hfh : ∀ α h : ℝ, 0 ≤ α → 0 ≤ h → ∀ (r : ℝ) (K M : ℕ),
      ν {q | ∃ k ≤ K, |Y (α + k * h) q| ≤ r} *
          ∑ i ∈ Finset.Icc 1 M, ν {q | |Y (i * h) q| ≤ r} ≤
        ∑ j ∈ Finset.range (K + M + 1), ν {q | |Y (α + j * h) q| ≤ 2 * r})
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (n : ℕ) {r : ℝ}
    (hhr : (2 : ℝ) ^ (-(n : ℤ)) ≤ r) (hr : r ≤ 1 / 4) :
    ν {q | ∃ i : ℕ, α + i * (2 : ℝ) ^ (-(n : ℤ)) ∈ Icc α β ∧
        |Y (α + i * (2 : ℝ) ^ (-(n : ℤ))) q| ≤ r} ≤
      ENNReal.ofReal (2 * c₁ * (β - α + 2) / α * (2 * √2) / c₂ / Real.log (1 / r)) := by
  have hh0 : 0 < (2 : ℝ) ^ (-(n : ℤ)) := zpow_pos two_pos _
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) = 1 :=
    ⟨2 ^ n, by
      rw [zpow_neg, zpow_natCast]
      push_cast
      exact mul_inv_cancel₀ (by positivity)⟩
  generalize (2 : ℝ) ^ (-(n : ℤ)) = h at hh0 hM hhr ⊢
  have hr0 : 0 < r := hh0.trans_le hhr
  have hh1 : h ≤ 1 := by linarith
  obtain ⟨K, hK, hKmem⟩ : ∃ K : ℕ, (K : ℝ) * h ≤ β - α ∧
      ∀ i : ℕ, (i : ℝ) * h ≤ β - α → i ≤ K :=
    ⟨⌊(β - α) / h⌋₊, (le_div_iff₀ hh0).1 (Nat.floor_le (div_nonneg (sub_nonneg.2 hαβ) hh0.le)),
      fun i hi => Nat.le_floor ((le_div_iff₀ hh0).2 hi)⟩
  have hsub : {q | ∃ i : ℕ, α + i * h ∈ Icc α β ∧ |Y (α + i * h) q| ≤ r} ⊆
      {q | ∃ k ≤ K, |Y (α + k * h) q| ≤ r} := by
    rintro q ⟨i, hi, hq⟩
    exact ⟨i, hKmem i (by linarith [hi.2]), hq⟩
  -- upper bound for the right side of the first-hit inequality
  have hU : ∑ j ∈ Finset.range (K + M + 1), ν {q | |Y (α + j * h) q| ≤ 2 * r} ≤
      ENNReal.ofReal (2 * c₁ * (β - α + 2) / α * (r / h)) := by
    calc ∑ j ∈ Finset.range (K + M + 1), ν {q | |Y (α + j * h) q| ≤ 2 * r}
        ≤ ∑ _j ∈ Finset.range (K + M + 1), ENNReal.ofReal (2 * c₁ * r / α) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hj : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg j) hh0.le
          refine (hup _ (add_pos_of_pos_of_nonneg hα hj) _ (by linarith)).trans
            (ENNReal.ofReal_le_ofReal ?_)
          calc c₁ * (2 * r) / (α + j * h) ≤ c₁ * (2 * r) / α :=
                div_le_div_of_nonneg_left (mul_nonneg hc₁ (by linarith)) hα
                  (le_add_of_nonneg_right hj)
            _ = 2 * c₁ * r / α := by ring
      _ = ENNReal.ofReal (((K + M + 1 : ℕ) : ℝ) * (2 * c₁ * r / α)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_mul (p := ((K + M + 1 : ℕ) : ℝ)) (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (2 * c₁ * (β - α + 2) / α * (r / h)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hcount : ((K + M + 1 : ℕ) : ℝ) ≤ (β - α + 2) / h := by
            rw [le_div_iff₀ hh0]
            push_cast
            linarith [show ((K : ℝ) + M + 1) * h = K * h + M * h + h by ring]
          calc ((K + M + 1 : ℕ) : ℝ) * (2 * c₁ * r / α)
              ≤ (β - α + 2) / h * (2 * c₁ * r / α) :=
                mul_le_mul_of_nonneg_right hcount
                  (div_nonneg (mul_nonneg (mul_nonneg zero_le_two hc₁) hr0.le) hα.le)
            _ = 2 * c₁ * (β - α + 2) / α * (r / h) := by ring
  -- lower bound for the harmonic sum on the left side
  have hL : ENNReal.ofReal (c₂ * Real.log (1 / r) / (2 * √2) * (r / h)) ≤
      ∑ i ∈ Finset.Icc 1 M, ν {q | |Y (i * h) q| ≤ r} := by
    calc ENNReal.ofReal (c₂ * Real.log (1 / r) / (2 * √2) * (r / h))
        ≤ ENNReal.ofReal (∑ i ∈ Finset.Icc 1 M, c₂ * min 1 (r / (√2 * ((i : ℝ) * h)))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Finset.mul_sum]
          calc c₂ * Real.log (1 / r) / (2 * √2) * (r / h)
              = c₂ * (r / h * (Real.log (1 / r) / (2 * √2))) := by ring
            _ ≤ c₂ * ∑ i ∈ Finset.Icc 1 M, min 1 (r / (√2 * ((i : ℝ) * h))) :=
                mul_le_mul_of_nonneg_left (div_mul_log_le_sum_min hh0 hhr hr hM) hc₂.le
      _ = ∑ i ∈ Finset.Icc 1 M, ENNReal.ofReal (c₂ * min 1 (r / (√2 * ((i : ℝ) * h)))) :=
          ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg hc₂.le
            (le_min zero_le_one (div_nonneg hr0.le
              (mul_nonneg (Real.sqrt_nonneg 2) (mul_nonneg (Nat.cast_nonneg i) hh0.le))))
      _ ≤ ∑ i ∈ Finset.Icc 1 M, ν {q | |Y (i * h) q| ≤ r} :=
          Finset.sum_le_sum fun i hi => hlow _
            (mul_pos (Nat.cast_pos.2 (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.1 hi).1))
              hh0) _ hr0.le
  have hℓ : 0 < Real.log (1 / r) := Real.log_pos (by rw [lt_div_iff₀ hr0]; linarith)
  have hA : 0 < c₂ * Real.log (1 / r) / (2 * √2) * (r / h) :=
    mul_pos (div_pos (mul_pos hc₂ hℓ) (by positivity)) (div_pos hr0 hh0)
  have hmain : ν {q | ∃ i : ℕ, α + i * h ∈ Icc α β ∧ |Y (α + i * h) q| ≤ r} *
      ENNReal.ofReal (c₂ * Real.log (1 / r) / (2 * √2) * (r / h)) ≤
      ENNReal.ofReal (2 * c₁ * (β - α + 2) / α * (r / h)) :=
    calc ν {q | ∃ i : ℕ, α + i * h ∈ Icc α β ∧ |Y (α + i * h) q| ≤ r} *
          ENNReal.ofReal (c₂ * Real.log (1 / r) / (2 * √2) * (r / h))
        ≤ ν {q | ∃ k ≤ K, |Y (α + k * h) q| ≤ r} *
          ∑ i ∈ Finset.Icc 1 M, ν {q | |Y (i * h) q| ≤ r} :=
          (mul_le_mul_of_nonneg_right (measure_mono hsub) zero_le).trans
            (mul_le_mul_of_nonneg_left hL zero_le)
      _ ≤ ∑ j ∈ Finset.range (K + M + 1), ν {q | |Y (α + j * h) q| ≤ 2 * r} :=
          hfh α h hα.le hh0.le r K M
      _ ≤ ENNReal.ofReal (2 * c₁ * (β - α + 2) / α * (r / h)) := hU
  have hP := (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hA).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2 hmain
  rw [← ENNReal.ofReal_div_of_pos hA, mul_div_mul_right _ _ (div_pos hr0 hh0).ne',
    div_div_eq_mul_div] at hP
  refine hP.trans_eq ?_
  rw [div_div]

end Abstract

/-- The constant `C(α, β)` of the polarity estimate for the level process:
`4 √2 c₁ (β - α + 2) / (α c₂)` with `c₁ = 8 / √(2π)` (small-ball upper bound) and
`c₂ = 2 e^{-1/2} / √(2π) · Φ(-1)²` (small-ball lower bound). -/
def cauchyLevelPolarityConst (α β : ℝ) : ℝ :=
  2 * (8 / √(2 * Real.pi)) * (β - α + 2) / α * (2 * √2) /
    (2 * Real.exp (-(1 / 2)) / √(2 * Real.pi) * (gaussianReal 0 1 (Iic (-1)) ^ 2).toReal)

/-- The squared standard Gaussian mass of `(-∞, -1]` is positive. -/
theorem gaussianReal_Iic_neg_one_sq_toReal_pos :
    0 < (gaussianReal 0 1 (Iic (-1 : ℝ)) ^ 2).toReal := by
  have hΦ : gaussianReal 0 1 (Iic (-1 : ℝ)) ≠ 0 := by
    intro h0
    have h' := gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
    simp at h'
  exact ENNReal.toReal_pos (pow_ne_zero 2 hΦ) (ENNReal.pow_ne_top (measure_ne_top _ _))

/-- The constant of the polarity estimate is positive for `0 < α ≤ β`. -/
theorem cauchyLevelPolarityConst_pos {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    0 < cauchyLevelPolarityConst α β := by
  have hg := gaussianReal_Iic_neg_one_sq_toReal_pos
  have hX : 0 < β - α + 2 := by linarith
  have hs : (0 : ℝ) < √(2 * Real.pi) := by positivity
  unfold cauchyLevelPolarityConst
  exact div_pos (mul_pos (div_pos (mul_pos (mul_pos two_pos (div_pos (by norm_num) hs)) hX) hα)
    (by positivity)) (mul_pos (div_pos (mul_pos two_pos (Real.exp_pos _)) hs) hg)

section PathLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- **Polarity estimate for the level process on a dyadic grid of levels.** Under
`ν = (W ⊗ W) ⊗ (W ⊗ W)`, `W` the Brownian path law, for `0 < α ≤ β`, `h = 2^{-n}` and
`h ≤ r ≤ 1/4`,
`ν {∃ i, α + i h ∈ [α, β], |cauchyLevel (α + i h)| ≤ r} ≤ C(α, β) / log (1 / r)`
with `C(α, β) = cauchyLevelPolarityConst α β`. -/
theorem measure_exists_dyadicLevel_abs_cauchyLevel_le (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (n : ℕ) {r : ℝ}
    (hhr : (2 : ℝ) ^ (-(n : ℤ)) ≤ r) (hr : r ≤ 1 / 4) :
    (((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
        ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))))
        {q | ∃ i : ℕ, α + i * (2 : ℝ) ^ (-(n : ℤ)) ∈ Icc α β ∧
          |cauchyLevel (α + i * (2 : ℝ) ^ (-(n : ℤ))) q| ≤ r} ≤
      ENNReal.ofReal (cauchyLevelPolarityConst α β / Real.log (1 / r)) := by
  have hne : gaussianReal 0 1 (Iic (-1 : ℝ)) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (measure_ne_top _ _)
  have hc₂ : 0 < 2 * Real.exp (-(1 / 2)) / √(2 * Real.pi) *
      (gaussianReal 0 1 (Iic (-1 : ℝ)) ^ 2).toReal :=
    mul_pos (by positivity) gaussianReal_Iic_neg_one_sq_toReal_pos
  refine measure_exists_grid_abs_le_div_log (Y := cauchyLevel) (c₁ := 8 / √(2 * Real.pi))
    (c₂ := 2 * Real.exp (-(1 / 2)) / √(2 * Real.pi) *
      (gaussianReal 0 1 (Iic (-1 : ℝ)) ^ 2).toReal)
    (by positivity) hc₂ ?_ ?_ ?_ hα hαβ n hhr hr
  · intro a ha s hs
    refine (measure_abs_cauchyLevel_le hB hm hcont ha hs).trans_eq ?_
    rw [← ENNReal.ofReal_mul (p := 2 * s / √(2 * Real.pi))
      (div_nonneg (by linarith) (Real.sqrt_nonneg _))]
    congr 1
    ring
  · intro a ha s hs
    refine le_trans (le_of_eq ?_) (le_measure_abs_cauchyLevel_le hB hm hcont ha hs)
    rw [mul_right_comm, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne]
  · intro α h hα hh s K M
    exact measure_exists_abs_cauchyLevel_le_mul_sum_le hB hm hcont hα hh s K M

/-- **Polarity estimate for the level process**, in the form
`∀ 0 < α < β, ∃ C r₀ > 0, ∀ n r, 2^{-n} ≤ r ≤ r₀ →
ν {∃ i, α + i 2^{-n} ∈ [α, β], |cauchyLevel (α + i 2^{-n})| ≤ r} ≤ C / log (1 / r)`.
The constants are `C = cauchyLevelPolarityConst α β` and `r₀ = 1/4`, which depend only on `α`
and `β`. -/
theorem exists_measure_dyadicLevel_abs_cauchyLevel_le_div_log (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ n : ℕ, ∀ r : ℝ, (2 : ℝ) ^ (-(n : ℤ)) ≤ r → r ≤ r₀ →
      (((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
          ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))))
          {q | ∃ i : ℕ, α + i * (2 : ℝ) ^ (-(n : ℤ)) ∈ Icc α β ∧
            |cauchyLevel (α + i * (2 : ℝ) ^ (-(n : ℤ))) q| ≤ r} ≤
        ENNReal.ofReal (C / Real.log (1 / r)) :=
  ⟨cauchyLevelPolarityConst α β, 1 / 4, cauchyLevelPolarityConst_pos hα hαβ.le, by norm_num,
    fun n _ hhr hr => measure_exists_dyadicLevel_abs_cauchyLevel_le hB hm hcont hα hαβ.le n hhr hr⟩

end PathLaw

end LatticeProb

end
