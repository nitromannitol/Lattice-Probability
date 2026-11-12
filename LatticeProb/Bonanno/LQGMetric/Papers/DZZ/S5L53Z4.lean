/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53Z4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Z3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Defs

/-!
# DZZ Lemma 5.3 part 1, R2 at the chain boxes (P2-DZZ53Z, packet P-131R)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, (eq-M-A-upper-bound-bis) l. 2453–2456, at the scales of
decision D131 §3: chain box `b ⊆ 𝖢` of side `s_b = ε*² s_𝖢` (the L3.13 boxes, l. 2379),
sub-boxes of side `s_b/K`, `K = 2^{⌊L^{0.51}⌋}` (l. 2427), proxy scale
`2^{-m_b}`, `m_b = n_b + ⌊L^{0.51}⌋ + ℓ` with `2^ℓ ≤ C' L` (DV-D131-1).

* `l53_two_pow_j_le`: `2^{2 n_{ε*} + ⌊L^{0.51}⌋ + ℓ} ≤ e^{L^{0.55}}` for large `L` (own elementary
  estimate: `ε*⁻¹ ≤ 2 e^{α*√L log L}`, `log L ≤ L^{0.02}`).
* **`l53_domination_chainBox`**: (eq-M-A-upper-bound-bis) on `l53E4`, with DZZ's factor
  `δ² s_b^{−2} e^{L^{0.91}}`, on the rational balls of `sqBox(x, 5 s_b/K)` for every `x ∈ b`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `2^{n_{ε*}} ≤ 2 e^{|α*| √L |log L|}` (minimality of `epsStarN`) -/
lemma two_pow_epsStarN_le (αs δ : ℝ) :
    (2 : ℝ) ^ epsStarN αs δ ≤
      2 * Real.exp (|αs| * (Real.sqrt (Real.log δ⁻¹) * |Real.log (Real.log δ⁻¹)|)) := by
  set N := epsStarN αs δ with hN
  have hab : αs * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹) ≤
      |αs| * (Real.sqrt (Real.log δ⁻¹) * |Real.log (Real.log δ⁻¹)|) := by
    rw [mul_assoc]
    refine (le_abs_self _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hpos0 : 0 ≤ |αs| * (Real.sqrt (Real.log δ⁻¹) * |Real.log (Real.log δ⁻¹)|) := by positivity
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · rw [h0, pow_zero]
    have := Real.one_le_exp hpos0; linarith
  · have hmin : ¬ (2 : ℝ)⁻¹ ^ (N - 1) ≤ epsStarThr αs δ :=
      Nat.find_min (exists_two_pow_le_epsStarThr αs δ)
        (show N - 1 < Nat.find (exists_two_pow_le_epsStarThr αs δ) from Nat.sub_lt hpos one_pos)
    push Not at hmin
    unfold epsStarThr at hmin
    rw [Real.exp_neg, inv_pow] at hmin
    have h1 := (inv_lt_inv₀ (by positivity) (by positivity)).1 hmin
    have e : (2 : ℝ) ^ N = 2 * 2 ^ (N - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]
    have := Real.exp_le_exp.2 hab
    linarith

/-- **the scale bookkeeping**: `2^{2 n_{ε*} + ⌊L^{0.51}⌋ + ℓ} ≤ e^{L^{0.55}}` when `2^ℓ ≤ C' L`,
for large `L` -/
theorem l53_two_pow_j_le (αs C' : ℝ) :
    ∃ L₀ : ℝ, ∀ δ : ℝ, L₀ ≤ Real.log δ⁻¹ → ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ ≤ C' * Real.log δ⁻¹ →
      (2 : ℝ) ^ (2 * epsStarN αs δ + ⌊Real.log δ⁻¹ ^ (0.51 : ℝ)⌋₊ + ℓ) ≤
        Real.exp (Real.log δ⁻¹ ^ (0.55 : ℝ)) := by
  have hlo := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.02)).bound one_pos
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (hlo.and ((eventually_ge_atTop (1 : ℝ)).and
    ((l53z_ev_mul_rpow_le (4 + 2 * |αs|) (by norm_num : (0.52 : ℝ) < 0.55)).and
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.02)).eventually
        (eventually_ge_atTop (2 * |C'| + 1))))))
  refine ⟨L₀, fun δ hδ ℓ hℓ => ?_⟩
  set L := Real.log δ⁻¹ with hLdef
  obtain ⟨hlog, hL1, hpow, hC⟩ := hL₀ L hδ
  have hL0 : 0 < L := by linarith
  simp only [Real.norm_eq_abs, one_mul] at hlog
  rw [abs_of_nonneg (Real.log_nonneg hL1), abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hlog
  have e52 : L ^ (0.52 : ℝ) = L ^ (0.5 : ℝ) * L ^ (0.02 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have e51 : (L ^ (0.51 : ℝ)) ^ 2 = L * L ^ (0.02 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
      show (0.51 : ℝ) * ((2 : ℕ) : ℝ) = 1 + 0.02 by norm_num, Real.rpow_add hL0, Real.rpow_one]
  set l51 := L ^ (0.51 : ℝ)
  set l52 := L ^ (0.52 : ℝ)
  have hl51 : 0 ≤ l51 := Real.rpow_nonneg hL0.le _
  have h5152 : l51 ≤ l52 := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hl52 : 1 ≤ l52 := Real.one_le_rpow hL1 (by norm_num)
  -- `α* √L log L ≤ |α*| L^{0.52}`
  have hsq : Real.sqrt L * Real.log L ≤ l52 := by
    rw [e52, Real.sqrt_eq_rpow, show (1 / 2 : ℝ) = 0.5 by norm_num]
    exact mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hL0.le _)
  have hα : |αs| * (Real.sqrt L * |Real.log L|) ≤ |αs| * l52 := by
    rw [abs_of_nonneg (Real.log_nonneg hL1)]
    exact mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  have hN := two_pow_epsStarN_le αs δ
  rw [← hLdef] at hN
  -- `2^{⌊L^{0.51}⌋} ≤ e^{L^{0.51}}`
  have hk : (2 : ℝ) ^ ⌊l51⌋₊ ≤ Real.exp l51 := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    refine Real.exp_le_exp.2 ?_
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have := Nat.floor_le hl51
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  -- `2^ℓ ≤ C' L ≤ e^{L^{0.51}}`
  have hl : (2 : ℝ) ^ ℓ ≤ Real.exp l51 := by
    refine hℓ.trans ?_
    have hq := Real.quadratic_le_exp_of_nonneg hl51
    have : C' * L ≤ l51 ^ 2 / 2 := by
      rw [e51]
      have h1 : C' * L ≤ |C'| * L := mul_le_mul_of_nonneg_right (le_abs_self _) hL0.le
      nlinarith [abs_nonneg C']
    linarith
  have hsplit : (2 : ℝ) ^ (2 * epsStarN αs δ + ⌊l51⌋₊ + ℓ) =
      ((2 : ℝ) ^ epsStarN αs δ) ^ 2 * 2 ^ ⌊l51⌋₊ * 2 ^ ℓ := by
    rw [pow_add, pow_add, pow_mul']
  rw [hsplit]
  have hN2 : ((2 : ℝ) ^ epsStarN αs δ) ^ 2 ≤ 4 * Real.exp (2 * (|αs| * l52)) := by
    have h1 : (2 : ℝ) ^ epsStarN αs δ ≤ 2 * Real.exp (|αs| * l52) :=
      hN.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hα) (by norm_num))
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, ← Real.exp_nat_mul] at h2
    push_cast at h2; linarith
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp 1
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]; nlinarith
  calc ((2 : ℝ) ^ epsStarN αs δ) ^ 2 * 2 ^ ⌊l51⌋₊ * 2 ^ ℓ
      ≤ (Real.exp 2 * Real.exp (2 * (|αs| * l52))) * Real.exp l51 * Real.exp l51 := by
        gcongr
        exact hN2.trans (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le)
    _ = Real.exp (2 + 2 * (|αs| * l52) + l51 + l51) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (L ^ (0.55 : ℝ)) := by
        refine Real.exp_le_exp.2 ?_
        nlinarith [abs_nonneg αs]

end DZZ
end LQGMetric
