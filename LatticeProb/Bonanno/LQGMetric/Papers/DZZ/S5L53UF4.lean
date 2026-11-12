/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53UF4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53UF3

/-!
# DZZ Lemma 5.3 part 1, node 4: numerics (P2-DZZ53UF)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2516–2522 and the final count
l. 2414 (`P(𝒟ᶜ) ≤ e^{−L^{0.22}}`): with `K = 2^{⌊L^{0.51}⌋}`, `ε*⁻¹ ≤ 2 e^{α* √L log L}` and
`N ≤ C_mc L/log 2 + 2 n_{ε*}`, `e^{−L^{0.23}} + 2(N+1)(800/ε*)·2K⁻⁴ ≤ e^{−L^{0.22}}/2` for large `L`.
Own elementary estimates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- `α √L log L ≤ L^{0.51}/8` and `log L ≤ L^{0.51}/8` for large `L` -/
lemma l53uf_ev_log (αs : ℝ) (hαs : 0 ≤ αs) : ∀ᶠ L : ℝ in atTop,
    αs * Real.sqrt L * Real.log L ≤ L ^ (0.51 : ℝ) / 8 ∧ Real.log L ≤ L ^ (0.51 : ℝ) / 8 := by
  have h1 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 0.01 by norm_num)).bound
    (show (0 : ℝ) < 1 / (8 * (αs + 1)) by positivity)
  have h2 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 0.51 by norm_num)).bound
    (show (0 : ℝ) < 1 / 8 by norm_num)
  filter_upwards [h1, h2, eventually_ge_atTop (1 : ℝ)] with L hL1 hL2 hL
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by positivity)] at hL1 hL2
  refine ⟨?_, by linarith⟩
  have hs : Real.sqrt L = L ^ (0.5 : ℝ) := by rw [Real.sqrt_eq_rpow]; norm_num
  have e : L ^ (0.51 : ℝ) = L ^ (0.5 : ℝ) * L ^ (0.01 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  rw [hs, e]
  have h5 : 0 ≤ L ^ (0.5 : ℝ) := by positivity
  have h01 : 0 ≤ L ^ (0.01 : ℝ) := by positivity
  have hq : αs / (αs + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  calc αs * L ^ (0.5 : ℝ) * Real.log L
      ≤ αs * L ^ (0.5 : ℝ) * (1 / (8 * (αs + 1)) * L ^ (0.01 : ℝ)) := by gcongr
    _ = (αs / (αs + 1)) * (L ^ (0.5 : ℝ) * L ^ (0.01 : ℝ)) / 8 := by
        field_simp
    _ ≤ 1 * (L ^ (0.5 : ℝ) * L ^ (0.01 : ℝ)) / 8 := by gcongr
    _ = _ := by ring

/-- `K⁻⁴ ≤ e^{3 − 2.7 L^{0.51}}` -/
lemma l53uf_K_le {L : ℝ} (hL : 0 ≤ L) :
    ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 ≤ Real.exp (3 - 2.7 * L ^ (0.51 : ℝ)) := by
  have h51 : 0 ≤ L ^ (0.51 : ℝ) := by positivity
  have hfl : L ^ (0.51 : ℝ) - 1 ≤ (⌊L ^ (0.51 : ℝ)⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (L ^ (0.51 : ℝ)); linarith
  have e : ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 =
      Real.exp (-(4 * Real.log 2 * (⌊L ^ (0.51 : ℝ)⌋₊ : ℝ))) := by
    have h2 : (2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊ =
        Real.exp ((⌊L ^ (0.51 : ℝ)⌋₊ : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log two_pos]
    rw [h2, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [e]
  refine Real.exp_le_exp.2 ?_
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have h0 : (0 : ℝ) ≤ (⌊L ^ (0.51 : ℝ)⌋₊ : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **The numerics of node 4** (`L = log δ⁻¹`, `Z = ε*⁻¹`, `Nr = N + 1`). -/
lemma l53uf_numerics (αs Cm A : ℝ) (hαs : 0 ≤ αs) (hCm : 0 ≤ Cm) (hA : 0 < A) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 2 / A ≤ Real.exp (L ^ (0.6 : ℝ)) ∧
      ∀ Z Nr : ℝ, 0 ≤ Z → Z ≤ 2 * Real.exp (αs * Real.sqrt L * Real.log L) → 0 ≤ Nr →
        Nr ≤ L / Real.log 2 * Cm + 2 * Z + 1 →
        2 ^ 13 * Z / A ≤ Real.exp (L ^ (0.6 : ℝ)) ∧
        Real.exp (-L ^ (0.23 : ℝ)) +
            2 * Nr * (800 * Z * (2 * ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4)) ≤
          Real.exp (-L ^ (0.22 : ℝ)) / 2 := by
  set D : ℝ := 6400 * (2 * Cm + 5) with hD
  have hD0 : 0 < D := by positivity
  have t6 := tendsto_rpow_atTop (show (0 : ℝ) < 0.6 by norm_num)
  have t51 := tendsto_rpow_atTop (show (0 : ℝ) < 0.51 by norm_num)
  have t01 := tendsto_rpow_atTop (show (0 : ℝ) < 0.01 by norm_num)
  have t22 := tendsto_rpow_atTop (show (0 : ℝ) < 0.22 by norm_num)
  filter_upwards [l53uf_ev_log αs hαs, eventually_ge_atTop (1 : ℝ),
    t6.eventually_ge_atTop (2 * (|Real.log (2 ^ 14 / A)| + |Real.log (2 / A)|)),
    t51.eventually_ge_atTop (|Real.log D| + 3 + Real.log 4),
    t01.eventually_ge_atTop 2, t22.eventually_ge_atTop 2] with L hlog hL1 h6 h51 h01 h22
  obtain ⟨hX, hlogL⟩ := hlog
  have hL0 : 0 < L := by linarith
  set Y := L ^ (0.51 : ℝ) with hY
  have hY6 : Y ≤ L ^ (0.6 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h2251 : L ^ (0.22 : ℝ) ≤ Y := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hY0 : 0 ≤ Y := by positivity
  have hlog4 : Real.log 4 < 1.39 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have hlog4' : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  refine ⟨hL1, ?_, fun Z Nr hZ0 hZ hN0 hN => ?_⟩
  · rw [← Real.exp_log (show 0 < 2 / A by positivity)]
    refine Real.exp_le_exp.2 ?_
    have := le_abs_self (Real.log (2 / A))
    have := abs_nonneg (Real.log (2 ^ 14 / A))
    linarith
  have hZ' : Z ≤ 2 * Real.exp (Y / 8) := hZ.trans (by gcongr)
  have hLY : L ≤ Real.exp (Y / 8) := by
    rw [← Real.exp_log hL0]; exact Real.exp_le_exp.2 hlogL
  have hE1 : 1 ≤ Real.exp (Y / 8) := Real.one_le_exp (by positivity)
  refine ⟨?_, ?_⟩
  · calc 2 ^ 13 * Z / A ≤ 2 ^ 13 * (2 * Real.exp (Y / 8)) / A := by gcongr
      _ = 2 ^ 14 / A * Real.exp (Y / 8) := by ring
      _ = Real.exp (Real.log (2 ^ 14 / A) + Y / 8) := by
          rw [Real.exp_add, Real.exp_log (by positivity)]
      _ ≤ Real.exp (L ^ (0.6 : ℝ)) := by
          refine Real.exp_le_exp.2 ?_
          have := le_abs_self (Real.log (2 ^ 14 / A))
          have := abs_nonneg (Real.log (2 / A))
          linarith
  -- the main term
  have hNr : Nr ≤ (2 * Cm + 5) * Real.exp (Y / 8) := by
    have h1 : L / Real.log 2 * Cm ≤ 2 * Cm * Real.exp (Y / 8) := by
      have : L / Real.log 2 ≤ 2 * L := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      calc L / Real.log 2 * Cm ≤ 2 * L * Cm := by gcongr
        _ ≤ 2 * Real.exp (Y / 8) * Cm := by gcongr
        _ = _ := by ring
    nlinarith
  have hK := l53uf_K_le hL0.le
  rw [← hY] at hK
  have hK0 : 0 ≤ ((2 : ℝ) ^ ⌊Y⌋₊)⁻¹ ^ 4 := by positivity
  have hmain : 2 * Nr * (800 * Z * (2 * ((2 : ℝ) ^ ⌊Y⌋₊)⁻¹ ^ 4)) ≤
      Real.exp (-L ^ (0.22 : ℝ)) / 4 := by
    calc 2 * Nr * (800 * Z * (2 * ((2 : ℝ) ^ ⌊Y⌋₊)⁻¹ ^ 4))
        ≤ 2 * ((2 * Cm + 5) * Real.exp (Y / 8)) *
          (800 * (2 * Real.exp (Y / 8)) * (2 * Real.exp (3 - 2.7 * Y))) := by gcongr
      _ = D * Real.exp (Y / 8 + Y / 8 + (3 - 2.7 * Y)) := by
          rw [hD, Real.exp_add, Real.exp_add]; ring
      _ = Real.exp (Real.log D + (Y / 8 + Y / 8 + (3 - 2.7 * Y))) := by
          rw [Real.exp_add (Real.log D), Real.exp_log hD0]
      _ ≤ Real.exp (-L ^ (0.22 : ℝ) - Real.log 4) := by
          refine Real.exp_le_exp.2 ?_
          have := le_abs_self (Real.log D)
          linarith
      _ = Real.exp (-L ^ (0.22 : ℝ)) / 4 := by
          rw [Real.exp_sub, Real.exp_log (by norm_num)]
  have h23 : Real.exp (-L ^ (0.23 : ℝ)) ≤ Real.exp (-L ^ (0.22 : ℝ)) / 4 := by
    have e : L ^ (0.23 : ℝ) = L ^ (0.22 : ℝ) * L ^ (0.01 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [← Real.exp_log (show (0 : ℝ) < 4 by norm_num), ← Real.exp_sub]
    refine Real.exp_le_exp.2 ?_
    rw [e]; nlinarith
  linarith

end DZZ
end LQGMetric
