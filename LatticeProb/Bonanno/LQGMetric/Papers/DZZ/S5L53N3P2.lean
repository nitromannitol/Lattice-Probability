/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53N3P2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53NU2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Y2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Y3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53GA1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J10

/-!
# DZZ Lemma 5.3, node 3: the asymptotics of the parameter choice (P2-DZZ53N3P)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2502–2514 (the per-cell bound
`K 2^{-L²} + (4e(L²+2)/j)^j`), AUDIT-2026-10-03-N row N11 and §3.
* `l53n3_ev_room`: `(L² + 2) 2^{2 n_{ε*} + c} ≤ 2^{⌊L^{0.51}⌋}` for large `L = k log 2`
  (`n_{ε*} ≲ α* √L log L / log 2`, `two_pow_epsStarN_le`, S5L53Z4).
* `l53n3_ev_beta`: `4(2N+1) 2^{-(M+1)} + 32 · 2^{-M} ≤ e^{-L^{1.5}}` when `2N+2 ≤ e^{L^{0.51}}`
  and `M ≥ L²`.
Own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- **Room in the grid**: for every `c`, `(L² + 2) · 2^{2 n_{ε*} + c} ≤ 2^{⌊L^{0.51}⌋₊}` for
`L = k log 2` large. -/
lemma l53n3_ev_room (αs : ℝ) (c : ℕ) : ∃ L₀ : ℝ, ∀ k : ℕ, L₀ ≤ (k : ℝ) * Real.log 2 →
    (((k : ℝ) * Real.log 2) ^ 2 + 2) * (2 : ℝ) ^ (2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) + c) ≤
      (2 : ℝ) ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h12 : 0 ≤ Real.log (12 * 2 ^ c) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ 2 ^ c := one_le_pow₀ (by norm_num)
    linarith)
  set A : ℝ := Real.log (12 * 2 ^ c) + Real.log 2 + 2 + 2 * |αs| with hA
  have hlo := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.002)).bound one_pos
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (hlo.and ((eventually_ge_atTop (1 : ℝ)).and
    (l53z_ev_mul_rpow_le (A / Real.log 2) (by norm_num : (0.502 : ℝ) < 0.51))))
  refine ⟨L₀, fun k hk => ?_⟩
  set L : ℝ := (k : ℝ) * Real.log 2 with hLdef
  obtain ⟨hlog, hL1, hAL⟩ := hL₀ L hk
  have hL0 : 0 < L := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hlog
  have hN := two_pow_epsStarN_le αs ((2 : ℝ)⁻¹ ^ k)
  rw [l53nu_log_delta k, ← hLdef] at hN
  set n := epsStarN αs ((2 : ℝ)⁻¹ ^ k)
  set P : ℝ := L ^ (0.502 : ℝ) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hL1 (by norm_num)
  have hQP : L ^ (0.002 : ℝ) ≤ P := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hsq : Real.sqrt L * |Real.log L| ≤ P := by
    rw [Real.sqrt_eq_rpow, hP, show (0.502 : ℝ) = 1 / 2 + 0.002 by norm_num,
      Real.rpow_add hL0]
    exact mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hL0.le _)
  have h2n : (2 : ℝ) ^ n ≤ 2 * Real.exp (|αs| * P) :=
    hN.trans (by gcongr)
  have hLe : L ≤ Real.exp (L ^ (0.002 : ℝ)) := by
    calc L = Real.exp (Real.log L) := (Real.exp_log hL0).symm
      _ ≤ _ := Real.exp_le_exp.2 ((le_abs_self _).trans hlog)
  have hL2 : L ^ 2 + 2 ≤ 3 * Real.exp (2 * L ^ (0.002 : ℝ)) := by
    have h1 : L ^ 2 ≤ Real.exp (L ^ (0.002 : ℝ)) ^ 2 := pow_le_pow_left₀ hL0.le hLe 2
    rw [exp_sq_eq] at h1
    nlinarith
  have hpow : (2 : ℝ) ^ (2 * n + c) = ((2 : ℝ) ^ n) ^ 2 * 2 ^ c := by
    rw [pow_add, pow_mul, ← pow_mul, ← pow_mul, mul_comm n 2]
  have hlhs : (L ^ 2 + 2) * (2 : ℝ) ^ (2 * n + c) ≤
      Real.exp (Real.log (12 * 2 ^ c) + 2 * L ^ (0.002 : ℝ) + 2 * (|αs| * P)) := by
    rw [hpow, Real.exp_add, Real.exp_add, Real.exp_log (by positivity)]
    have h2 : ((2 : ℝ) ^ n) ^ 2 ≤ 4 * Real.exp (2 * (|αs| * P)) := by
      calc ((2 : ℝ) ^ n) ^ 2 ≤ (2 * Real.exp (|αs| * P)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h2n 2
        _ = 4 * Real.exp (2 * (|αs| * P)) := by rw [mul_pow, exp_sq_eq]; norm_num
    calc (L ^ 2 + 2) * (((2 : ℝ) ^ n) ^ 2 * 2 ^ c)
        ≤ (3 * Real.exp (2 * L ^ (0.002 : ℝ))) * ((4 * Real.exp (2 * (|αs| * P))) * 2 ^ c) := by
          gcongr
      _ = _ := by ring
  have hκ : L ^ (0.51 : ℝ) - 1 ≤ (⌊L ^ (0.51 : ℝ)⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (L ^ (0.51 : ℝ)); linarith
  have hrhs : Real.exp ((L ^ (0.51 : ℝ) - 1) * Real.log 2) ≤
      (2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊ := by
    rw [two_pow_eq_exp]; exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hκ hl2.le)
  refine hlhs.trans (le_trans (Real.exp_le_exp.2 ?_) hrhs)
  have hAL' : A * P ≤ Real.log 2 * L ^ (0.51 : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hl2] at hAL; linarith
  have hαP : 0 ≤ |αs| := abs_nonneg _
  nlinarith

/-- **The per-cell bound**: `4(2N+1) 2^{-(M+1)} + 32 · 2^{-M} ≤ e^{-L^{1.5}}` for large `L` when
`2N+2 ≤ e^{L^{0.51}}` and `L² ≤ M`. -/
lemma l53n3_ev_beta : ∀ᶠ L : ℝ in atTop, ∀ N M : ℕ,
    (2 * N + 2 : ℝ) ≤ Real.exp (L ^ (0.51 : ℝ)) → L ^ 2 ≤ M →
    4 * ((2 * N + 1 : ℝ) * (2 : ℝ)⁻¹ ^ (M + 1)) + 32 * (2 : ℝ)⁻¹ ^ M ≤
      Real.exp (-L ^ (1.5 : ℝ)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    l53z_ev_mul_rpow_le ((Real.log 34 + 2) / Real.log 2) (by norm_num : (1.5 : ℝ) < 2)]
    with L hL1 hA N M hN hM
  have hL0 : 0 < L := by linarith
  rw [Real.rpow_two, div_mul_eq_mul_div, div_le_iff₀ hl2] at hA
  have h1 : 1 ≤ L ^ (1.5 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have h51 : L ^ (0.51 : ℝ) ≤ L ^ (1.5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h34 : 0 ≤ Real.log 34 := Real.log_nonneg (by norm_num)
  have hq : (2 : ℝ)⁻¹ ^ M ≤ Real.exp (-(L ^ 2 * Real.log 2)) := by
    rw [inv_two_pow_eq_exp]
    exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hM hl2.le))
  have hq0 : 0 ≤ (2 : ℝ)⁻¹ ^ M := by positivity
  have e1 : (2 : ℝ)⁻¹ ^ (M + 1) = (2 : ℝ)⁻¹ ^ M / 2 := by rw [pow_succ]; ring
  have hE : 1 ≤ Real.exp (L ^ (0.51 : ℝ)) := Real.one_le_exp (by positivity)
  calc 4 * ((2 * N + 1 : ℝ) * (2 : ℝ)⁻¹ ^ (M + 1)) + 32 * (2 : ℝ)⁻¹ ^ M
      = (2 * (2 * N + 1) + 32) * (2 : ℝ)⁻¹ ^ M := by rw [e1]; ring
    _ ≤ (34 * Real.exp (L ^ (0.51 : ℝ))) * Real.exp (-(L ^ 2 * Real.log 2)) := by
        gcongr
        linarith
    _ = Real.exp (Real.log 34 + L ^ (0.51 : ℝ) - L ^ 2 * Real.log 2) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (-L ^ (1.5 : ℝ)) := Real.exp_le_exp.2 (by nlinarith)

end DZZ
end LQGMetric
