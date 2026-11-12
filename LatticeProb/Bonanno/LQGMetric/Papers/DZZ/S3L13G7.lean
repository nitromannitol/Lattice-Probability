/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13G7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13G6

/-!
# DZZ Lemma 3.13: the cell-geometric node `L313GeomC` and the lemma (P2-DZZ313G)

Ding–Zeitouni–Zhang arXiv:1807.00422 `LBM_LGDarXiv.tex` l. 1325–1340 (proof of Lemma 3.13).

* `l313_len_asym`: for small `δ`, `ε* ≤ 1/16` (`epsStarN ≥ 4`) and `(ε*)^{-4} ≤ e^{(log δ⁻¹)^{0.6}}` (own
  elementary asymptotics: `(ε*)^{-2} ≤ 4 e^{2X}` by minimality of `ε*`, `X = α* √L log L`,
  `log L ≤ 20 L^{1/20}`), so `d ≤ d₀ (ε*)^{-4} ≤ D' e^{2(log δ⁻¹)^{0.6}}` (DZZ l. 1320).
* **`l313GeomC_of_pos`**: `L313GeomC γ W α*` for `α* > 0` (the box sequence of `l313_assemble`; the cover
  condition from `s_B log s_B⁻¹ + 2 s_B ≤ ε* s_𝖢/10`, `l313_size_asym`, with `s_𝖢 ≥ δ^{C_mc}` from
  `cellSizeEvent ⊆ 𝓔_{δ,α*}`, DZZ l. 1334–1335).
* **`dzz_lemma313`**: DZZ Lemma 3.13 for every `α* > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox WhiteNoise

lemma l313_len_asym {αs : ℝ} (hαs : 0 < αs) : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    4 ≤ epsStarN αs δ ∧ (4 : ℝ) ^ (2 * epsStarN αs δ) ≤ Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ)) := by
  set L₀ : ℝ := max (max 9 (Real.exp αs⁻¹)) ((80 * αs + 3) ^ 20)
  refine ⟨Real.exp (-L₀), Real.exp_pos _, fun δ hδ => ?_⟩
  set L := Real.log δ⁻¹ with hLdef
  have hL : L₀ < L := by
    rw [hLdef, Real.log_inv, lt_neg]
    exact (Real.log_lt_iff_lt_exp hδ.1).2 hδ.2
  have hL9 : 9 ≤ L := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hL.le
  have hLe : Real.exp αs⁻¹ ≤ L := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hL.le
  have hLc : (80 * αs + 3) ^ 20 ≤ L := (le_max_right _ _).trans hL.le
  have hL0 : 0 < L := by linarith
  have hlogL : αs⁻¹ ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]; exact hLe
  have hαlog : 1 ≤ αs * Real.log L := by
    rw [← mul_inv_cancel₀ hαs.ne']; exact mul_le_mul_of_nonneg_left hlogL hαs.le
  set X := αs * Real.sqrt L * Real.log L with hX
  have hsq3 : 3 ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  have hXsq : Real.sqrt L ≤ X := by
    rw [hX, mul_right_comm]; nlinarith
  have hX0 : 0 ≤ X := by linarith
  have h16 : (16 : ℝ) ≤ Real.exp 3 := by
    have := Real.exp_one_gt_d9
    have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have p := pow_le_pow_left₀ (by norm_num) this.le 3
    rw [e]; norm_num at p; linarith
  set N := epsStarN αs δ
  have hεX : (2 : ℝ)⁻¹ ^ N ≤ Real.exp (-X) := epsStar_le_thr αs δ
  constructor
  · by_contra hN
    push_neg at hN
    have h1 : (2 : ℝ)⁻¹ ^ 3 ≤ (2 : ℝ)⁻¹ ^ N := ipow_le (by omega)
    have h2 : Real.exp (-X) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by linarith)
    have h3 : Real.exp (-3) * Real.exp 3 = 1 := by rw [← Real.exp_add]; norm_num
    have h4 : 0 < Real.exp (-3) := Real.exp_pos _
    nlinarith
  · have h4 := four_pow_epsStarN_le αs δ hX0
    -- `4 X + 3 ≤ L^{0.6}`
    have hlog : Real.log L ≤ L ^ (0.05 : ℝ) / 0.05 := Real.log_le_rpow_div hL0.le (by norm_num)
    have hsqrt : Real.sqrt L = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
    have e6 : L ^ (0.6 : ℝ) = L ^ (1 / 2 : ℝ) * L ^ (0.05 : ℝ) * L ^ (0.05 : ℝ) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
    have hc : 80 * αs + 3 ≤ L ^ (0.05 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) hLc (show (0 : ℝ) ≤ ((20 : ℕ) : ℝ)⁻¹ by positivity)
      rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at h
      convert h using 2; norm_num
    have hA1 : 1 ≤ L ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hB1 : 1 ≤ L ^ (0.05 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hXb : X ≤ αs * L ^ (1 / 2 : ℝ) * (20 * L ^ (0.05 : ℝ)) := by
      rw [hX, hsqrt]
      have e20 : L ^ (0.05 : ℝ) / 0.05 = 20 * L ^ (0.05 : ℝ) := by
        rw [div_eq_iff (by norm_num)]; ring_nf
      have : Real.log L ≤ 20 * L ^ (0.05 : ℝ) := e20 ▸ hlog
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hkey : 4 * X + 3 ≤ L ^ (0.6 : ℝ) := by
      rw [e6]
      have hAB : 1 ≤ L ^ (1 / 2 : ℝ) * L ^ (0.05 : ℝ) := by nlinarith
      have := mul_le_mul_of_nonneg_left hc (show 0 ≤ L ^ (1 / 2 : ℝ) * L ^ (0.05 : ℝ) by positivity)
      nlinarith
    have e42 : (4 : ℝ) ^ (2 * N) = ((4 : ℝ) ^ N) ^ 2 := by rw [pow_mul, ← pow_mul, mul_comm, pow_mul]
    rw [e42]
    calc ((4 : ℝ) ^ N) ^ 2 ≤ (4 * Real.exp (2 * X)) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
      _ = 16 * Real.exp (4 * X) := by rw [mul_pow, ← Real.exp_nat_mul]; norm_num; ring_nf
      _ ≤ Real.exp 3 * Real.exp (4 * X) := mul_le_mul_of_nonneg_right h16 (Real.exp_pos _).le
      _ = Real.exp (4 * X + 3) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (L ^ (0.6 : ℝ)) := Real.exp_le_exp.2 hkey

lemma l313Near_mono {r r' : ℝ} (h : r ≤ r') {b : DyBox} {z : ℂ} (hn : l313Near r b z) :
    l313Near r' b z := by
  obtain ⟨n1, n2, n3, n4⟩ := hn
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end DZZ
end LQGMetric
