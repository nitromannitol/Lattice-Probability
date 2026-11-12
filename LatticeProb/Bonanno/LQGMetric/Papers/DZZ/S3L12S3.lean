/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12S3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12S2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinAsym

/-!
# DZZ Lemma 3.12: the path surgery reduced to DZZ's one-step claim (P2-DZZ316)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1436–1499.

* **`L312Step`** (open): DZZ's claim (l. 1447–1453; proof l. 1462–1499, Cases 1–3): a
  `Neighbour`-chain of cells joining the good points `u`, `v` with a bad cell can be modified,
  adding at most `32 (ε*)^{-2}` cells, so that (i) or (ii) holds (loop-free sequences).
* `four_pow_epsStarN_le`, `l312_count_asym`: `1 + 32 (ε*)^{-2} (2 C_mc log₂ δ⁻¹ + 1) ≤ e^{(log δ⁻¹)^{0.6}}`
  (DZZ l. 1458: `d_0 (ε*)^{-2} C_mc log₂ δ⁻¹ ≤ d_0 e^{(log δ⁻¹)^{0.6}}`).
* **`l312SurgeryC_of_step`**: `L312Step γ → L312SurgeryC γ` (`𝒞_0` = `exists_geodesic_chain`,
  iteration `l312_iterate`, good sequence `isGoodSeq_of_bad_empty`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

/-- `(ε*)^{-2} ≤ 4 e^{2 α* √(log δ⁻¹) log log δ⁻¹}` (minimality of `ε*`). -/
lemma four_pow_epsStarN_le (αs δ : ℝ)
    (hX : 0 ≤ αs * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)) :
    (4 : ℝ) ^ epsStarN αs δ ≤
      4 * Real.exp (2 * (αs * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹))) := by
  classical
  set X := αs * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)
  set N := epsStarN αs δ with hN
  have e4 : (4 : ℝ) ^ N = ((2 : ℝ) ^ N) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · rw [h0, pow_zero]
    have := Real.one_le_exp (show 0 ≤ 2 * X by linarith)
    linarith
  · have hmin := Nat.find_min (exists_two_pow_le_epsStarThr αs δ) (show N - 1 < N by omega)
    have hlt : epsStarThr αs δ < (2 : ℝ)⁻¹ ^ (N - 1) := lt_of_not_ge hmin
    rw [epsStarThr, inv_two_pow_eq_exp, Real.exp_lt_exp] at hlt
    have hc : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hc] at hlt
    have h2 : (2 : ℝ) ^ N ≤ 2 * Real.exp X := by
      rw [two_pow_eq_exp, show (2 : ℝ) = Real.exp (Real.log 2) from
        (Real.exp_log (by norm_num)).symm, ← Real.exp_add, Real.exp_le_exp, Real.log_exp]
      linarith
    rw [e4]
    calc ((2 : ℝ) ^ N) ^ 2 ≤ (2 * Real.exp X) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      _ = 4 * Real.exp (2 * X) := by rw [mul_pow, exp_sq_eq]; norm_num

/-- The counting asymptotics of DZZ l. 1458. -/
lemma l312_count_asym {C αs : ℝ} (hC : 0 < C) (hαs : 0 < αs) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      1 + ((32 * 4 ^ epsStarN αs δ : ℕ) : ℝ) * (2 * ⌊C * Real.logb 2 δ⁻¹⌋₊ + 1) ≤
        Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ)) := by
  have e1 := ev_pow_le (show (0 : ℝ) < 1 / 16 by norm_num) (512 * C) (show 20 < 24 by norm_num)
  have e2 := ev_pow_le (show (0 : ℝ) < 1 / 16 by norm_num) 129 (show 0 < 24 by norm_num)
  obtain ⟨U, hU⟩ := eventually_atTop.1 (e1.and e2)
  set U' := max (max U 1) (80 * αs) with hU'
  refine ⟨Real.exp (-(U' ^ 20)), Real.exp_pos _, Real.exp_lt_one_iff.2 (by
    have : 0 < U' := lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _))
    simp only [neg_lt_zero]; positivity), ?_⟩
  rintro δ ⟨hδ0, hδ1⟩
  set L := Real.log δ⁻¹ with hLdef
  have hU1 : 1 ≤ U' := (le_max_right _ _).trans (le_max_left _ _)
  have hL : U' ^ 20 < L := by
    have := Real.log_lt_log hδ0 hδ1
    rw [Real.log_exp] at this
    have h2 : L = -Real.log δ := by rw [hLdef, Real.log_inv]
    linarith
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
  set u := L ^ ((1 : ℝ) / 20) with hudef
  have hu20 : u ^ 20 = L := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hu12 : L ^ (0.6 : ℝ) = u ^ 12 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have huU : U' ≤ u := by
    have h1 : (U' ^ 20) ^ ((1 : ℝ) / 20) = U' := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rw [← h1]; exact Real.rpow_le_rpow (by positivity) hL.le (by norm_num)
  have hu1 : 1 ≤ u := hU1.trans huU
  have hu80 : 80 * αs ≤ u := (le_max_right _ _).trans huU
  obtain ⟨E1, E2⟩ := hU u ((le_max_left _ _).trans ((le_max_left _ _).trans huU))
  simp only [pow_zero, mul_one] at E2
  have hsqrt : Real.sqrt L = u ^ 10 := by
    rw [← hu20, show u ^ 20 = (u ^ 10) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have hlogL : Real.log L ≤ 20 * u := by
    have := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 20 by norm_num)
    rw [← hudef] at this
    calc Real.log L ≤ u / (1 / 20) := this
      _ = 20 * u := by ring
  have hL1 : 1 ≤ L := by rw [← hu20]; exact one_le_pow₀ hu1
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  set X := αs * Real.sqrt L * Real.log L with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hX : 2 * X ≤ 40 * αs * u ^ 11 := by
    have := mul_le_mul_of_nonneg_left hlogL (show 0 ≤ αs * u ^ 10 by positivity)
    rw [hXdef, hsqrt]; nlinarith
  have hK := four_pow_epsStarN_le αs δ hX0
  rw [← hLdef] at hK
  -- `M ≤ 2 C L`
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hM : (⌊C * Real.logb 2 δ⁻¹⌋₊ : ℝ) ≤ 2 * C * L := by
    refine (Nat.floor_le (by
      rw [Real.logb]; exact mul_nonneg hC.le (div_nonneg hL0.le (by linarith)))).trans ?_
    rw [Real.logb, ← hLdef, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    have := mul_lt_mul_of_pos_left hlog2 (mul_pos (mul_pos two_pos hC) hL0)
    linarith
  have hKc : ((32 * 4 ^ epsStarN αs δ : ℕ) : ℝ) ≤ 128 * Real.exp (2 * X) := by
    push_cast; linarith
  -- `e^{y} ≥ y²/2` with `y = u^{12} − 40 α* u^{11} ≥ u^{12}/2`
  set y := u ^ 12 - 40 * αs * u ^ 11 with hy
  have hy2 : u ^ 12 / 2 ≤ y := by
    have : 80 * αs * u ^ 11 ≤ u ^ 12 := by
      have := mul_le_mul_of_nonneg_right hu80 (show 0 ≤ u ^ 11 by positivity)
      calc 80 * αs * u ^ 11 ≤ u * u ^ 11 := this
        _ = u ^ 12 := by ring
    rw [hy]; linarith
  have hey : u ^ 24 / 8 ≤ Real.exp y := by
    have := Real.pow_div_factorial_le_exp y (by nlinarith [pow_pos (by linarith : (0 : ℝ) < u) 12]) 2
    have hsq : (u ^ 12 / 2) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by positivity) hy2 2
    calc u ^ 24 / 8 = (u ^ 12 / 2) ^ 2 / 2 := by ring
      _ ≤ y ^ 2 / 2 := by linarith
      _ = y ^ 2 / (Nat.factorial 2) := by norm_num [Nat.factorial]
      _ ≤ Real.exp y := this
  rw [hu12]
  have hexp : Real.exp (u ^ 12) = Real.exp (40 * αs * u ^ 11) * Real.exp y := by
    rw [← Real.exp_add]; congr 1; ring
  have hE1 : 1 ≤ Real.exp (2 * X) := Real.one_le_exp (by linarith)
  have hE2 : Real.exp (2 * X) ≤ Real.exp (40 * αs * u ^ 11) := Real.exp_le_exp.2 hX
  have hpoly : 1 + 128 * (4 * C * u ^ 20 + 1) ≤ Real.exp y := by linarith
  have hMu : 2 * (⌊C * Real.logb 2 δ⁻¹⌋₊ : ℝ) + 1 ≤ 4 * C * u ^ 20 + 1 := by
    rw [hu20]; linarith
  calc 1 + ((32 * 4 ^ epsStarN αs δ : ℕ) : ℝ) * (2 * ⌊C * Real.logb 2 δ⁻¹⌋₊ + 1)
      ≤ Real.exp (2 * X) + 128 * Real.exp (2 * X) * (4 * C * u ^ 20 + 1) := by
        have := mul_le_mul hKc hMu (by positivity) (by positivity)
        linarith
    _ = Real.exp (2 * X) * (1 + 128 * (4 * C * u ^ 20 + 1)) := by ring
    _ ≤ Real.exp (40 * αs * u ^ 11) * Real.exp y :=
        mul_le_mul hE2 hpoly (by positivity) (Real.exp_pos _).le
    _ = Real.exp (u ^ 12) := hexp.symm

end DZZ
end LQGMetric
