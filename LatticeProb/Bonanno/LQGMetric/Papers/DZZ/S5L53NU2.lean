/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53NU2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53NU1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Geom

/-!
# DZZ Lemma 5.3 part 1: the side conditions of `l53_bad_cond_proxy` at DZZ's scales (P2-DZZ53NUM)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2427–2502, with the parameters of DEC-131-IF
(G-M, S/F-3): `L = k log 2`, `κ = ⌊L^{0.51}⌋₊`, `K = 2^κ`, chain box `b` (side `s = s_b`), sub-box
`𝖡` of `b` at level `n_b + κ` (side `t = s/K`), proxy level `m = n_b + κ + (4κ + ℓ₀)` with
`2^{ℓ₀} ≤ C' L`, near-pair cut-off `r ∈ [t K⁻⁴, t/(16K)]` (DV-D131-3).

**`l53_scales_ok`**: for large `k`, all real-number hypotheses of `l53_bad_cond_proxy` (S5L53Y4)
hold: `0 < r`, `2^{-m} ≤ s`, the locality range `(2^{-m} log 2^m + 2^{-m})/2 < t`,
`16 r ≤ K⁻¹ t`, and for every pair `z, z' ∈ ∂𝖡` with `|z − z'| ≥ r`, `α = |z'−z|/|v−u|`:
`α ≤ 1`, `α ≤ s`, `2^{-m} ≤ α` (the coupling range `ρ = α 2^m ≥ 1` of X4),
`α 2^m ≤ e^{L^{0.52}}`, and `𝕍̃_{z,z'} ⊆ 𝕍_ξ'` given `𝕍_{c_𝖡,5t} ⊆ 𝕍_ξ'` (the G-G1 geometry is
a hypothesis). Own elementary estimates (DZZ states these scale relations without proof).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- `|v − u| ≤ 1` on `𝕍̄` -/
lemma l53nu_norm_sub_le_one {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) : ‖v - u‖ ≤ 1 := by
  have h1 := sqBox_subset_closedBall _ (by norm_num : (0 : ℝ) ≤ 1 / 20) hu
  have h2 := sqBox_subset_closedBall _ (by norm_num : (0 : ℝ) ≤ 1 / 20) hv
  rw [mem_closedBall] at h1 h2
  rw [← dist_eq_norm]
  linarith [dist_triangle_right v u (⟨1 / 2, 1 / 2⟩ : ℂ)]

set_option maxHeartbeats 800000 in
/-- **the scale side conditions of P-131F** (`hpair` and the locality / cut-off hypotheses of
`l53_bad_cond_proxy`, S5L53Y4) at DZZ's scales, for all large `k`. -/
theorem l53_scales_ok {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v)
    (A₁ C' : ℝ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ κ : ℕ, κ = ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ →
      ∀ ℓ₀ : ℕ, (2 : ℝ) ^ ℓ₀ ≤ C' * ((k : ℝ) * Real.log 2) →
      ∀ b B : DyBox, (b.n : ℝ) ≤ A₁ * k → B.n = b.n + κ →
      ∀ m : ℕ, m = b.n + κ + (4 * κ + ℓ₀) →
      B.side * ((2 : ℝ) ^ κ)⁻¹ ^ 4 ≤ B.side / (16 * 2 ^ κ) ∧ ∀ r : ℝ, B.side * ((2 : ℝ) ^ κ)⁻¹ ^ 4 ≤ r → r ≤ B.side / (16 * 2 ^ κ) →
      0 < r ∧ (2 : ℝ)⁻¹ ^ m ≤ b.side ∧
      ((2 : ℝ)⁻¹ ^ m * Real.log ((2 : ℝ)⁻¹ ^ m)⁻¹ + (2 : ℝ)⁻¹ ^ m) / 2 < B.side ∧
      16 * ENNReal.ofReal r ≤ (ENNReal.ofReal ((2 : ℝ) ^ κ))⁻¹ * ENNReal.ofReal B.side ∧
      ∀ ξ' : ℝ, sqBox B.center (5 * B.side) ⊆ dzzVXi ξ' →
      ∀ z ∈ frontier B.closedBox, ∀ z' ∈ frontier B.closedBox, r ≤ dist z z' →
        ‖z' - z‖ / ‖v - u‖ ≤ 1 ∧ ‖z' - z‖ / ‖v - u‖ ≤ b.side ∧
        (2 : ℝ)⁻¹ ^ m ≤ ‖z' - z‖ / ‖v - u‖ ∧
        ‖z' - z‖ / ‖v - u‖ * (2 : ℝ) ^ m ≤ Real.exp (((k : ℝ) * Real.log 2) ^ (0.52 : ℝ)) ∧
        tildeBox z z' ⊆ dzzVXi ξ' := by
  have hd0 : 0 < ‖v - u‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm huv))
  have hd1 := l53nu_norm_sub_le_one hu hv
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2h : 1 / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl21 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 ((eventually_ge_atTop (1 : ℝ)).and
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.51)).eventually
      (eventually_ge_atTop (max 3 (2 / ‖v - u‖)))).and ((l53nu_ev_mul_le_exp C').and
      ((l53z_ev_mul_rpow_le 6 (by norm_num : (0.51 : ℝ) < 0.52)).and
        (l53z_ev_mul_rpow_le (2 * |A₁| + 8) (by norm_num : (1 : ℝ) < 2.04))))))
  refine ⟨⌈L₀ / Real.log 2⌉₊, fun k hk κ hκ ℓ₀ hℓ₀ b B hbn hBn m hm => ?_⟩
  set L := (k : ℝ) * Real.log 2 with hLdef
  have hL : L₀ ≤ L := by
    rw [hLdef, ← div_le_iff₀ hl2]; exact (Nat.le_ceil _).trans (by exact_mod_cast hk)
  obtain ⟨hL1, hl51b, hCL, h652, hA⟩ := hL₀ L hL
  rw [Real.rpow_one] at hA
  have hL0 : 0 < L := by linarith
  set l51 := L ^ (0.51 : ℝ) with hl51def
  have hl51 : 0 ≤ l51 := Real.rpow_nonneg hL0.le _
  have hl51L : l51 ≤ L := by
    calc l51 ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := Real.rpow_one L
  have hl51_3 : 3 ≤ l51 := (le_max_left _ _).trans hl51b
  have hl51_d : 2 / ‖v - u‖ ≤ l51 := (le_max_right _ _).trans hl51b
  -- `K = 2^κ`
  set K : ℝ := (2 : ℝ) ^ κ with hKdef
  have hκl : (κ : ℝ) ≤ l51 := by rw [hκ]; exact Nat.floor_le hl51
  have hκ1 : l51 < κ + 1 := by rw [hκ]; exact Nat.lt_floor_add_one _
  have hK1 : (κ : ℝ) + 1 ≤ K := by
    have := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1) κ
    rw [hKdef]; norm_num at this; linarith
  have hKl : l51 ≤ K := by linarith
  have hK0 : 0 < K := by positivity
  have hKe : K ≤ Real.exp l51 := by rw [hKdef, hκ]; exact l53nu_two_pow_floor_le hl51
  have hK4 : L ^ (2.04 : ℝ) ≤ K ^ 4 := by
    have e : L ^ (2.04 : ℝ) = l51 ^ 4 := by
      rw [hl51def, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    rw [e]; exact pow_le_pow_left₀ hl51 hKl 4
  -- `P = 2^{ℓ₀}`
  set Pw : ℝ := (2 : ℝ) ^ ℓ₀ with hPdef
  have hP1 : 1 ≤ Pw := one_le_pow₀ (by norm_num)
  have hPe : Pw ≤ Real.exp l51 := hℓ₀.trans hCL
  have hℓ₀l : (ℓ₀ : ℝ) ≤ 2 * l51 := by
    have e : Pw = Real.exp ((ℓ₀ : ℝ) * Real.log 2) := by
      rw [hPdef, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [e, Real.exp_le_exp] at hPe
    nlinarith [(Nat.cast_nonneg ℓ₀ : (0 : ℝ) ≤ ℓ₀)]
  -- sides
  set s := b.side with hsdef
  set t := B.side with htdef
  have hs0 : 0 < s := DyBox.side_pos' b
  have ht0 : 0 < t := DyBox.side_pos' B
  have hs1 : s ≤ 1 := by rw [hsdef]; unfold DyBox.side; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hts : t * K = s := by
    rw [htdef, hsdef, hKdef]; unfold DyBox.side
    rw [hBn, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow,
      mul_one]
  have hK16 : 16 * K ≤ K ^ 4 := by
    have h3 : (3 : ℝ) ≤ K := hl51_3.trans hKl
    nlinarith [mul_le_mul h3 h3 (by norm_num) hK0.le]
  refine ⟨?_, fun r hr1 hr2 => ?_⟩
  · rw [inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left ht0.le (by positivity) hK16
  set e := (2 : ℝ)⁻¹ ^ m with hedef
  have he0 : 0 < e := by positivity
  have hem : e * (K ^ 4 * Pw) = t := by
    have hmB : m = B.n + (4 * κ + ℓ₀) := by omega
    have h4 : K ^ 4 * Pw = (2 : ℝ) ^ (4 * κ + ℓ₀) := by rw [pow_add, pow_mul']
    rw [hedef, h4, hmB, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
      one_pow, mul_one, htdef]; rfl
  have hKP : 1 ≤ K ^ 4 * Pw := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hP1
  have het : e ≤ t := by rw [← hem]; exact le_mul_of_one_le_right he0.le hKP
  have hts' : t ≤ s := by rw [← hts]; exact le_mul_of_one_le_right ht0.le (by linarith)
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have her : e ≤ r := by
    refine le_trans ?_ hr1
    rw [← hem, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have : e * K ^ 4 ≤ e * (K ^ 4 * Pw) := by
      rw [← mul_assoc]; exact le_mul_of_one_le_right (by positivity) hP1
    linarith
  -- `m ≤ (2|A₁| + 7) L`
  have hk2 : (k : ℝ) ≤ 2 * L := by
    rw [hLdef]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hmL : (m : ℝ) + 1 ≤ (2 * |A₁| + 8) * L := by
    have hm' : (m : ℝ) = b.n + κ + (4 * κ + ℓ₀) := by rw [hm]; push_cast; ring
    have hb : (b.n : ℝ) ≤ |A₁| * (2 * L) :=
      hbn.trans (mul_le_mul (le_abs_self _) hk2 (Nat.cast_nonneg _) (abs_nonneg _))
    rw [hm']; nlinarith
  refine ⟨hr0, het.trans hts', ?_, ?_, ?_⟩
  · -- the locality range
    have hlog : Real.log e⁻¹ = (m : ℝ) * Real.log 2 := by
      rw [hedef, inv_pow, inv_inv, Real.log_pow]
    rw [hlog]
    have h1 : (m : ℝ) * Real.log 2 + 1 < 2 * (K ^ 4 * Pw) := by
      have : (m : ℝ) * Real.log 2 ≤ m := by
        nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      nlinarith
    calc (e * ((m : ℝ) * Real.log 2) + e) / 2 = e * ((m : ℝ) * Real.log 2 + 1) / 2 := by ring
      _ < e * (2 * (K ^ 4 * Pw)) / 2 := by gcongr
      _ = t := by rw [← hem]; ring
  · -- `16 r ≤ K⁻¹ t`
    have h16 : 16 * r ≤ K⁻¹ * t := by
      rw [le_div_iff₀ (by positivity)] at hr2
      rw [inv_mul_eq_div, le_div_iff₀ hK0]; linarith
    calc 16 * ENNReal.ofReal r = ENNReal.ofReal (16 * r) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ ≤ ENNReal.ofReal (K⁻¹ * t) := ENNReal.ofReal_le_ofReal h16
      _ = _ := by rw [ENNReal.ofReal_mul (inv_nonneg.2 hK0.le), ENNReal.ofReal_inv_of_pos hK0]
  · intro ξ' hS z hz z' hz' hzz
    have hB := closedBox_eq_sqBox B
    rw [hB] at hz hz'
    have hzB := (isClosed_sqBox _ _).frontier_subset hz
    have hzB' := (isClosed_sqBox _ _).frontier_subset hz'
    have hD2 : ‖z' - z‖ ≤ 2 * t := by
      have h1 := sqBox_subset_closedBall _ ht0.le hzB
      have h2 := sqBox_subset_closedBall _ ht0.le hzB'
      rw [mem_closedBall] at h1 h2
      rw [← dist_eq_norm]
      linarith [dist_triangle_right z' z B.center]
    have hDr : r ≤ ‖z' - z‖ := by rwa [dist_eq_norm, norm_sub_rev] at hzz
    set D := ‖z' - z‖
    set d := ‖v - u‖
    have hKd : 2 ≤ K * d := by
      have := (div_le_iff₀ hd0).1 (hl51_d.trans hKl); linarith
    have hαs : D / d ≤ s := by
      rw [div_le_iff₀ hd0, ← hts]; nlinarith
    have hne : z ≠ z' := by
      rintro rfl; rw [dist_self] at hzz; linarith
    refine ⟨hαs.trans hs1, hαs, ?_, ?_, (tildeBox_subset_sqBox_five hzB hzB' hne).trans hS⟩
    · exact (her.trans hDr).trans (le_div_self (by linarith) hd0 hd1)
    · -- `α 2^m ≤ 2 K⁴ P / d ≤ e^{6 L^{0.51}} ≤ e^{L^{0.52}}`
      have h2m : (2 : ℝ) ^ m = e⁻¹ := by rw [hedef, inv_pow, inv_inv]
      have hde : 2 / d ≤ Real.exp l51 := hl51_d.trans (by linarith [Real.add_one_le_exp l51])
      have hK4e : K ^ 4 ≤ Real.exp (4 * l51) := by
        rw [show 4 * l51 = ((4 : ℕ) : ℝ) * l51 by norm_num, Real.exp_nat_mul]
        exact pow_le_pow_left₀ hK0.le hKe 4
      calc D / d * (2 : ℝ) ^ m ≤ 2 * t / d * e⁻¹ := by
            rw [h2m]; gcongr
        _ = 2 / d * (K ^ 4 * Pw) := by
            rw [← hem]; field_simp
        _ ≤ Real.exp l51 * (Real.exp (4 * l51) * Real.exp l51) := by gcongr
        _ = Real.exp (6 * l51) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp (L ^ (0.52 : ℝ)) := Real.exp_le_exp.2 h652

end DZZ
end LQGMetric
