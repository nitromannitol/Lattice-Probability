/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53NU1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Z4

/-!
# DZZ Lemma 5.3 part 1: the scale bookkeeping at the sheet's `ℓ = 4κ + ℓ₀` (P2-DZZ53NUM)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2427–2456, with the parameter choice of DEC-131-IF
S/F-3: `κ = ⌊L^{0.51}⌋₊`, `ℓ = 4κ + ℓ₀` with `2^{ℓ₀} ≤ C' L` (so that `2^ℓ ≥ K⁴`), proxy level
`m_b = n_b + κ + ℓ`, `j = 2 n_{ε*} + κ + ℓ`.

* `l53_two_pow_j_le_nu`: `2^{2 n_{ε*} + κ + (4κ + ℓ₀)} ≤ e^{L^{0.55}}` for large `L` (adapted from
  `l53_two_pow_j_le`, S5L53Z4, which covers only `2^ℓ ≤ C' L`; same proof with `K⁵` in place of `K`).
* `l53_domination_chainBox_nu`: Z4's `l53_domination_chainBox` at the level `n_b + κ + (4κ + ℓ₀)`
  (same proof, with `l53_two_pow_j_le_nu`).
* `l53_chainBox_n_le`: chain boxes `b` (`n_b = n_𝖢 + 2 n_{ε*}`, `s_𝖢 ≥ δ^{C}`) have
  `n_b ≤ (C + 1) k` for large `k` (`δ = 2^{-k}`). Own elementary proof (from `l53_two_pow_j_le`).
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

/-- `log (2^{-k})⁻¹ = k log 2` -/
lemma l53nu_log_delta (k : ℕ) : Real.log (((2 : ℝ)⁻¹ ^ k)⁻¹) = (k : ℝ) * Real.log 2 := by
  rw [inv_pow, inv_inv, Real.log_pow]

/-- `2^{⌊x⌋₊} ≤ e^x` for `x ≥ 0` -/
lemma l53nu_two_pow_floor_le {x : ℝ} (hx : 0 ≤ x) : (2 : ℝ) ^ ⌊x⌋₊ ≤ Real.exp x := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  refine Real.exp_le_exp.2 ?_
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have := Nat.floor_le hx
  nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

/-- `C' L ≤ e^{L^{0.51}}` eventually (from `C' L ≤ (L^{0.51})²/2`) -/
lemma l53nu_ev_mul_le_exp (C' : ℝ) :
    ∀ᶠ L : ℝ in atTop, C' * L ≤ Real.exp (L ^ (0.51 : ℝ)) := by
  filter_upwards [l53z_ev_mul_rpow_le (2 * |C'|) (by norm_num : (1 : ℝ) < 1.02),
    eventually_gt_atTop 0] with L hL hL0
  have hl51 : 0 ≤ L ^ (0.51 : ℝ) := Real.rpow_nonneg hL0.le _
  have e51 : (L ^ (0.51 : ℝ)) ^ 2 = L ^ (1.02 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hq := Real.quadratic_le_exp_of_nonneg hl51
  rw [Real.rpow_one] at hL
  have h1 : C' * L ≤ |C'| * L := mul_le_mul_of_nonneg_right (le_abs_self _) hL0.le
  nlinarith [abs_nonneg C']

/-- **level of the chain boxes**: for `δ = 2^{-k}` and `k` large, a box `b` with
`n_b = n_𝖢 + 2 n_{ε*}` and `s_𝖢 ≥ δ^{C}` has `n_b ≤ (C + 1) k`. Own elementary proof. -/
theorem l53_chainBox_n_le (αs Cm : ℝ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ B b : DyBox, ((2 : ℝ)⁻¹ ^ k) ^ Cm ≤ B.side →
      b.n = B.n + 2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) → (b.n : ℝ) ≤ (Cm + 1) * k := by
  obtain ⟨L₀, hL₀⟩ := l53_two_pow_j_le αs 1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨⌈max L₀ 1 / Real.log 2⌉₊, fun k hk B b hB hb => ?_⟩
  have hkL : max L₀ 1 ≤ (k : ℝ) * Real.log 2 := by
    rw [← div_le_iff₀ hl2]; exact (Nat.le_ceil _).trans (by exact_mod_cast hk)
  -- `n_𝖢 ≤ C k`
  have hBn : (B.n : ℝ) ≤ Cm * k := by
    have e1 : ((2 : ℝ)⁻¹ ^ k) ^ Cm = (2 : ℝ)⁻¹ ^ ((k : ℝ) * Cm) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e2 : B.side = (2 : ℝ)⁻¹ ^ (B.n : ℝ) := by
      unfold DyBox.side; rw [Real.rpow_natCast]
    rw [e1, e2, Real.rpow_le_rpow_left_iff_of_base_lt_one (by norm_num) (by norm_num)] at hB
    linarith
  -- `2 n_{ε*} ≤ k`
  have hN : ((2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) : ℕ) : ℝ) ≤ k := by
    have hLd := l53nu_log_delta k
    have hj := hL₀ ((2 : ℝ)⁻¹ ^ k) (by rw [hLd]; exact (le_max_left _ _).trans hkL) 0
      (by rw [pow_zero, hLd, one_mul]; exact (le_max_right _ _).trans hkL)
    rw [hLd, add_zero] at hj
    have hL1 : 1 ≤ (k : ℝ) * Real.log 2 := (le_max_right _ _).trans hkL
    have h55 : ((k : ℝ) * Real.log 2) ^ (0.55 : ℝ) ≤ (k : ℝ) * Real.log 2 := by
      calc ((k : ℝ) * Real.log 2) ^ (0.55 : ℝ) ≤ ((k : ℝ) * Real.log 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = _ := Real.rpow_one _
    have h2 : (2 : ℝ) ^ (2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k)) ≤ Real.exp ((k : ℝ) * Real.log 2) :=
      (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)).trans
        (hj.trans (Real.exp_le_exp.2 h55))
    have e : (2 : ℝ) ^ (2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k)) =
        Real.exp (((2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [e, Real.exp_le_exp] at h2
    exact le_of_mul_le_mul_right h2 hl2
  rw [hb]; push_cast at hN ⊢; linarith

end DZZ
end LQGMetric
