/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53N3F1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53O1A
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53GB5

/-!
# DZZ Lemma 5.3, node 3: elementary inputs of the per-cell assembly (P2-DZZ53N3F)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2425–2514. Small facts used by `l53n3_cell_core`
(S5L53N3F2) when it applies `l53_box_desirable_prob_proxy` (S5L53GB5) to a chain cell:
* `l53n3_side_eq`: `s_𝖢 = 2^κ t`, `t = 2^{-(n_𝖢+κ)}`;
* `l53n3_sqBox_five_mono`: `𝕍_{c_𝖡, 5 s_𝖡} ⊆ 𝕍_{c_𝖢, 5 s_𝖢}` for a sub-box `𝖡 ⊆ 𝖢`;
* `l53n3_eps`: the per-site bound `ε = 2 (2 K_L⁻⁴) Kt²` of `l53_bad_cond_proxy'` with
  `K_L = 2N + 2`, `Kt = N + 1` satisfies `ε ≤ (1/16)^{64}` and `(2N+1)(N+1) ε ≤ 1/2`
  (the hypotheses `hεθ` of GB5 and `hε` of `l53_box_rhs_le`).
Own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

lemma l53n3_side_eq (C : DyBox) (κ : ℕ) : C.side = 2 ^ κ * (2 : ℝ)⁻¹ ^ (C.n + κ) := by
  unfold DyBox.side
  rw [pow_add, mul_comm, mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
    one_pow, mul_one]

/-- `𝕍_{c_𝖡, 5 s_𝖡} ⊆ 𝕍_{c_𝖢, 5 s_𝖢}` for `𝖡̄ ⊆ 𝖢̄`, `2 s_𝖡 ≤ s_𝖢`. -/
lemma l53n3_sqBox_five_mono {B C : DyBox} (hBC : B.closedBox ⊆ C.closedBox)
    (hs : 2 * B.side ≤ C.side) : sqBox B.center (5 * B.side) ⊆ sqBox C.center (5 * C.side) := by
  have hc : B.center ∈ C.closedBox := hBC (by
    rw [closedBox_eq_sqBox]
    exact ⟨by simp; linarith [side_pos' B], by simp; linarith [side_pos' B]⟩)
  rw [closedBox_eq_sqBox] at hc
  obtain ⟨c1, c2⟩ := hc
  rintro z ⟨z1, z2⟩
  have hB := side_pos' B
  constructor
  · calc |z.re - C.center.re| ≤ |z.re - B.center.re| + |B.center.re - C.center.re| :=
          abs_sub_le _ _ _
      _ ≤ 5 * C.side / 2 := by linarith
  · calc |z.im - C.center.im| ≤ |z.im - B.center.im| + |B.center.im - C.center.im| :=
          abs_sub_le _ _ _
      _ ≤ 5 * C.side / 2 := by linarith

/-- **The per-site bound at `K_L = 2N + 2`, `Kt = N + 1`.** -/
lemma l53n3_eps {N κ : ℕ} (hK : 2 ^ κ = 2 * N + 2) (hN : (2 : ℝ) ^ 127 ≤ N + 1) :
    2 * ENNReal.ofReal (2 * ((2 : ℝ) ^ κ)⁻¹ ^ 4) * ((N + 1 : ℕ) : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (1 / 16) ^ ((7 + 1) ^ 2) ∧
      ((2 * N + 1 : ℕ) : ℝ≥0∞) * (((N + 1 : ℕ) : ℝ≥0∞) *
        (2 * ENNReal.ofReal (2 * ((2 : ℝ) ^ κ)⁻¹ ^ 4) * ((N + 1 : ℕ) : ℝ≥0∞) ^ 2)) ≤ 2⁻¹ := by
  have hKR : (2 : ℝ) ^ κ = 2 * N + 2 := by exact_mod_cast hK
  have hN0 : (0 : ℝ) < N + 1 := by positivity
  have e : 2 * ENNReal.ofReal (2 * ((2 : ℝ) ^ κ)⁻¹ ^ 4) * ((N + 1 : ℕ) : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal (1 / (4 * ((N : ℝ) + 1) ^ 2)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hKR]; push_cast
    field_simp
    ring
  rw [e]
  constructor
  · rw [← ENNReal.ofReal_pow (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [one_div_pow]
    apply one_div_le_one_div_of_le (by positivity)
    have h2 : ((2 : ℝ) ^ 127) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hN 2
    have : (16 : ℝ) ^ ((7 + 1) ^ 2) = 4 * ((2 : ℝ) ^ 127) ^ 2 := by norm_num
    rw [this]; linarith
  · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ by
        rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    rw [show ((2 : ℝ) * N + 1) * ((N + 1) * (1 / (4 * (N + 1) ^ 2))) =
      (2 * N + 1) / (4 * (N + 1)) by field_simp]
    rw [div_le_iff₀ (by positivity)]
    nlinarith

lemma l53n3_theta : (8 : ℝ≥0∞) * ENNReal.ofReal (1 / 16) ≤ 2⁻¹ := by
  rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp, ← ENNReal.ofReal_mul (by norm_num),
    show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ by rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end DZZ
end LQGMetric
