/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53G5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B11
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Side
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B1

/-!
# DZZ Lemma 5.3, part 1, node 2: the tail at `(u, v)` of the per-pair far bound (P2-DZZ53G)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2490–2493: after the scaling step
`D̃_{δδ̃}(z,z') ≤ D̃_{δ̃ e^{−(log δ⁻¹)^{0.95}}}(u,v)`, "we combine the preceding inequality with
Corollary 3.9 and Proposition 3.17, and deduce that
`P(log D̃_{δδ̃}(z,z') ≥ E log D̃_{δ̃}(u,v) + (log δ⁻¹)^{0.97} | 𝓕*) ≤ O(K⁻⁴)`."

* **`l53_uv_tail`**: the Proposition 3.17 part, at the wall `𝕍̃_{u,v}` (which is in `dgWalls`,
  `tildeBox_mem_dgWalls`): for small `δ'` and every threshold
  `T ≥ E log D̃_{δ'}(u,v) + (log δ'⁻¹)^{0.95}`,
  `P(log D̃_{δ'}(u,v) > T) ≤ e^{−(log δ'⁻¹)^{0.7}}` (eq-concentration-2 of the walled P3.17,
  `DZZProp317Walls … dgWalls`, the hypothesis of the task).
* **`l53_K4_of_rpow`**: `e^{−x^{0.7}} ≤ K⁻⁴` with `K = 2^{⌊L^{0.51}⌋}` once `x ≥ L^{0.95}` and `L`
  is large: the concentration must be applied at `δ' = δ̃ e^{−(log δ⁻¹)^{0.95}}`, whose
  `log δ'⁻¹ ≥ L^{0.95}`, not at `δ̃` (see "Source errors": at `δ̃` itself, when `δ̃ = 2^{−l}` with
  `l` small, neither Cor 3.9 (probability `1 − δ̃^c`) nor P3.17 (`1 − e^{−(log δ̃⁻¹)^{0.7}}`) is
  `O(K⁻⁴)`). The remaining comparison `E log D̃_{δ'}(u,v) + (log δ'⁻¹)^{0.95} ≤
  E log D̃_{δ̃}(u,v) + (log δ⁻¹)^{0.97}` is the expectation form of Cor 3.9.
* **`l53_uv_far_small`**: the whole `(u,v)`-step at `μIn` in the regime `l log 2 ≤ L^{0.96}`
  (`δ̃ = 2^{−l}`, `L = log δ⁻¹`), where the expectation comparison follows from the crude bound
  `E log D̃_{δ'}(u,v) ≤ A + B log δ'⁻¹` (`lintegral_log_tilde_le`, S5L53CrudeP):
  `P(log D̃_{2^{−l}e^{−L^{0.95}}}(u,v) > E log D̃_{2^{−l}}(u,v) + L^{0.97}) ≤ K⁻⁴`. Own elementary
  argument (DZZ only cite Cor 3.9 and P3.17). The regime `l log 2 > L^{0.96}` needs the
  expectation form of Cor 3.9 (open, see the handoff).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The tail at `(u,v)`** from the walled P3.17 (eq-concentration-2) at `𝕍̃_{u,v}`. -/
theorem l53_uv_tail {μ : Ω → Measure ℂ} {ξ : ℝ} (h317 : DZZProp317Walls P μ ξ dgWalls)
    (hξ : 0 < ξ) (hξ4 : ξ ≤ 1 / 4) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v)
    (h2ξ : 2 * ξ ≤ dist u v) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ' ∈ Ioo (0 : ℝ) δ₀, ∀ T : ℝ,
      (∫ ω', logMinLGD (dzzWall (tildeBox u v) (μ ω')) δ' {u} {v} ∂P) +
        Real.log δ'⁻¹ ^ (0.95 : ℝ) ≤ T →
      P {ω | T < logMinLGD (dzzWall (tildeBox u v) (μ ω)) δ' {u} {v}} ≤
        ENNReal.ofReal (Real.exp (-(Real.log δ'⁻¹ ^ (0.7 : ℝ)))) := by
  have hin := dzzProp317In_tildeBox_of_walls h317 hu hv huv
  have hVu : u ∈ dzzVXi ξ := by
    have h := tildeBox_subset_dzzVXi hu hv huv (mem_tildeBox_left u v)
    exact ⟨h.1, hξ4.trans h.2⟩
  have hVv : v ∈ dzzVXi ξ := by
    have h := tildeBox_subset_dzzVXi hu hv huv (mem_tildeBox_right u v)
    exact ⟨h.1, hξ4.trans h.2⟩
  have hAB := isXiAdmissible_const_singleton hVu hVv (by linarith)
  obtain ⟨c, hc, hall⟩ := hin
  obtain ⟨δ₀, hδ₀, h2⟩ := (hall _ _ hAB (fun _ _ =>
    ⟨singleton_subset_iff.2 (mem_kXi_tildeBox_left huv h2ξ),
      singleton_subset_iff.2 (mem_kXi_tildeBox_right huv h2ξ)⟩)).2
  refine ⟨δ₀, hδ₀, fun δ' hδ' T hT => le_trans (measure_mono fun ω hω => ?_) (h2 δ' hδ')⟩
  simp only [conc2Event, mem_compl_iff, mem_ofPred_eq, not_le] at hω ⊢
  exact lt_of_lt_of_le (by linarith) (le_abs_self _)

/-- `e^{−x^{0.7}} ≤ (2^{⌊L^{0.51}⌋})^{−4}` for `x ≥ L^{0.95}` and large `L` (DZZ's `O(K⁻⁴)`,
`K = 2^{⌊(log δ⁻¹)^{0.51}⌋}`, l. 2427). -/
lemma l53_K4_of_rpow : ∀ᶠ L : ℝ in atTop, ∀ x : ℝ, L ^ (0.95 : ℝ) ≤ x →
    Real.exp (-(x ^ (0.7 : ℝ))) ≤ ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 := by
  have hev : ∀ᶠ L : ℝ in atTop, 4 * Real.log 2 * L ^ (0.51 : ℝ) ≤ L ^ (0.665 : ℝ) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.665 - 0.51)).eventually
      (eventually_ge_atTop (4 * Real.log 2))
    filter_upwards [h, eventually_gt_atTop 0] with L hL hL0
    have : L ^ (0.665 : ℝ) = L ^ (0.51 : ℝ) * L ^ (0.665 - 0.51 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [this, mul_comm (4 * Real.log 2)]
    exact mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hL0.le _)
  filter_upwards [hev, eventually_ge_atTop 1] with L hL hL1 x hx
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hx0 : 0 ≤ x := (Real.rpow_nonneg hL0 _).trans hx
  -- `x^{0.7} ≥ L^{0.665}`
  have h1 : L ^ (0.665 : ℝ) ≤ x ^ (0.7 : ℝ) := by
    have : L ^ (0.665 : ℝ) = (L ^ (0.95 : ℝ)) ^ (0.7 : ℝ) := by
      rw [← Real.rpow_mul hL0]; norm_num
    rw [this]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hL0 _) hx (by norm_num)
  -- `K⁻⁴ ≥ e^{−4 log 2 L^{0.51}}`
  have hK : ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 =
      Real.exp (-(4 * Real.log 2 * (⌊L ^ (0.51 : ℝ)⌋₊ : ℝ))) := by
    rw [← Real.rpow_natCast 2, Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg,
      ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [hK, Real.exp_le_exp]
  have hfl : (⌊L ^ (0.51 : ℝ)⌋₊ : ℝ) ≤ L ^ (0.51 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hL0 _)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  nlinarith

/-- The crude bound in expectation: `E log D̃_δ(u,v) ≤ A + B log δ⁻¹`. -/
lemma l53_integral_log_tilde_le {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ δ : ℝ, 0 < δ →
      δ ≤ 1 / 2 → (∫ ω, logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v} ∂P) ≤
        A + B * Real.log δ⁻¹ := by
  obtain ⟨A, B, hA, hB, h⟩ := lintegral_log_tilde_le (P := P) hW hγ hγ2
  refine ⟨A, B, hA, hB, fun u hu v hv huv δ hδ hδ2 => ?_⟩
  have hint := integrable_log_tilde hW hγ hγ2 (aemeasurable_wickQArea_ball hW hγ hγ2) hu hv huv hδ
  have hlog : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg (by
    rw [one_le_inv₀ hδ]; linarith)
  rw [integral_eq_lintegral_of_nonneg_ae
    (f := fun ω => logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v})
    (ae_of_all _ fun ω => Real.log_natCast_nonneg _) hint.aestronglyMeasurable]
  calc (∫⁻ ω, ENNReal.ofReal (logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v}) ∂P
        ).toReal ≤ (ENNReal.ofReal (A + B * Real.log δ⁻¹)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (h u hu v hv huv δ hδ hδ2)
    _ = A + B * Real.log δ⁻¹ := ENNReal.toReal_ofReal (by positivity)

/-- **The `(u,v)`-step of the far bound at `μIn`, regime `l log 2 ≤ L^{0.96}`.** -/
theorem l53_uv_far_small {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {ξ : ℝ} (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) (hξ : 0 < ξ)
    (hξ4 : ξ ≤ 1 / 4) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v)
    (h2ξ : 2 * ξ ≤ dist u v) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ l : ℕ, (l : ℝ) * Real.log 2 ≤ L ^ (0.96 : ℝ) →
      P {ω | (∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
          ∂P) + L ^ (0.97 : ℝ) <
        logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω))
          ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ)))) {u} {v}} ≤
        ENNReal.ofReal (((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4) := by
  obtain ⟨δ₀, hδ₀, htail⟩ := l53_uv_tail h317 hξ hξ4 hu hv huv h2ξ
  obtain ⟨A, B, hA, hB, hcr⟩ := l53_integral_log_tilde_le (P := P) hW hγ hγ2
  -- the eventual inequalities in `L`
  have hev1 : ∀ᶠ L : ℝ in atTop, A + (B + 1) * (2 * L ^ (0.96 : ℝ)) ≤ L ^ (0.97 : ℝ) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.97 - 0.96)).eventually
      (eventually_ge_atTop (A + 2 * (B + 1)))
    filter_upwards [h, eventually_ge_atTop 1] with L hL hL1
    have hL0 : 0 < L := by linarith
    have h96 : 1 ≤ L ^ (0.96 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have : L ^ (0.97 : ℝ) = L ^ (0.96 : ℝ) * L ^ (0.97 - 0.96 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [this]
    nlinarith
  have hev2 : ∀ᶠ L : ℝ in atTop, Real.exp (-(L ^ (0.95 : ℝ))) < min δ₀ (1 / 2) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.95)).eventually
      (eventually_gt_atTop (-Real.log (min δ₀ (1 / 2))))
    filter_upwards [h] with L hL
    rw [← Real.exp_log (lt_min hδ₀ (by norm_num) : (0 : ℝ) < min δ₀ (1 / 2))]
    exact Real.exp_lt_exp.2 (by linarith)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1
    (hev1.and (hev2.and (l53_K4_of_rpow.and (eventually_ge_atTop 1))))
  refine ⟨L₀, fun L hL l hl => ?_⟩
  obtain ⟨h1, h2, h3, hL1⟩ := hL₀ L hL
  set δ' : ℝ := (2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ))) with hδ'
  have hpow : 0 < (2 : ℝ)⁻¹ ^ l := by positivity
  have hpow1 : (2 : ℝ)⁻¹ ^ l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hδ'0 : 0 < δ' := by positivity
  have hδ'le : δ' ≤ Real.exp (-(L ^ (0.95 : ℝ))) :=
    mul_le_of_le_one_left (Real.exp_pos _).le hpow1
  have hδ'1 : δ' < δ₀ := hδ'le.trans_lt (h2.trans_le (min_le_left _ _))
  have hδ'2 : δ' ≤ 1 / 2 := (hδ'le.trans h2.le).trans (min_le_right _ _)
  -- `log δ'⁻¹ = l log 2 + L^{0.95}`
  have hx : Real.log δ'⁻¹ = l * Real.log 2 + L ^ (0.95 : ℝ) := by
    rw [hδ', mul_inv, Real.log_mul (by positivity) (by positivity), inv_pow, inv_inv,
      Real.log_pow, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hL0 : 0 ≤ L := by linarith
  have h95 : L ^ (0.95 : ℝ) ≤ L ^ (0.96 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h95' : 1 ≤ L ^ (0.95 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hl0 : 0 ≤ (l : ℝ) * Real.log 2 := by positivity
  have hxge : L ^ (0.95 : ℝ) ≤ Real.log δ'⁻¹ := by rw [hx]; linarith
  have hx1 : 1 ≤ Real.log δ'⁻¹ := h95'.trans hxge
  have hxle : Real.log δ'⁻¹ ≤ 2 * L ^ (0.96 : ℝ) := by rw [hx]; linarith
  have hxpow : Real.log δ'⁻¹ ^ (0.95 : ℝ) ≤ Real.log δ'⁻¹ :=
    Real.rpow_le_self_of_one_le hx1 (by norm_num)
  have hEX : 0 ≤ ∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l)
      {u} {v} ∂P := integral_nonneg fun ω => Real.log_natCast_nonneg _
  have hcrδ := hcr u hu v hv huv δ' hδ'0 hδ'2
  have hT : (∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) δ' {u} {v} ∂P) +
      Real.log δ'⁻¹ ^ (0.95 : ℝ) ≤
      (∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v} ∂P) +
        L ^ (0.97 : ℝ) := by
    have : B * Real.log δ'⁻¹ ≤ B * (2 * L ^ (0.96 : ℝ)) := mul_le_mul_of_nonneg_left hxle hB
    nlinarith
  refine (htail δ' ⟨hδ'0, hδ'1⟩ _ hT).trans ?_
  exact ENNReal.ofReal_le_ofReal (h3 _ hxge)

end DZZ
end LQGMetric
