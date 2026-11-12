/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53B6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B3

/-!
# From high-probability comparisons to exponents (P2-DZZ53b)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) repeatedly pass from a high-probability comparison
`|log D − log D'| = o(log δ⁻¹)` to the equality of the exponents `E log D / log δ⁻¹`, using the
crude second moments (eq-very-crude), (eq-very-crude-prime) (l. 852–857; e.g. Cor 3.3, l. 859–865,
and "χ does not depend on u,v", l. 2423). `tendsto_sub_div_log_of_close` is this step:
if `E X_δ², E Y_δ² ≤ A + B (log δ⁻¹)²` and `P(|X_δ − Y_δ| > ε log δ⁻¹) → 0` for every `ε > 0`, then
`E X_δ / log δ⁻¹ − E Y_δ / log δ⁻¹ → 0`. Own elementary proof
(`|X − Y| ≤ εL + (2X² + 2Y²)/M + M 1_{bad}` with `M = KL`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma integrable_sq_of_lintegral {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hf : Integrable f P)
    {c : ℝ} (hc : ∫⁻ ω, ENNReal.ofReal (f ω) ^ 2 ∂P ≤ ENNReal.ofReal c) :
    Integrable (fun ω => f ω ^ 2) P ∧ ∫ ω, f ω ^ 2 ∂P ≤ max c 0 := by
  have hm : AEStronglyMeasurable (fun ω => f ω ^ 2) P := hf.aestronglyMeasurable.pow 2
  have eofr : ∀ ω, ENNReal.ofReal (f ω ^ 2) = ENNReal.ofReal (f ω) ^ 2 := fun ω =>
    ENNReal.ofReal_pow (hf0 ω) 2
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)]
    simp only [eofr]
    exact hc.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _) hm]
    simp only [eofr]
    refine ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (hc.trans ?_)
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)

lemma one_lt_log_inv_of_lt {δ : ℝ} (hδ : 0 < δ) (h3 : δ < 1 / 3) : 1 < Real.log δ⁻¹ := by
  rw [Real.lt_log_iff_exp_lt (inv_pos.2 hδ)]
  have h1 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have : (3 : ℝ) < δ⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hδ]; linarith
  linarith

/-- **High-probability closeness of `X_δ` and `Y_δ` at scale `o(log δ⁻¹)` plus crude second
moments give equal exponents.** -/
theorem tendsto_sub_div_log_of_close [IsProbabilityMeasure P] {X Y : ℝ → Ω → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hX0 : ∀ δ ω, 0 ≤ X δ ω) (hY0 : ∀ δ ω, 0 ≤ Y δ ω)
    (hXi : ∀ δ, 0 < δ → Integrable (X δ) P) (hYi : ∀ δ, 0 < δ → Integrable (Y δ) P)
    (hX2 : ∀ δ, 0 < δ → δ ≤ 1 / 2 → ∫⁻ ω, ENNReal.ofReal (X δ ω) ^ 2 ∂P ≤
      ENNReal.ofReal (A + B * Real.log δ⁻¹ ^ 2))
    (hY2 : ∀ δ, 0 < δ → δ ≤ 1 / 2 → ∫⁻ ω, ENNReal.ofReal (Y δ ω) ^ 2 ∂P ≤
      ENNReal.ofReal (A + B * Real.log δ⁻¹ ^ 2))
    (hclose : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ => P {ω | ε * Real.log δ⁻¹ < |X δ ω - Y δ ω|})
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun δ => (∫ ω, X δ ω ∂P) / Real.log δ⁻¹ - (∫ ω, Y δ ω ∂P) / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  set K : ℝ := 16 * (A + B) / η + 1 with hK
  have hK0 : 0 < K := by positivity
  have hKb : 4 * (A + B) / K ≤ η / 4 := by
    rw [div_le_iff₀ hK0, hK]
    have : 16 * (A + B) / η * η = 16 * (A + B) := by field_simp
    nlinarith
  have hc := (hclose (η / 4) (by positivity)).eventually
    (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal (η / (4 * K)) by
      rw [ENNReal.ofReal_pos]; positivity))
  filter_upwards [hc, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 3 by norm_num)] with δ hPδ hδ
  obtain ⟨hδ0, hδ3⟩ := hδ
  set L := Real.log δ⁻¹ with hL
  have hL1 : 1 < L := one_lt_log_inv_of_lt hδ0 hδ3
  have hL0 : 0 < L := by linarith
  have hδ2 : δ ≤ 1 / 2 := by linarith
  obtain ⟨hXs, hXs'⟩ := integrable_sq_of_lintegral (hX0 δ) (hXi δ hδ0) (hX2 δ hδ0 hδ2)
  obtain ⟨hYs, hYs'⟩ := integrable_sq_of_lintegral (hY0 δ) (hYi δ hδ0) (hY2 δ hδ0 hδ2)
  have hABL : 0 ≤ A + B * L ^ 2 := by positivity
  rw [max_eq_left hABL] at hXs' hYs'
  set Bd := {ω | η / 4 * L < |X δ ω - Y δ ω|} with hBd
  set T := toMeasurable P Bd with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable P _
  have hPT : P.real T < η / (4 * K) := by
    rw [measureReal_def, hT, measure_toMeasurable]
    exact (ENNReal.toReal_lt_of_lt_ofReal hPδ)
  set M := K * L with hM
  have hM0 : 0 < M := by positivity
  have hpt : ∀ ω, |X δ ω - Y δ ω| ≤ η / 4 * L + (2 * X δ ω ^ 2 + 2 * Y δ ω ^ 2) / M +
      M * T.indicator 1 ω := by
    intro ω
    have hx := hX0 δ ω; have hy := hY0 δ ω
    have hq : 0 ≤ (2 * X δ ω ^ 2 + 2 * Y δ ω ^ 2) / M := by positivity
    have hs : |X δ ω - Y δ ω| ≤ X δ ω + Y δ ω := by
      rw [abs_le]; constructor <;> linarith
    by_cases hω : ω ∈ Bd
    · have hiT : T.indicator (1 : Ω → ℝ) ω = 1 := by
        rw [indicator_of_mem (subset_toMeasurable P _ hω), Pi.one_apply]
      rw [hiT, mul_one]
      have hηL : 0 ≤ η / 4 * L := by positivity
      by_cases hxM : X δ ω + Y δ ω ≤ M
      · linarith
      · push Not at hxM
        have : X δ ω + Y δ ω ≤ (2 * X δ ω ^ 2 + 2 * Y δ ω ^ 2) / M := by
          rw [le_div_iff₀ hM0]
          nlinarith [sq_nonneg (X δ ω - Y δ ω)]
        linarith
    · have : |X δ ω - Y δ ω| ≤ η / 4 * L := not_lt.1 hω
      have : 0 ≤ M * T.indicator (1 : Ω → ℝ) ω :=
        mul_nonneg hM0.le (indicator_nonneg (fun _ _ => zero_le_one) _)
      linarith
  have hi1 : Integrable (fun ω => (2 * X δ ω ^ 2 + 2 * Y δ ω ^ 2) / M) P :=
    ((hXs.const_mul 2).add (hYs.const_mul 2)).div_const M
  have hi2 : Integrable (fun ω => M * T.indicator (1 : Ω → ℝ) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hTm).const_mul M
  have hint : ∫ ω, |X δ ω - Y δ ω| ∂P ≤
      η / 4 * L + (2 * (A + B * L ^ 2) + 2 * (A + B * L ^ 2)) / M + M * (η / (4 * K)) := by
    calc ∫ ω, |X δ ω - Y δ ω| ∂P
        ≤ ∫ ω, (η / 4 * L + (2 * X δ ω ^ 2 + 2 * Y δ ω ^ 2) / M + M * T.indicator 1 ω) ∂P :=
          integral_mono ((hXi δ hδ0).sub (hYi δ hδ0)).abs
            (((integrable_const _).add hi1).add hi2) hpt
      _ = η / 4 * L + (2 * (∫ ω, X δ ω ^ 2 ∂P) + 2 * (∫ ω, Y δ ω ^ 2 ∂P)) / M +
          M * P.real T := by
          have h1 := integral_add ((integrable_const (η / 4 * L)).add hi1) hi2
          have h2 := integral_add (integrable_const (η / 4 * L)) hi1
          have h3 := integral_add (hXs.const_mul 2) (hYs.const_mul 2)
          simp only [Pi.add_apply] at h1 h2 h3
          rw [h1, h2, integral_const, integral_div, h3, integral_const_mul, integral_const_mul,
            integral_const_mul, integral_indicator_one hTm]
          simp
      _ ≤ _ := by
          gcongr
  have hdiff : |(∫ ω, X δ ω ∂P) - ∫ ω, Y δ ω ∂P| ≤ ∫ ω, |X δ ω - Y δ ω| ∂P := by
    rw [← integral_sub (hXi δ hδ0) (hYi δ hδ0)]
    exact abs_integral_le_integral_abs
  rw [dist_zero_right, Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hL0,
    div_lt_iff₀ hL0]
  have e1 : (2 * (A + B * L ^ 2) + 2 * (A + B * L ^ 2)) / M ≤ 4 * (A + B) / K * L := by
    rw [hM, div_le_iff₀ hM0]
    have : 4 * (A + B) / K * L * (K * L) = 4 * (A + B) * L ^ 2 := by field_simp
    rw [this]
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hL2 hA]
  have e2 : M * (η / (4 * K)) = η / 4 * L := by rw [hM]; field_simp
  have e3 : 4 * (A + B) / K * L ≤ η / 4 * L := mul_le_mul_of_nonneg_right hKb hL0.le
  nlinarith

end DZZ
end LQGMetric
