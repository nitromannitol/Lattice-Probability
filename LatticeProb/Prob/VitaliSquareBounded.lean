import Mathlib

/-!
# Vitali convergence under a uniform second-moment bound

On a finite measure space, a sequence `f n` with uniformly bounded second moments `∫ ‖f n‖² ≤ K` is uniformly
integrable (`uniformIntegrable_one_of_lintegral_sq_le`): on the set `{c ≤ ‖f n‖}` one has `‖f n‖ ≤ c⁻¹ ‖f n‖²`, so the
integral of `‖f n‖` over that set is at most `K / c`, uniformly in `n`.

Consequently, if `f n → g` in measure, then `g` is integrable and `∫ f n → ∫ g`
(`tendsto_integral_of_tendstoInMeasure_of_lintegral_sq_le`): the Vitali convergence theorem
(`MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure`) gives convergence in `L¹`, and integrability of `g` follows
from Fatou's lemma along an almost surely convergent subsequence.

Literature: Vitali's convergence theorem and the uniform integrability of bounded sets in `L^q`, `q > 1`,
e.g. Bogachev, *Measure Theory*, Vol. I, Sec. 4.5 (Springer 2007).
-/

namespace LatticeProb

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- For `c > 0` and a value `a = ‖f x‖ₑ` with `c ≤ a`, one has `a ≤ c⁻¹ a²`. -/
theorem enorm_le_inv_mul_enorm_sq {c : ℝ≥0} (hc : 0 < c) {a : ℝ≥0∞} (hca : (c : ℝ≥0∞) ≤ a) :
    a ≤ (c : ℝ≥0∞)⁻¹ * a ^ 2 := by
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hct : (c : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  calc a = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * a) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
    _ ≤ (c : ℝ≥0∞)⁻¹ * (a * a) := by gcongr
    _ = (c : ℝ≥0∞)⁻¹ * a ^ 2 := by rw [sq]

/-- **A uniform second-moment bound gives uniform integrability** on a finite measure space. -/
theorem uniformIntegrable_one_of_lintegral_sq_le [IsFiniteMeasure μ] {f : ℕ → α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {K : ℝ≥0}
    (hK : ∀ n, ∫⁻ x, ‖f n x‖ₑ ^ 2 ∂μ ≤ K) : UniformIntegrable f 1 μ := by
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top hf fun ε hε => ?_
  -- a threshold `c > 0` with `K ≤ c ε`
  obtain ⟨c, hc, hKc⟩ : ∃ c : ℝ≥0, 0 < c ∧ (K : ℝ≥0∞) ≤ c * ε := by
    rcases eq_or_ne ε ∞ with rfl | hεt
    · exact ⟨1, one_pos, by simp⟩
    · lift ε to ℝ≥0 using hεt
      have hε0 : 0 < ε := by exact_mod_cast hε
      refine ⟨K / ε + 1, by positivity, ?_⟩
      have : K ≤ (K / ε + 1) * ε := by
        rw [add_mul, div_mul_cancel₀ _ hε0.ne']
        exact le_self_add
      exact_mod_cast this
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hct : (c : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  refine ⟨c, fun n => ?_⟩
  have hmeas : AEStronglyMeasurable ({x | c ≤ ‖f n x‖₊}.indicator (f n)) μ :=
    (hf n).indicator₀ (((hf n).nnnorm.aemeasurable).nullMeasurableSet_preimage measurableSet_Ici)
  rw [eLpNorm_one_eq_lintegral_enorm hmeas]
  have hpt : ∀ x, ‖({x | c ≤ ‖f n x‖₊}.indicator (f n)) x‖ₑ ≤ (c : ℝ≥0∞)⁻¹ * ‖f n x‖ₑ ^ 2 := by
    intro x
    by_cases h : c ≤ ‖f n x‖₊
    · rw [Set.indicator_of_mem (show x ∈ {x | c ≤ ‖f n x‖₊} from h)]
      exact enorm_le_inv_mul_enorm_sq hc (by exact_mod_cast h)
    · rw [Set.indicator_of_notMem (show x ∉ {x | c ≤ ‖f n x‖₊} from h)]
      simp
  calc ∫⁻ x, ‖({x | c ≤ ‖f n x‖₊}.indicator (f n)) x‖ₑ ∂μ
      ≤ ∫⁻ x, (c : ℝ≥0∞)⁻¹ * ‖f n x‖ₑ ^ 2 ∂μ := lintegral_mono hpt
    _ = (c : ℝ≥0∞)⁻¹ * ∫⁻ x, ‖f n x‖ₑ ^ 2 ∂μ := lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0)
    _ ≤ (c : ℝ≥0∞)⁻¹ * K := by gcongr; exact hK n
    _ ≤ (c : ℝ≥0∞)⁻¹ * (c * ε) := by gcongr
    _ = ε := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-- **Vitali convergence under a second-moment bound.** On a finite measure space, if `f n → g` in measure and
`∫ ‖f n‖² ≤ K` for all `n`, then `g` is integrable and `∫ f n → ∫ g`. -/
theorem tendsto_integral_of_tendstoInMeasure_of_lintegral_sq_le [IsFiniteMeasure μ] {f : ℕ → α → ℝ}
    {g : α → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) μ) {K : ℝ≥0}
    (hK : ∀ n, ∫⁻ x, ‖f n x‖ₑ ^ 2 ∂μ ≤ K) (hfg : TendstoInMeasure μ f atTop g) :
    Integrable g μ ∧ Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hui : UniformIntegrable f 1 μ := uniformIntegrable_one_of_lintegral_sq_le hf hK
  obtain ⟨ns, hns, hae⟩ := hfg.exists_seq_tendsto_ae
  have hgm : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => hf (ns n)) hae
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, ∀ n, eLpNorm (f n) 1 μ ≤ C := hui.2
  have hint : Integrable g μ :=
    memLp_one_iff_integrable.1 (memLp_iff.2 (((Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => hf (ns n)) g hgm hae).trans (liminf_le_of_frequently_le' (Frequently.of_forall
        fun n => hC (ns n)))).trans_lt ENNReal.coe_lt_top))
  refine ⟨hint, ?_⟩
  have hL1 := tendsto_Lp_finite_of_tendstoInMeasure (p := 1) le_rfl ENNReal.one_ne_top hf
    (memLp_one_iff_integrable.2 hint) hui.1 hfg
  refine tendsto_integral_of_L1 g hint.aestronglyMeasurable
    (Eventually.of_forall fun n => ?_) ?_
  · refine ⟨hf n, ?_⟩
    rw [HasFiniteIntegral, ← eLpNorm_one_eq_lintegral_enorm (hf n)]
    exact (hC n).trans_lt ENNReal.coe_lt_top
  · refine hL1.congr fun n => ?_
    rw [eLpNorm_one_eq_lintegral_enorm ((hf n).sub hgm)]
    rfl

end LatticeProb
