import LatticeProb.LQG.WholePlaneAreaNull
import LatticeProb.Prob.IndependentNullSection

/-! # Independent null sections of whole-plane quantum area -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb.Gauss

/-- An independent measurable random Lebesgue-null section has zero whole-plane
quantum area on every fixed compact subset of the unit disk. -/
theorem IsWholePlaneGFF.ae_lqgMeasure_inter_compact_eq_zero_of_indepFun
    {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ)
    (hμm : AEMeasurable μ P) {Y : Ω → B} (hY : Measurable Y)
    (hind : IndepFun Y μ P) {S : Set (B × ℂ)} (hS : MeasurableSet S)
    (hnull : ∀ᵐ ω ∂P, volume (Prod.mk (Y ω) ⁻¹' S) = 0)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ Metric.ball (0 : ℂ) 1) :
    ∀ᵐ ω ∂P, μ ω ((Prod.mk (Y ω) ⁻¹' S) ∩ K) = 0 := by
  let μ₀ := hμm.mk μ
  have hμ₀ : Measurable μ₀ := hμm.measurable_mk
  have heq : μ =ᵐ[P] μ₀ := hμm.ae_eq_mk
  let κ : Kernel (Measure ℂ) ℂ :=
    ⟨fun m => if m K < ⊤ then m.restrict K else 0, by
      apply Measurable.ite ((Measure.measurable_coe hK.measurableSet)
        (measurableSet_Iio : MeasurableSet (Iio (⊤ : ℝ≥0∞))))
      · refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
        simpa only [Measure.restrict_apply ht] using Measure.measurable_coe (ht.inter hK.measurableSet)
      · exact measurable_const⟩
  have hκ : ∀ m, IsFiniteMeasure (κ m) := by
    intro m
    change IsFiniteMeasure (if m K < ⊤ then m.restrict K else 0)
    by_cases hm : m K < ⊤
    · simpa [hm] using (isFiniteMeasure_restrict.mpr hm.ne)
    · simpa [hm] using (inferInstance : IsFiniteMeasure (0 : Measure ℂ))
  have hfixed : ∀ b, volume (Prod.mk b ⁻¹' S) = 0 →
      ∀ᵐ ω ∂P, κ (μ₀ ω) (Prod.mk b ⁻¹' S) = 0 := by
    intro b hb
    have hs : MeasurableSet (Prod.mk b ⁻¹' S) := measurable_prodMk_left hS
    have hz := hh.ae_lqgMeasure_eq_zero_of_volume_eq_zero hγ0 hγ2 hμ
      (hs.inter hK.measurableSet) (measure_mono_null inter_subset_left hb)
      (inter_subset_right.trans hKsub)
    filter_upwards [hz, heq] with ω hω hωeq
    change (if μ₀ ω K < ⊤ then (μ₀ ω).restrict K else 0) (Prod.mk b ⁻¹' S) = 0
    by_cases hf : μ₀ ω K < ⊤
    · simp only [hf, ↓reduceIte, Measure.restrict_apply hs]
      rw [← hωeq]
      exact hω
    · simp [hf]
  have hresult := LatticeProb.ae_kernel_section_eq_zero_of_indepFun hμ₀ hY
    (hind.congr (Filter.EventuallyEq.rfl) heq) κ hκ volume hS hfixed hnull
  filter_upwards [hresult, heq, hμ] with ω hω hωeq hωμ
  have hf : μ₀ ω K < ⊤ := by
    rw [← hωeq]
    let := hωμ.isLocallyFiniteMeasure
    exact hK.measure_lt_top
  change (if μ₀ ω K < ⊤ then (μ₀ ω).restrict K else 0)
    (Prod.mk (Y ω) ⁻¹' S) = 0 at hω
  simp only [hf, ↓reduceIte, Measure.restrict_apply (measurable_prodMk_left hS)] at hω
  rw [← hωeq] at hω
  exact hω

end LatticeProb.Gauss
