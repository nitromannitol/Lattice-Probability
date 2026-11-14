/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelMean
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelAeMono
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldExpTail
import Mathlib.MeasureTheory.Integral.MeanInequalities

 












set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneA3R_two_holder : (2 : ℝ).HolderConjugate 2 :=
  Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩

 
theorem laneA3R_lintegral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ (2 : ℝ) ≤ ∫⁻ a, f a ^ (2 : ℝ) ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ laneA3R_two_holder hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at h
  calc (∫⁻ a, f a ∂μ) ^ (2 : ℝ)
      ≤ ((∫⁻ a, f a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ∫⁻ a, f a ^ (2 : ℝ) ∂μ := by
        rw [← ENNReal.rpow_mul]
        norm_num

 
theorem laneA3R_cond_sq_le {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {Z : Ω → ℝ≥0∞} (hZ : Measurable Z) :
    ∫⁻ ω, (∫⁻ x, Z x ∂(condExpKernel P m ω)) ^ (2 : ℝ) ∂P ≤
      ∫⁻ x, Z x ^ (2 : ℝ) ∂P := by
  calc ∫⁻ ω, (∫⁻ x, Z x ∂(condExpKernel P m ω)) ^ (2 : ℝ) ∂P
      ≤ ∫⁻ ω, ∫⁻ x, Z x ^ (2 : ℝ) ∂(condExpKernel P m ω) ∂P :=
        lintegral_mono fun ω => laneA3R_lintegral_sq_le hZ.aemeasurable
    _ = ∫⁻ x, Z x ^ (2 : ℝ) ∂P :=
        laneC_conditional_lintegral_mean P hm (hZ.pow_const _)

 
theorem laneA3R_sq_lintegral_le_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ≥0∞} (hZ : Measurable Z) {A x₀ : ℝ} (hA : 0 < A)
    (hx₀ : 0 ≤ x₀)
    (htail : ∀ t, x₀ < t →
      2 * Real.exp (2 * t) * (P {ω | ENNReal.ofReal (A * Real.exp t) ≤ Z ω}).toReal ≤
        Real.exp (-t)) :
    ∫⁻ ω, Z ω ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (A ^ 2 * (Real.exp (2 * x₀) + 1)) := by
  set X : Ω → ℝ := fun ω => max 0 (Real.log ((Z ω).toReal / A)) with hXdef
  have hXm : Measurable X :=
    measurable_const.max (Real.measurable_log.comp (hZ.ennreal_toReal.div_const A))
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => le_max_left _ _
  
  have hsub : ∀ t, 0 < t → {ω | t ≤ X ω} ⊆ {ω | ENNReal.ofReal (A * Real.exp t) ≤ Z ω} := by
    intro t ht ω hω
    simp only [mem_setOf_eq] at hω ⊢
    have hXpos : 0 < X ω := lt_of_lt_of_le ht hω
    have hXeq : X ω = Real.log ((Z ω).toReal / A) := by
      rcases le_total 0 (Real.log ((Z ω).toReal / A)) with h | h
      · exact max_eq_right h
      · exfalso
        have : X ω = 0 := max_eq_left h
        linarith
    have hlog : t ≤ Real.log ((Z ω).toReal / A) := hXeq ▸ hω
    have hratio : 0 < (Z ω).toReal / A := by
      rcases (div_nonneg ENNReal.toReal_nonneg hA.le).lt_or_eq with h | h
      · exact h
      · rw [← h, Real.log_zero] at hlog; linarith
    have hexp : Real.exp t ≤ (Z ω).toReal / A := by
      rw [← Real.exp_log hratio]; exact Real.exp_le_exp.mpr hlog
    have hle : A * Real.exp t ≤ (Z ω).toReal := by
      rw [le_div_iff₀ hA] at hexp; linarith
    exact (ENNReal.ofReal_le_ofReal hle).trans ENNReal.ofReal_toReal_le
  have hmom := LQGMetric.DDDF.lintegral_exp_le_of_tail (P := P) hX0 hXm.aemeasurable
    (x₀ := x₀) (B := 1) (κ := 1) (l := 2) two_pos hx₀ one_pos zero_le_one
    (fun t ht => by
      have ht0 : 0 < t := lt_of_le_of_lt hx₀ ht
      have hP : P.real {ω | t ≤ X ω} ≤
          (P {ω | ENNReal.ofReal (A * Real.exp t) ≤ Z ω}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hsub t ht0))
      calc 2 * Real.exp (2 * t) * P.real {ω | t ≤ X ω}
          ≤ 2 * Real.exp (2 * t) * (P {ω | ENNReal.ofReal (A * Real.exp t) ≤ Z ω}).toReal :=
            mul_le_mul_of_nonneg_left hP (by positivity)
        _ ≤ Real.exp (-t) := htail t ht
        _ = 1 * Real.exp (-1 * t) := by ring_nf)
  
  have htop : P {ω | Z ω = ⊤} = 0 := by
    have hbound : ∀ t, x₀ < t → (P {ω | Z ω = ⊤}).toReal ≤ Real.exp (-(3 * t)) / 2 := by
      intro t ht
      have h1 : (P {ω | Z ω = ⊤}).toReal ≤
          (P {ω | ENNReal.ofReal (A * Real.exp t) ≤ Z ω}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => by
          simp only [mem_setOf_eq] at hω ⊢; rw [hω]; exact le_top)
      have h2 := htail t ht
      have hpos : 0 < 2 * Real.exp (2 * t) := by positivity
      have h3 : (P {ω | ENNReal.ofReal (A * Real.exp t) ≤ Z ω}).toReal ≤
          Real.exp (-t) / (2 * Real.exp (2 * t)) := by
        rw [le_div_iff₀ hpos]; linarith
      have e : Real.exp (-t) / (2 * Real.exp (2 * t)) = Real.exp (-(3 * t)) / 2 := by
        rw [show -(3 * t) = -t - 2 * t by ring, Real.exp_sub]; field_simp
      linarith
    have hlim : Tendsto (fun t : ℝ => Real.exp (-(3 * t)) / 2) atTop (nhds 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3))).div_const 2
      simpa [Function.comp_def] using this
    have hle : (P {ω | Z ω = ⊤}).toReal ≤ 0 :=
      ge_of_tendsto hlim ((eventually_gt_atTop x₀).mono fun t ht => hbound t ht)
    have h0 : (P {ω | Z ω = ⊤}).toReal = 0 := le_antisymm hle ENNReal.toReal_nonneg
    rcases ENNReal.toReal_eq_zero_iff _ |>.mp h0 with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  have hfin : ∀ᵐ ω ∂P, Z ω ≠ ⊤ := by
    rw [ae_iff]
    simpa using htop
  
  have hpt : ∀ᵐ ω ∂P, Z ω ^ (2 : ℝ) ≤
      ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (Real.exp (2 * X ω)) := by
    filter_upwards [hfin] with ω hω
    have hZle : (Z ω).toReal ≤ A * Real.exp (X ω) := by
      by_cases hr : (Z ω).toReal / A ≤ 1
      · have : (Z ω).toReal ≤ A := by rwa [div_le_one hA] at hr
        have : A ≤ A * Real.exp (X ω) := le_mul_of_one_le_right hA.le
          (Real.one_le_exp (hX0 ω))
        linarith
      · push Not at hr
        have hpos : 0 < (Z ω).toReal / A := by linarith
        have : Real.exp (Real.log ((Z ω).toReal / A)) ≤ Real.exp (X ω) :=
          Real.exp_le_exp.mpr (le_max_right _ _)
        rw [Real.exp_log hpos] at this
        rw [div_le_iff₀ hA] at this
        linarith
    rw [← ENNReal.ofReal_toReal hω, ← ENNReal.ofReal_mul (sq_nonneg A),
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have e : A ^ 2 * Real.exp (2 * X ω) = (A * Real.exp (X ω)) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    rw [e, show ((Z ω).toReal) ^ (2 : ℝ) = ((Z ω).toReal) ^ (2 : ℕ) by norm_cast]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg hZle 2
  calc ∫⁻ ω, Z ω ^ (2 : ℝ) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (Real.exp (2 * X ω)) ∂P :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (A ^ 2) * ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * X ω)) ∂P :=
        lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
          (Real.measurable_exp.comp (hXm.const_mul 2)))
    _ ≤ ENNReal.ofReal (A ^ 2) *
          ENNReal.ofReal (Real.exp (2 * x₀) + 1 * Real.exp (-1 * x₀) / 1) :=
        mul_le_mul' le_rfl hmom
    _ ≤ ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (Real.exp (2 * x₀) + 1) := by
        apply mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal _)
        have : Real.exp (-1 * x₀) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
    _ = ENNReal.ofReal (A ^ 2 * (Real.exp (2 * x₀) + 1)) :=
        (ENNReal.ofReal_mul (sq_nonneg A)).symm

end SupercriticalLQGUniqueness.B2.DG20Conc
