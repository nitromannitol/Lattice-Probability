/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RC2Cond at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RC2Moment
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTripleHolder
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConcaveMoment
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelAeMono

 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneA4R_cond_max_sq_le {Ω ι : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) (I : Finset ι) {R : Ω → ℝ≥0∞} (hR : Measurable R)
    {E D U : ι → Ω → ℝ≥0∞} (hE : ∀ b, Measurable (E b)) (hU : ∀ b, AEMeasurable (U b) P)
    (hDU : ∀ b ∈ I, ∀ x, D b x ≤ E b x * U b x)
    {q ζ : ℝ} (hq : 0 < q) (hζ : 0 < ζ) (hζ1 : ζ < 1) {G : ℝ≥0∞}
    (hG : ∀ b ∈ I, ∀ᵐ ω ∂P,
      ∫⁻ x, E b x ^ (q * (1 + ζ)) ∂(condExpKernel P m ω) ≤ G) :
    ∫⁻ ω, (I.sup fun b => ∫⁻ x, R x ^ q * D b x ^ q ∂(condExpKernel P m ω)) ^ (2 : ℝ) ∂P ≤
      (G ^ (1 / (1 + ζ))) ^ (2 : ℝ) *
        ((∫⁻ x, R x ^ (q * (2 * ((1 + ζ) / ζ))) ∂P) ^ (2 * ζ / (1 + ζ))) ^ (1 / 2 : ℝ) *
        ((∫⁻ x, (I.sup fun b => U b x) ^ (q * (2 * ((1 + ζ) / ζ))) ∂P) ^
          (2 * ζ / (1 + ζ))) ^ (1 / 2 : ℝ) := by
  set κ := condExpKernel P m with hκ
  set r : ℝ := 2 * ((1 + ζ) / ζ) with hr
  set α : ℝ := ζ / (2 * (1 + ζ)) with hα
  set β : ℝ := 1 / (1 + ζ) with hβ
  set γ : ℝ := 2 * ζ / (1 + ζ) with hγ
  have h1ζ : 0 < 1 + ζ := by linarith
  have hr0 : 0 < r := by positivity
  have hα0 : 0 < α := by positivity
  have hγ0 : 0 < γ := by positivity
  have hγ1 : γ < 1 := by rw [hγ, div_lt_one h1ζ]; linarith
  set M : Ω → ℝ≥0∞ := fun x => I.sup fun b => U b x with hMdef
  have hMae : AEMeasurable M P := laneA4R_aemeasurable_finset_sup I hU
  set M' : Ω → ℝ≥0∞ := hMae.mk M with hM'def
  have hM'm : Measurable M' := hMae.measurable_mk
  have hMM' : M =ᵐ[P] M' := hMae.ae_eq_mk
  
  set A : Ω → ℝ≥0∞ := fun ω => ∫⁻ x, (R x ^ q) ^ r ∂(κ ω) with hA
  set B : Ω → ℝ≥0∞ := fun ω => ∫⁻ x, (M' x ^ q) ^ r ∂(κ ω) with hB
  have hAm : Measurable A :=
    (Measurable.lintegral_kernel ((hR.pow_const q).pow_const r)).mono hm le_rfl
  have hBm : Measurable B :=
    (Measurable.lintegral_kernel ((hM'm.pow_const q).pow_const r)).mono hm le_rfl
  
  have hpt : ∀ b ∈ I, ∀ x, R x ^ q * D b x ^ q ≤ (R x ^ q * M x ^ q) * E b x ^ q := by
    intro b hb x
    have hle : D b x ≤ E b x * M x :=
      (hDU b hb x).trans (mul_le_mul_right (Finset.le_sup (f := fun b => U b x) hb) _)
    calc R x ^ q * D b x ^ q ≤ R x ^ q * (E b x * M x) ^ q :=
          mul_le_mul_right (ENNReal.rpow_le_rpow hle hq.le) _
      _ = (R x ^ q * M x ^ q) * E b x ^ q := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]; ring
  have hstep : ∀ b ∈ I, ∀ᵐ ω ∂P,
      ∫⁻ x, R x ^ q * D b x ^ q ∂(κ ω) ≤ A ω ^ α * B ω ^ α * G ^ β := by
    intro b hb
    have hcongr : (fun x => (R x ^ q * M x ^ q) * E b x ^ q) =ᵐ[P]
        fun x => (R x ^ q * M' x ^ q) * E b x ^ q := by
      filter_upwards [hMM'] with x hx
      rw [hx]
    filter_upwards [laneC_conditional_lintegral_mono_ae P hm hcongr.le, hG b hb] with ω h1 h2
    have hhol := laneC_triple_holder_at (κ ω) (hR.pow_const q).aemeasurable
      (hM'm.pow_const q).aemeasurable ((hE b).pow_const q).aemeasurable hζ
    have hEq : ∫⁻ x, (E b x ^ q) ^ (1 + ζ) ∂(κ ω) ≤ G := by
      refine le_trans (le_of_eq ?_) h2
      refine lintegral_congr fun x => ?_
      rw [← ENNReal.rpow_mul]
    calc ∫⁻ x, R x ^ q * D b x ^ q ∂(κ ω)
        ≤ ∫⁻ x, (R x ^ q * M x ^ q) * E b x ^ q ∂(κ ω) := lintegral_mono (hpt b hb)
      _ ≤ ∫⁻ x, (R x ^ q * M' x ^ q) * E b x ^ q ∂(κ ω) := h1
      _ ≤ A ω ^ α * B ω ^ α * (∫⁻ x, (E b x ^ q) ^ (1 + ζ) ∂(κ ω)) ^ (1 / (1 + ζ)) := hhol
      _ ≤ A ω ^ α * B ω ^ α * G ^ β :=
          mul_le_mul_right (ENNReal.rpow_le_rpow hEq (by positivity)) _
  have hall : ∀ᵐ ω ∂P, ∀ b ∈ I,
      ∫⁻ x, R x ^ q * D b x ^ q ∂(κ ω) ≤ A ω ^ α * B ω ^ α * G ^ β :=
    (Filter.eventually_all_finset I).mpr hstep
  
  have hsq : ∀ᵐ ω ∂P,
      (I.sup fun b => ∫⁻ x, R x ^ q * D b x ^ q ∂(κ ω)) ^ (2 : ℝ) ≤
        (A ω ^ α) ^ (2 : ℝ) * (B ω ^ α) ^ (2 : ℝ) * (G ^ β) ^ (2 : ℝ) := by
    filter_upwards [hall] with ω hω
    have := ENNReal.rpow_le_rpow (Finset.sup_le hω) (by norm_num : (0 : ℝ) ≤ 2)
    rwa [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)] at this
  have hfA : Measurable fun ω => (A ω ^ α) ^ (2 : ℝ) := (hAm.pow_const _).pow_const _
  have hfB : Measurable fun ω => (B ω ^ α) ^ (2 : ℝ) := (hBm.pow_const _).pow_const _
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq P laneA3R_two_holder hfA.aemeasurable
    hfB.aemeasurable
  have hpowA : ∀ ω, ((A ω ^ α) ^ (2 : ℝ)) ^ (2 : ℝ) = A ω ^ γ := by
    intro ω
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 1; rw [hα, hγ]; field_simp
  have hpowB : ∀ ω, ((B ω ^ α) ^ (2 : ℝ)) ^ (2 : ℝ) = B ω ^ γ := by
    intro ω
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 1; rw [hα, hγ]; field_simp
  have hJA : ∫⁻ ω, A ω ^ γ ∂P ≤ (∫⁻ x, (R x ^ q) ^ r ∂P) ^ γ :=
    laneC_conditional_lintegral_concave_moment P hm ((hR.pow_const q).pow_const r) hγ0 hγ1
  have hJB : ∫⁻ ω, B ω ^ γ ∂P ≤ (∫⁻ x, (M' x ^ q) ^ r ∂P) ^ γ :=
    laneC_conditional_lintegral_concave_moment P hm ((hM'm.pow_const q).pow_const r) hγ0 hγ1
  have hRr : ∫⁻ x, (R x ^ q) ^ r ∂P = ∫⁻ x, R x ^ (q * r) ∂P :=
    lintegral_congr fun x => by rw [← ENNReal.rpow_mul]
  have hMr : ∫⁻ x, (M' x ^ q) ^ r ∂P = ∫⁻ x, M x ^ (q * r) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hMM'] with x hx
    rw [hx, ← ENNReal.rpow_mul]
  calc ∫⁻ ω, (I.sup fun b => ∫⁻ x, R x ^ q * D b x ^ q ∂(κ ω)) ^ (2 : ℝ) ∂P
      ≤ ∫⁻ ω, (A ω ^ α) ^ (2 : ℝ) * (B ω ^ α) ^ (2 : ℝ) * (G ^ β) ^ (2 : ℝ) ∂P :=
        lintegral_mono_ae hsq
    _ = (∫⁻ ω, (A ω ^ α) ^ (2 : ℝ) * (B ω ^ α) ^ (2 : ℝ) ∂P) * (G ^ β) ^ (2 : ℝ) :=
        lintegral_mul_const _ (hfA.mul hfB)
    _ ≤ ((∫⁻ ω, ((A ω ^ α) ^ (2 : ℝ)) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, ((B ω ^ α) ^ (2 : ℝ)) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))) * (G ^ β) ^ (2 : ℝ) :=
        mul_le_mul_left hCS _
    _ = ((∫⁻ ω, A ω ^ γ ∂P) ^ (1 / (2 : ℝ)) * (∫⁻ ω, B ω ^ γ ∂P) ^ (1 / (2 : ℝ))) *
          (G ^ β) ^ (2 : ℝ) := by
        simp only [hpowA, hpowB]
    _ ≤ (((∫⁻ x, R x ^ (q * r) ∂P) ^ γ) ^ (1 / (2 : ℝ)) *
          ((∫⁻ x, M x ^ (q * r) ∂P) ^ γ) ^ (1 / (2 : ℝ))) * (G ^ β) ^ (2 : ℝ) := by
        rw [← hRr, ← hMr]
        gcongr
    _ = (G ^ β) ^ (2 : ℝ) * ((∫⁻ x, R x ^ (q * r) ∂P) ^ γ) ^ (1 / 2 : ℝ) *
          ((∫⁻ x, M x ^ (q * r) ∂P) ^ γ) ^ (1 / 2 : ℝ) := by
        rw [show (1 / (2 : ℝ)) = (1 / 2 : ℝ) by norm_num]; ring

end SupercriticalLQGUniqueness.B2.DG20Conc
