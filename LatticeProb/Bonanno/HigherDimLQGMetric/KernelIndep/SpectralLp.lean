/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.SpectralLp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.SpectralMass

/-! Square integrability of the cosine-sine spectral representatives. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd IsLFPPKernel)

private def specMajorant {d : ℕ} (κ : Rd d → ℝ) (a b : ℝ)
    (p : ℝ × Rd d) : ℝ :=
  (Ico (0 : ℝ) 1).indicator (fun _ => bandSpec κ a b p.2) p.1 +
    (Ico (1 : ℝ) 2).indicator (fun _ => bandSpec κ a b p.2) p.1

private theorem integrable_specMajorant {d : ℕ} (hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Integrable (specMajorant κ a b) volume := by
  have hS := integrable_bandSpec hd hκ ha hab
  have h0 : Integrable ((Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const measure_Ico_lt_top.ne)
  have h1 : Integrable ((Ico (1 : ℝ) 2).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const measure_Ico_lt_top.ne)
  have hp0 := h0.mul_prod hS
  have hp1 := h1.mul_prod hS
  have heq0 : (fun p : ℝ × Rd d =>
      (Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) p.1 * bandSpec κ a b p.2) =
      (fun p => (Ico (0 : ℝ) 1).indicator (fun _ => bandSpec κ a b p.2) p.1) := by
    funext p
    by_cases h : p.1 ∈ Ico (0 : ℝ) 1 <;> simp [h]
  have heq1 : (fun p : ℝ × Rd d =>
      (Ico (1 : ℝ) 2).indicator (fun _ => (1 : ℝ)) p.1 * bandSpec κ a b p.2) =
      (fun p => (Ico (1 : ℝ) 2).indicator (fun _ => bandSpec κ a b p.2) p.1) := by
    funext p
    by_cases h : p.1 ∈ Ico (1 : ℝ) 2 <;> simp [h]
  change Integrable (fun p : ℝ × Rd d =>
    (Ico (0 : ℝ) 1).indicator (fun _ => bandSpec κ a b p.2) p.1 +
    (Ico (1 : ℝ) 2).indicator (fun _ => bandSpec κ a b p.2) p.1) volume
  exact (heq0 ▸ hp0).add (heq1 ▸ hp1)

private theorem measurable_specFun {d : ℕ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (a b : ℝ) (z : Rd d) :
    Measurable (specFun κ a b z) := by
  have hS : Measurable (fun p : ℝ × Rd d => bandSpec κ a b p.2) :=
    (measurable_bandSpec hκ a b).comp measurable_snd
  have hphase : Measurable (fun p : ℝ × Rd d =>
      2 * Real.pi * inner ℝ z p.2) := by fun_prop
  unfold specFun
  have hi0 : MeasurableSet {p : ℝ × Rd d | p.1 ∈ Ico (0 : ℝ) 1} :=
    measurable_fst (measurableSet_Ico)
  have hi1 : MeasurableSet {p : ℝ × Rd d | p.1 ∈ Ico (1 : ℝ) 2} :=
    measurable_fst (measurableSet_Ico)
  have hc := (hS.sqrt.mul hphase.cos).indicator hi0
  have hs := (hS.sqrt.mul hphase.sin).indicator hi1
  convert hc.add hs using 1
  funext p
  by_cases h0 : p.1 ∈ Ico (0 : ℝ) 1 <;>
    by_cases h1 : p.1 ∈ Ico (1 : ℝ) 2 <;>
    simp only [Set.mem_Ico] at h0 h1 <;>
    simp [Set.indicator, h0, h1]

private theorem specFun_sq_le_majorant {d : ℕ} (κ : Rd d → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (z : Rd d) (p : ℝ × Rd d) :
    (specFun κ a b z p) ^ 2 ≤ specMajorant κ a b p := by
  let S := bandSpec κ a b p.2
  have hS : 0 ≤ S := bandSpec_nonneg κ ha p.2
  have hc : (Real.cos (2 * Real.pi * inner ℝ z p.2)) ^ 2 ≤ 1 :=
    Real.cos_sq_le_one _
  have hs : (Real.sin (2 * Real.pi * inner ℝ z p.2)) ^ 2 ≤ 1 :=
    Real.sin_sq_le_one _
  by_cases h0 : p.1 ∈ Ico (0 : ℝ) 1
  · have h1 : p.1 ∉ Ico (1 : ℝ) 2 := by
      intro h1
      exact (not_lt_of_ge h1.1) h0.2
    simp only [specFun, specMajorant, Set.indicator_of_mem h0,
      Set.indicator_of_notMem h1, add_zero]
    calc
      (Real.sqrt S * Real.cos (2 * Real.pi * inner ℝ z p.2)) ^ 2
          = S * (Real.cos (2 * Real.pi * inner ℝ z p.2)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt hS]
      _ ≤ S * 1 := mul_le_mul_of_nonneg_left hc hS
      _ = S := mul_one _
  · by_cases h1 : p.1 ∈ Ico (1 : ℝ) 2
    · simp only [specFun, specMajorant, Set.indicator_of_notMem h0,
        Set.indicator_of_mem h1, zero_add]
      calc
        (Real.sqrt S * Real.sin (2 * Real.pi * inner ℝ z p.2)) ^ 2
            = S * (Real.sin (2 * Real.pi * inner ℝ z p.2)) ^ 2 := by
                rw [mul_pow, Real.sq_sqrt hS]
        _ ≤ S * 1 := mul_le_mul_of_nonneg_left hs hS
        _ = S := mul_one _
    · simp [specFun, specMajorant, h0, h1]

/-- The spectral representative is genuinely square integrable on positive finite bands. -/
theorem memLp_specFun {d : ℕ} (hd : 1 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (z : Rd d) : MemLp (specFun κ a b z) 2 volume := by
  have hm := measurable_specFun hκ a b z
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  apply (integrable_specMajorant hd hκ ha hab).mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact specFun_sq_le_majorant κ ha.le z p

end HigherDimLQGMetric
