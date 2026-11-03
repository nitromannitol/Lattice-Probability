/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.Existence.AdmissibleAux at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.HeatFeature
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2

/-!
# Admissible measures: the integrability package, and examples

* `gffEx_hkGood`: two admissible measures satisfy `HkGood` (no mass on the diagonal or its
  reflection, and integrable `log|x - y|`, `log|x - ȳ|`).
* `gffEx_admissible_zero`, `gffEx_admissible_smul`, `gffEx_admissible_ref`: the zero measure,
  finite multiples of admissible measures, and the uniform measure on the circle `∂B(2i, 1)`
  are admissible.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ComplexConjugate ENNReal

namespace QuantumZipper.GFFExist

/-! ### No atoms, null diagonal -/

theorem gffEx_measure_singleton {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (a : ℂ) : μ {a} = 0 := by
  obtain ⟨hfin, -, C, hC, hbd⟩ := hμ
  by_contra hne
  set m : ℝ := (μ {a}).toReal with hm_def
  have hm : 0 < m := ENNReal.toReal_pos hne (measure_ne_top μ _)
  set L : ℝ := C.toReal / m + 1 with hL_def
  have hL : 0 < L := by positivity
  set y : ℂ := a + (Real.exp (-L) : ℂ) with hy_def
  have hnorm : ‖a - y‖ = Real.exp (-L) := by
    rw [hy_def, sub_add_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have h1 : ∫⁻ x in {a}, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ := setLIntegral_le_lintegral _ _
  rw [lintegral_singleton, hnorm, Real.log_exp, neg_neg] at h1
  have h2 := h1.trans (hbd y)
  have hmeq : μ {a} = ENNReal.ofReal m := (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
  rw [hmeq, ← ENNReal.ofReal_mul hL.le, ← ENNReal.ofReal_toReal hC.ne,
    ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at h2
  have : L * m = C.toReal + m := by
    rw [hL_def]; field_simp
  linarith

theorem gffEx_prod_diag {μ ν : Measure ℂ} [SFinite ν] (hν : IsAdmissibleH ν) :
    (μ.prod ν) {z : ℂ × ℂ | z.1 = z.2} = 0 := by
  have hs : MeasurableSet {z : ℂ × ℂ | z.1 = z.2} := measurableSet_eq_fun measurable_fst
    measurable_snd
  rw [Measure.prod_apply hs]
  have : ∀ x : ℂ, ν (Prod.mk x ⁻¹' {z : ℂ × ℂ | z.1 = z.2}) = 0 := by
    intro x
    have e : Prod.mk x ⁻¹' {z : ℂ × ℂ | z.1 = z.2} = {x} := by
      ext y; simp [eq_comm]
    rw [e]
    exact gffEx_measure_singleton hν x
  simp only [this, lintegral_zero]

/-! ### The integrability package -/

lemma gffEx_abs_log_le {D d B : ℝ} (hd : 0 < d) (hdD : d ≤ D) (hDB : D ≤ B) (hB : 1 ≤ B) :
    |Real.log D| ≤ Real.log B + max (-Real.log d) 0 := by
  have hD : 0 < D := hd.trans_le hdD
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB
  rcases le_total 1 D with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_log hD hDB
    have := le_max_right (-Real.log d) 0
    linarith
  · rw [abs_of_nonpos (Real.log_nonpos hD.le h)]
    have := Real.log_le_log hd hdD
    have := le_max_left (-Real.log d) 0
    linarith

theorem gffEx_hkGood {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) :
    HkGood μ ν := by
  have := hμ.1
  have := hν.1
  obtain ⟨K₁, hK₁, hK₁H, hK₁0⟩ := hμ.2.1
  obtain ⟨K₂, hK₂, hK₂H, hK₂0⟩ := hν.2.1
  obtain ⟨C₁, hC₁, hbd₁⟩ := hμ.2.2
  obtain ⟨R, hR⟩ := (hK₁.union hK₂).isBounded.subset_closedBall 0
  set B : ℝ := max (2 * R) 1 with hB_def
  have hB1 : 1 ≤ B := le_max_right _ _
  have h1 : ∀ᵐ z ∂(μ.prod ν), z.1 ∈ K₁ := by
    have : ∀ᵐ x ∂μ, x ∈ K₁ := by
      rw [ae_iff]; exact hK₁0
    exact Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst this
  have h2 : ∀ᵐ z ∂(μ.prod ν), z.2 ∈ K₂ := by
    have : ∀ᵐ x ∂ν, x ∈ K₂ := by
      rw [ae_iff]; exact hK₂0
    exact Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd this
  have hdiag : ∀ᵐ z ∂(μ.prod ν), z.1 ≠ z.2 := by
    rw [ae_iff]; simpa using gffEx_prod_diag (μ := μ) hν
  -- pointwise facts on the good set
  have hgood : ∀ᵐ z ∂(μ.prod ν), 0 < ‖z.1 - z.2‖ ∧ ‖z.1 - z.2‖ ≤ ‖z.1 - conj z.2‖ ∧
      ‖z.1 - z.2‖ ≤ B ∧ ‖z.1 - conj z.2‖ ≤ B := by
    filter_upwards [h1, h2, hdiag] with z hz1 hz2 hz
    have n1 : ‖z.1‖ ≤ R := by simpa using hR (mem_union_left _ hz1)
    have n2 : ‖z.2‖ ≤ R := by simpa using hR (mem_union_right _ hz2)
    have hB2 : 2 * R ≤ B := le_max_left _ _
    refine ⟨norm_pos_iff.2 (sub_ne_zero.2 hz), norm_sub_le_norm_sub_conj (hK₁H hz1) (hK₂H hz2),
      ?_, ?_⟩
    · linarith [norm_sub_le z.1 z.2]
    · have := norm_sub_le z.1 (conj z.2)
      rw [Complex.norm_conj] at this
      linarith
  have hlin : ∫⁻ z, ENNReal.ofReal (-Real.log ‖z.1 - z.2‖) ∂(μ.prod ν) ≠ ⊤ := by
    rw [lintegral_prod_symm _ (by fun_prop)]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun y => hbd₁ y)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top hC₁.ne (measure_ne_top ν _)
  have hg : Integrable (fun z : ℂ × ℂ => max (-Real.log ‖z.1 - z.2‖) 0) (μ.prod ν) := by
    have := integrable_toReal_of_lintegral_ne_top (by fun_prop) hlin
    simpa [ENNReal.toReal_ofReal'] using this
  have hG : Integrable (fun z : ℂ × ℂ => Real.log B + max (-Real.log ‖z.1 - z.2‖) 0)
      (μ.prod ν) := (integrable_const _).add hg
  have hc2 : Continuous fun z : ℂ × ℂ => ‖z.1 - conj z.2‖ :=
    (continuous_fst.sub (Complex.continuous_conj.comp continuous_snd)).norm
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · filter_upwards [hgood] with z hz
    exact ⟨hz.1, hz.1.trans_le hz.2.1⟩
  · refine hG.mono' (Real.measurable_log.comp
      (by fun_prop : Measurable fun z : ℂ × ℂ => ‖z.1 - z.2‖)).aestronglyMeasurable ?_
    filter_upwards [hgood] with z hz
    rw [Real.norm_eq_abs]
    exact gffEx_abs_log_le hz.1 le_rfl hz.2.2.1 hB1
  · refine hG.mono' (Real.measurable_log.comp hc2.measurable).aestronglyMeasurable ?_
    filter_upwards [hgood] with z hz
    rw [Real.norm_eq_abs]
    exact gffEx_abs_log_le hz.1 hz.2.1 hz.2.2.2 hB1

/-! ### Examples of admissible measures -/

theorem gffEx_admissible_zero : IsAdmissibleH 0 :=
  ⟨inferInstance, ⟨∅, isCompact_empty, empty_subset _, by simp⟩, 0, ENNReal.zero_lt_top,
    fun y => by simp⟩

theorem gffEx_admissible_smul {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    IsAdmissibleH (c • μ) := by
  obtain ⟨hfin, ⟨K, hK, hKH, hK0⟩, C, hC, hbd⟩ := hμ
  refine ⟨⟨?_⟩, ⟨K, hK, hKH, by simp [hK0]⟩, c * C, ENNReal.mul_lt_top hc.lt_top hC,
    fun y => ?_⟩
  · simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top μ _)
  · rw [lintegral_smul_measure]
    exact mul_le_mul' le_rfl (hbd y)

/-- The reference probability measure: uniform on the circle `∂B(2i, 1) ⊆ ℍ`. -/
abbrev gffExRef : Measure ℂ := LQGDimension.Coupling.circMeas (2 * Complex.I) 1

theorem gffEx_admissible_ref : IsAdmissibleH gffExRef := by
  have h2 : ‖(2 : ℂ) * Complex.I‖ = 2 := by simp
  refine ⟨inferInstance, ⟨Metric.sphere (2 * Complex.I) 1, isCompact_sphere _ _, ?_, ?_⟩,
    ENNReal.ofReal 14, ENNReal.ofReal_lt_top, fun y => ?_⟩
  · intro z hz
    rw [mem_sphere_iff_norm] at hz
    have := Complex.abs_im_le_norm (z - 2 * Complex.I)
    rw [hz] at this
    have e : (z - 2 * Complex.I).im = z.im - 2 := by simp
    rw [e, abs_le] at this
    show 0 ≤ z.im
    linarith [this.1]
  · have h := LQGDimension.Coupling.ae_circMeas (2 * Complex.I) 1
    rw [ae_iff] at h
    convert h using 2
    ext z
    simp [mem_sphere_iff_norm]
  · by_cases hy : ‖y‖ ≤ 4
    · have hi : Integrable (fun x => |Real.log ‖y - x‖|) gffExRef :=
        (LQGDimension.Coupling.integrable_log_norm_sub_circ y _ 1).abs
      have hb := LQGDimension.Coupling.integral_abs_log_le y (2 * Complex.I) one_pos
      calc ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂gffExRef
          ≤ ∫⁻ x, ENNReal.ofReal |Real.log ‖y - x‖| ∂gffExRef := by
            refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
            rw [norm_sub_rev]; exact neg_le_abs _
        _ = ENNReal.ofReal (∫ x, |Real.log ‖y - x‖| ∂gffExRef) :=
            (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => abs_nonneg _)).symm
        _ ≤ ENNReal.ofReal 14 := by
            refine ENNReal.ofReal_le_ofReal (hb.trans ?_)
            rw [h2, Real.log_one]; linarith
    · have : ∀ᵐ x ∂gffExRef, ENNReal.ofReal (-Real.log ‖x - y‖) = 0 := by
        filter_upwards [LQGDimension.Coupling.ae_circMeas (2 * Complex.I) 1] with x hx
        have hxn := LQGDimension.Coupling.norm_le_of_circ hx
        rw [h2, abs_one] at hxn
        have h1 : 1 ≤ ‖x - y‖ := by
          have := norm_sub_norm_le y x
          rw [norm_sub_rev] at this
          linarith
        rw [ENNReal.ofReal_eq_zero]
        linarith [Real.log_nonneg h1]
      rw [lintegral_congr_ae this, lintegral_zero]
      exact zero_le

end QuantumZipper.GFFExist
