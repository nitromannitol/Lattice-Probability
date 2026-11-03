/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentPos2Fin at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2Cell
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMass
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist

/-!
# DZZ Lemma 2.10, positive moments: `E μ(𝕍)^q < ∞` for `1 < q < 4/γ²` (P2-KAHANE3)

* `uniform_moment_areaApprox_sqIn` : `sup_{k ≥ k₀(s)} E areaApprox_k(sqIn s)^q ≤ C`, `C` independent
  of `s`;
* `lintegral_qAreaMeasureOn_rpow_lt_top_of_one_lt` : `E μ_h(𝕍)^q < ∞` for the LQG measure of the
  zero-boundary GFF on `𝕍` and `1 < q < 4/γ²` (DZZ Lemma 2.10, positive moments; Kahane 1985,
  Rhodes–Vargas arXiv:1305.6221 Thm 2.11, Berestycki–Powell arXiv:2404.16642 Thm 3.23).

Route: `areaApprox_k(sqIn s) ≤ ∫_{t ∈ [0,1)²} W_t` with `W_t` the Riemann sum at offset `t`
(`setLIntegral_sqIn_le`); Jensen in `t`; for each `t`, `W_t` is a.s. the circle-average sum `oM`
(`avgReg_ae_eq`), whose `q`-th moment is bounded uniformly (`exists_uniform_moment_oM`); finally
the Fatou passage `lintegral_qAreaMeasureOn_rpow_le_of_sqIn`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

lemma volume_cell0 : volume cell0 = 1 := by
  have h := Complex.volume_preserving_equiv_real_prod
  have e : cell0 = Complex.measurableEquivRealProd ⁻¹' (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) := by
    ext z
    simp [cell0, Complex.measurableEquivRealProd, Complex.equivRealProd, and_assoc]
  rw [e, h.measure_preimage (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico]
  simp

instance : IsProbabilityMeasure (volume.restrict cell0) :=
  ⟨by rw [Measure.restrict_apply_univ, volume_cell0]⟩

/-- Jensen for `x ↦ x^q` (`q > 1`) under a probability measure, in `ℝ≥0∞` -/
lemma rpow_lintegral_le {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) {q : ℝ} (hq : 1 < q) :
    (∫⁻ a, g a ∂ν) ^ q ≤ ∫⁻ a, g a ^ q ∂ν := by
  have hpq := Real.HolderConjugate.conjExponent hq
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hg aemeasurable_const (g := fun _ => 1)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at h
  calc (∫⁻ a, g a ∂ν) ^ q ≤ ((∫⁻ a, g a ^ q ∂ν) ^ (1 / q)) ^ q :=
        ENNReal.rpow_le_rpow h (by linarith)
    _ = ∫⁻ a, g a ^ q ∂ν := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by linarith),
          ENNReal.rpow_one]

/-- the offset of the evaluation point inside the cell -/
def vOff (j : ℕ) (t : ℂ) : ℂ := ((2 : ℝ)⁻¹ ^ j : ℝ) • (t - ⟨1 / 2, 1 / 2⟩)

lemma cellMap_eq (j : ℕ) (i : ℕ × ℕ) (t : ℂ) : cellMap j i t = cpt j i + vOff j t := by
  apply Complex.ext
  · simp only [cellMap, cpt, vOff, Complex.smul_re, Complex.add_re, Complex.sub_re, smul_eq_mul,
      inv_pow]
    field_simp
    ring
  · simp only [cellMap, cpt, vOff, Complex.smul_im, Complex.add_im, Complex.sub_im, smul_eq_mul,
      inv_pow]
    field_simp
    ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

end DGMC

open DGMC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

end LQGMetric
