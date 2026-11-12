/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoiseL4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# DDDF Lemma 4 for `φ_δ` (task P2-WN; blueprint DDDF.L4, the `φ` half)

DDDF (arXiv:1904.08021, `tightness.tex` l. 380–395, Lemma 4 = `lem:FieldScale`):
`Var(φ_δ(x) − φ_δ(x')) ≤ C|x − x'|/δ`. We follow the paper's proof: the variance is
`∫_{δ²}^1 t⁻¹(1 − e^{−|x−x'|²/(2t)}) dt`, then `1 − e^{−z} ≤ √z` (`z ≤ 1`: `1 − e^{−z} ≤ z ≤ √z`;
`z ≥ 1`: `1 − e^{−z} ≤ 1 ≤ √z`) and `∫_{δ²}^1 t^{−3/2} dt ≤ 2/δ`. Explicit constant `C = √2`.
The `ψ_δ` half of Lemma 4 belongs to DDDF.D2.psi (WP-95).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `1 − e^{−z} ≤ √z` for `z ≥ 0` (DDDF l. 391). -/
lemma one_sub_exp_neg_le_sqrt {z : ℝ} (hz : 0 ≤ z) : 1 - Real.exp (-z) ≤ Real.sqrt z := by
  have he := Real.add_one_le_exp (-z)
  rcases le_total z 1 with h | h
  · have hs := Real.sq_sqrt hz
    have hs1 : Real.sqrt z ≤ 1 := Real.sqrt_le_one.mpr h
    have hs0 := Real.sqrt_nonneg z
    nlinarith
  · have : 1 ≤ Real.sqrt z := Real.one_le_sqrt.mpr h
    have := Real.exp_pos (-z)
    linarith

/-- `∫_{δ²}^1 t⁻¹ (√t)⁻¹ dt = 2/δ − 2`. -/
lemma integral_inv_mul_inv_sqrt {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ t in δ ^ 2..1, t⁻¹ * (Real.sqrt t)⁻¹ = 2 / δ - 2 := by
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  have hpos : ∀ t ∈ uIcc (δ ^ 2) 1, 0 < t := fun t ht => by
    rw [uIcc_of_le hδ2] at ht; exact lt_of_lt_of_le (by positivity) ht.1
  have hderiv : ∀ t ∈ uIcc (δ ^ 2) 1,
      HasDerivAt (fun t => -2 * (Real.sqrt t)⁻¹) (t⁻¹ * (Real.sqrt t)⁻¹) t := by
    intro t ht
    have ht0 := hpos t ht
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have h := ((Real.hasDerivAt_sqrt ht0.ne').inv hs0.ne').const_mul (-2)
    have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
    have e : t⁻¹ * (Real.sqrt t)⁻¹ = -2 * (-(1 / (2 * Real.sqrt t)) / Real.sqrt t ^ 2) := by
      rw [hst]; field_simp
    rw [e]; exact h
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹ * (Real.sqrt t)⁻¹) (uIcc (δ ^ 2) 1) := by
    refine ContinuousOn.mul (continuousOn_inv₀.mono fun t ht => (hpos t ht).ne') ?_
    exact (Real.continuous_sqrt.continuousOn).inv₀ fun t ht => (Real.sqrt_pos.mpr (hpos t ht)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  rw [Real.sqrt_one, Real.sqrt_sq hδ.le]
  field_simp
  ring

/-- **DDDF Lemma 4 (φ part)**: `Var(φ_δ(x) − φ_δ(x')) ≤ √2 |x − x'| / δ` for `δ ∈ (0, 1]`. -/
theorem variance_phi_sub_le (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x x' : ℂ) :
    Var[fun ω => phi W δ 1 x ω - phi W δ 1 x' ω; P] ≤ Real.sqrt 2 * ‖x - x'‖ / δ := by
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  rw [(hasLaw_phi_sub hW hδ 1 x x').variance_eq, variance_id_gaussianReal, Real.coe_toNNReal']
  refine max_le ?_ (by positivity)
  set r := ‖x - x'‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hpos : ∀ t ∈ Icc (δ ^ 2) ((1 : ℝ) ^ 2), 0 < t := fun t ht =>
    lt_of_lt_of_le (by positivity) ht.1
  have hle : ∀ t ∈ Icc (δ ^ 2) ((1 : ℝ) ^ 2),
      t⁻¹ * (1 - Real.exp (-r ^ 2 / (2 * t))) ≤ r / Real.sqrt 2 * (t⁻¹ * (Real.sqrt t)⁻¹) := by
    intro t ht
    have ht0 := hpos t ht
    have hz : 0 ≤ r ^ 2 / (2 * t) := by positivity
    have h1 := one_sub_exp_neg_le_sqrt hz
    rw [neg_div]
    have hsq : Real.sqrt (r ^ 2 / (2 * t)) = r / Real.sqrt 2 * (Real.sqrt t)⁻¹ := by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr0,
        Real.sqrt_mul (by norm_num)]
      field_simp
    calc t⁻¹ * (1 - Real.exp (-(r ^ 2 / (2 * t))))
        ≤ t⁻¹ * Real.sqrt (r ^ 2 / (2 * t)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr ht0.le)
      _ = r / Real.sqrt 2 * (t⁻¹ * (Real.sqrt t)⁻¹) := by rw [hsq]; ring
  have hint2 : IntegrableOn (fun t : ℝ => r / Real.sqrt 2 * (t⁻¹ * (Real.sqrt t)⁻¹))
      (Icc (δ ^ 2) ((1 : ℝ) ^ 2)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine continuousOn_const.mul (ContinuousOn.mul
      (continuousOn_inv₀.mono fun t ht => (hpos t ht).ne') ?_)
    exact (Real.continuous_sqrt.continuousOn).inv₀ fun t ht => (Real.sqrt_pos.mpr (hpos t ht)).ne'
  have hint1 : IntegrableOn (fun t : ℝ => t⁻¹ * (1 - Real.exp (-r ^ 2 / (2 * t))))
      (Icc (δ ^ 2) ((1 : ℝ) ^ 2)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine ContinuousOn.mul (continuousOn_inv₀.mono fun t ht => (hpos t ht).ne') ?_
    refine continuousOn_const.sub (Real.continuous_exp.comp_continuousOn ?_)
    exact continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht =>
      (mul_pos two_pos (hpos t ht)).ne'
  refine (setIntegral_mono_on hint1 hint2 measurableSet_Icc hle).trans ?_
  rw [integral_const_mul, integral_Icc_eq_integral_Ioc, one_pow,
    ← intervalIntegral.integral_of_le hδ2, integral_inv_mul_inv_sqrt hδ hδ1]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2p : 0 < Real.sqrt 2 := by positivity
  have hr : 0 ≤ r := norm_nonneg _
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hs2p hδ]
  have e1 : r * (2 / δ - 2) * δ = 2 * r - 2 * (r * δ) := by field_simp
  have e2 : Real.sqrt 2 * r * Real.sqrt 2 = 2 * r := by rw [mul_comm _ r, mul_assoc, hs2]; ring
  rw [e1, e2]
  nlinarith [mul_nonneg hr hδ.le]

end WhiteNoise
end LQGMetric
