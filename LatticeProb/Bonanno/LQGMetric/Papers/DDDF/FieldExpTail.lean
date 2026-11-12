/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.FieldExpTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# From tail bounds to exponential moments (task P2-DDDFFIELD)

The elementary bound used in DDDF (arXiv:1904.08021, `tightness.tex` l. 345–352, proof of
(2.17)) and DF (arXiv:1809.02607, l. 1860–1880, proof of Lemma 10.2):
`E e^{λX} ≤ e^{λx₀} + ∫_{x₀}^∞ λ e^{λt} P(X ≥ t) dt` (layer-cake formula, mathlib
`lintegral_comp_eq_lintegral_meas_le_mul`). `lintegral_exp_le_of_tail`: if moreover
`λ e^{λt} P(X ≥ t) ≤ B e^{−κt}` for `t > x₀`, then `E e^{λX} ≤ e^{λx₀} + B e^{−κx₀}/κ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Exponential moment from an exponential tail.** -/
theorem lintegral_exp_le_of_tail [IsProbabilityMeasure P] {X : Ω → ℝ} (hX0 : ∀ ω, 0 ≤ X ω)
    (hXm : AEMeasurable X P) {l x₀ B κ : ℝ} (hl : 0 < l) (hx₀ : 0 ≤ x₀) (hκ : 0 < κ)
    (hB : 0 ≤ B)
    (htail : ∀ t, x₀ < t → l * Real.exp (l * t) * P.real {ω | t ≤ X ω} ≤ B * Real.exp (-κ * t)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * X ω)) ∂P ≤
      ENNReal.ofReal (Real.exp (l * x₀) + B * Real.exp (-κ * x₀) / κ) := by
  set g : ℝ → ℝ := fun t => l * Real.exp (l * t) with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hftc : ∀ x : ℝ, ∫ t in (0 : ℝ)..x, g t = Real.exp (l * x) - 1 := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.exp (l * t))]
    · simp
    · intro t _
      have := ((hasDerivAt_id t).const_mul l).exp
      simpa [hg, mul_comm] using this
    · exact hgc.intervalIntegrable _ _
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (l * X ω)) =
      1 + ENNReal.ofReal (∫ t in (0 : ℝ)..X ω, g t) := by
    intro ω
    rw [hftc, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one]
    · congr 1; ring
    · have : 1 ≤ Real.exp (l * X ω) := Real.one_le_exp (by have := hX0 ω; positivity)
      linarith
  simp_rw [hpt]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_comp_eq_lintegral_meas_le_mul P (Eventually.of_forall hX0) hXm
      (fun t _ => hgc.intervalIntegrable _ _)
      (Eventually.of_forall fun t => by simp only [hg]; positivity)]
  have hgn : ∀ t, 0 ≤ g t := fun t => by simp only [hg]; positivity
  have hm1 : Measurable fun t => ENNReal.ofReal (g t) := hgc.measurable.ennreal_ofReal
  have hm2 : Measurable fun t : ℝ => ENNReal.ofReal (B * Real.exp (-κ * t)) := by fun_prop
  have hI1 : ∫⁻ t in Ioc 0 x₀, ENNReal.ofReal (g t) = ENNReal.ofReal (Real.exp (l * x₀) - 1) := by
    have hint : IntegrableOn g (Ioc 0 x₀) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx₀).1 (hgc.intervalIntegrable 0 x₀)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hgn),
      ← intervalIntegral.integral_of_le hx₀, hftc]
  have hI2 : ∫⁻ t in Ioi x₀, ENNReal.ofReal (B * Real.exp (-κ * t)) =
      ENNReal.ofReal (B * Real.exp (-κ * x₀) / κ) := by
    have hint : IntegrableOn (fun t => B * Real.exp (-κ * t)) (Ioi x₀) :=
      (integrableOn_exp_mul_Ioi (by linarith) x₀).const_mul B
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun t => by positivity), integral_const_mul,
      integral_exp_mul_Ioi (by linarith)]
    congr 1; field_simp
  have hsplit : ∫⁻ t in Ioi 0, P {ω | t ≤ X ω} * ENNReal.ofReal (g t) ≤
      (∫⁻ t in Ioc 0 x₀, ENNReal.ofReal (g t)) +
        ∫⁻ t in Ioi x₀, ENNReal.ofReal (B * Real.exp (-κ * t)) := by
    have ha : ∫⁻ t in Ioc 0 x₀, P {ω | t ≤ X ω} * ENNReal.ofReal (g t) ≤
        ∫⁻ t in Ioc 0 x₀, ENNReal.ofReal (g t) :=
      setLIntegral_mono hm1 fun t _ => mul_le_of_le_one_left (zero_le) prob_le_one
    have hb : ∫⁻ t in Ioi x₀, P {ω | t ≤ X ω} * ENNReal.ofReal (g t) ≤
        ∫⁻ t in Ioi x₀, ENNReal.ofReal (B * Real.exp (-κ * t)) := by
      refine setLIntegral_mono hm2 fun t ht => ?_
      rw [← ofReal_measureReal, ← ENNReal.ofReal_mul measureReal_nonneg]
      refine ENNReal.ofReal_le_ofReal ?_
      have := htail t ht
      simp only [hg]
      linarith [mul_comm (P.real {ω | t ≤ X ω}) (l * Real.exp (l * t))]
    rw [← Ioc_union_Ioi_eq_Ioi hx₀]
    exact (lintegral_union_le _ _ _).trans (add_le_add ha hb)
  have h1 : 0 ≤ Real.exp (l * x₀) - 1 := by
    have : 1 ≤ Real.exp (l * x₀) := Real.one_le_exp (by positivity)
    linarith
  have h2 : 0 ≤ B * Real.exp (-κ * x₀) / κ := by positivity
  calc 1 + ∫⁻ t in Ioi 0, P {ω | t ≤ X ω} * ENNReal.ofReal (g t)
      ≤ 1 + (ENNReal.ofReal (Real.exp (l * x₀) - 1) +
          ENNReal.ofReal (B * Real.exp (-κ * x₀) / κ)) := by
        rw [← hI1, ← hI2]; exact add_le_add le_rfl hsplit
    _ = ENNReal.ofReal (Real.exp (l * x₀) + B * Real.exp (-κ * x₀) / κ) := by
        rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (add_nonneg h1 h2)]
        congr 1; ring

/-- Real-valued form: `e^{λX}` is integrable and `E e^{λX} ≤ e^{λx₀} + B e^{−κx₀}/κ`. -/
theorem integral_exp_le_of_tail [IsProbabilityMeasure P] {X : Ω → ℝ} (hX0 : ∀ ω, 0 ≤ X ω)
    (hXm : AEMeasurable X P) {l x₀ B κ : ℝ} (hl : 0 < l) (hx₀ : 0 ≤ x₀) (hκ : 0 < κ)
    (hB : 0 ≤ B)
    (htail : ∀ t, x₀ < t → l * Real.exp (l * t) * P.real {ω | t ≤ X ω} ≤ B * Real.exp (-κ * t)) :
    Integrable (fun ω => Real.exp (l * X ω)) P ∧
      ∫ ω, Real.exp (l * X ω) ∂P ≤ Real.exp (l * x₀) + B * Real.exp (-κ * x₀) / κ := by
  have h := lintegral_exp_le_of_tail hX0 hXm hl hx₀ hκ hB htail
  have hm : AEStronglyMeasurable (fun ω => Real.exp (l * X ω)) P :=
    (Real.measurable_exp.comp_aemeasurable (hXm.const_mul l)).aestronglyMeasurable
  have hfin : ∫⁻ ω, ENNReal.ofReal (Real.exp (l * X ω)) ∂P < ⊤ :=
    h.trans_lt ENNReal.ofReal_lt_top
  have hint : Integrable (fun ω => Real.exp (l * X ω)) P := by
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    exact hfin
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => (Real.exp_pos _).le) hm]
  have h0 : 0 ≤ Real.exp (l * x₀) + B * Real.exp (-κ * x₀) / κ := by positivity
  exact (ENNReal.toReal_le_of_le_ofReal h0 h)

end DDDF
end LQGMetric
