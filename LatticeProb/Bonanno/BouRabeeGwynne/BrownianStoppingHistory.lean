/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianStoppingHistory at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStrongMarkov
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianPathFreezing

/-!
# The complete observed history and the genuine Brownian future

The strong Markov theorem gives the joint law for any history measurable at
the actual stopping time. This retains the entire preceding excursion prefix
when constructing the successive ball-excursion law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

lemma measurable_brownianPosition_stopping {d : ℕ}
    {τ : BrownianPath d → ℝ≥0∞}
    (hτ : IsStoppingTime (brownianNaturalFiltration d) τ) (z : Euc d) :
    Measurable[hτ.measurableSpace] (fun ω ↦ z + ω (τ ω).toNNReal) := by
  have heval : Measurable (fun p : BrownianPath d × ℝ≥0 ↦ p.1 p.2) := by fun_prop
  have hm := heval.comp ((measurable_frozenBrownianPath_stopping hτ).prodMk
    (ENNReal.measurable_toNNReal.comp hτ.measurable))
  simpa only [Function.comp_def, frozenBrownianPath_apply, min_self, Pi.add_def] using
    measurable_const.add hm

/-- The observed history and future increment path have their actual product
law at an almost surely finite stopping time. -/
theorem standardBrownianLaw_stopping_history_joint {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {τ : BrownianPath d → ℝ≥0∞}
    (hτ : IsStoppingTime (brownianNaturalFiltration d) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ∞)
    {H : Type*} [MeasurableSpace H] {history : BrownianPath d → H}
    (hhistory : Measurable[hτ.measurableSpace] history) :
    μ.map (fun ω ↦ (history ω, shiftedBrownianPath (τ ω).toNNReal ω)) =
      (μ.map history).prod μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hmH : Measurable history := hhistory.mono hτ.measurableSpace_le le_rfl
  have hmF : Measurable (fun ω ↦ shiftedBrownianPath (τ ω).toNNReal ω) :=
    measurable_variable_shiftedBrownianPath (ENNReal.measurable_toNNReal.comp hτ.measurable')
  apply Measure.ext_prod
  intro S T hS hT
  have h := congrArg (fun ρ : Measure (BrownianPath d) ↦ ρ T)
    (standardBrownianLaw_aeFiniteStopping_map_restrict hμ hτ hfinite (hhistory hS))
  rw [Measure.map_apply hmF hT, Measure.restrict_apply (hmF hT),
    Measure.smul_apply, smul_eq_mul] at h
  rw [Measure.map_apply (hmH.prodMk hmF) (hS.prod hT), Measure.prod_prod,
    Measure.map_apply hmH hS]
  change μ (history ⁻¹' S ∩ (fun ω ↦ shiftedBrownianPath (τ ω).toNNReal ω) ⁻¹' T) = _
  rw [inter_comm]
  exact h

end BouRabeeGwynne
