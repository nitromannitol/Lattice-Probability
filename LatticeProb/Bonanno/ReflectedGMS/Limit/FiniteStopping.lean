/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.FiniteStopping at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
Optional stopping at finitely valued stopping times on actual nonnegative-real
time. Mathlib already supplies the stronger bounded countable-range conditional-
expectation identity, so no finite-atom decomposition is reimplemented. The
second-moment estimate reuses its conditional-expectation contraction inequality.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Finite-valued optional stopping: the stopped expectation equals the terminal
expectation. The finite deterministic upper bound excludes the `WithTop` value
infinity; no path continuity or completed filtration is required. -/
theorem finite_stopping_integral_eq_terminal
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hfin : (Set.range τ).Finite)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    (∫ ω, stoppedValue M τ ω ∂P) = ∫ ω, M T ω ∂P := by
  have he := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτT hfin.countable
  exact (integral_congr_ae he).trans (integral_condExp hτ.measurableSpace_le)

/-- Terminal L² integrability alone suffices at a bounded finite-valued stopping
time, by its existing conditional-expectation representation. -/
theorem finite_stopping_memLp_two
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hfin : (Set.range τ).Finite)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) (h2T : MemLp (M T) 2 P) :
    MemLp (stoppedValue M τ) 2 P := by
  have he := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτT hfin.countable
  exact (memLp_congr_ae he).2 (h2T.condExp one_le_two)

/-- Finite-valued optional stopping for second moments. No square-integrability
at every time is added: the terminal second moment controls the stopped one. -/
theorem finite_stopping_second_moment_le
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hfin : (Set.range τ).Finite)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) (h2T : MemLp (M T) 2 P) :
    (∫ ω, (stoppedValue M τ ω) ^ 2 ∂P) ≤ ∫ ω, (M T ω) ^ 2 ∂P := by
  have he := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτT hfin.countable
  calc
    _ = ∫ ω, (P[M T | hτ.measurableSpace] ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [he] with ω hω using congrArg (fun x : ℝ => x ^ 2) hω
    _ ≤ _ := by
      have hint : Integrable (fun ω => ‖M T ω‖ ^ (2 : ℝ)) P := by
        simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using h2T.integrable_sq
      have h := integral_norm_condExp_rpow_le (m := hτ.measurableSpace)
        (show (1 : ℝ) ≤ 2 from one_le_two) hint
      simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

end ReflectedGMS.MartingaleLimit
