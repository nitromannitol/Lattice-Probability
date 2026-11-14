/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianPredictableTaylor at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianPredictableMoments
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianTaylorBound

/-!
# Taylor expectation bounds with coefficients from the actual Brownian past

This is the stopped one-step integration argument. A stopping indicator and a
random current position may enter the gradient and Hessian coefficients. The
full natural-filtration independence proves cancellation of their linear and
zero-trace quadratic terms.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace BouRabeeGwynne

lemma standardBrownianLaw_integrable_predictable_linear {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    {C : BrownianPath d → ℝ} (hC : Measurable[brownianNaturalFiltration d t] C)
    (hiC : Integrable C μ) (i : Fin d) :
    Integrable (fun ω ↦ C ω * (ω (t + s) i - ω t i)) μ := by
  have hm : Measurable (fun ω : BrownianPath d ↦ ω s i) :=
    (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω s i)).measurable
  have hind := (standardBrownianLaw_indepFun_shift_coefficient hμ t hC).symm.comp
    measurable_id hm
  exact hind.integrable_mul hiC (((hμ.2.1 i).shift t).integrable_eval s)

lemma standardBrownianLaw_integrable_predictable_quadratic {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    {C : BrownianPath d → ℝ} (hC : Measurable[brownianNaturalFiltration d t] C)
    (hiC : Integrable C μ) (i j : Fin d) :
    Integrable (fun ω ↦ C ω *
      ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j))) μ := by
  have hm : Measurable (fun ω : BrownianPath d ↦ ω s i * ω s j) :=
    (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω s i * ω s j)).measurable
  have hind := (standardBrownianLaw_indepFun_shift_coefficient hμ t hC).symm.comp
    measurable_id hm
  have hi : Integrable (fun ω : BrownianPath d ↦
      (ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) μ := by
    have htwo (k : Fin d) :
        MemLp (fun ω : BrownianPath d ↦ ω (t + s) k - ω t k) 2 μ :=
      ((hμ.2.1 k).hasLaw_sub (t + s) t).memLp (memLp_id_gaussianReal' 2 (by norm_num))
    exact (htwo i).integrable_mul (htwo j)
  exact hind.integrable_mul hiC hi

/-- Integrating an actual Taylor remainder with predictable coefficients.
The input is a pointwise analytic remainder bound; no conditional moment or
process-convergence statement is assumed. -/
theorem standardBrownianLaw_predictable_taylor_bound {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    (L : Fin d → BrownianPath d → ℝ) (H : Fin d → Fin d → BrownianPath d → ℝ)
    (hL : ∀ i, Measurable[brownianNaturalFiltration d t] (L i))
    (hH : ∀ i j, Measurable[brownianNaturalFiltration d t] (H i j))
    (hiL : ∀ i, Integrable (L i) μ) (hiH : ∀ i j, Integrable (H i j) μ)
    (htrace : ∀ ω, ∑ i, H i i ω = 0)
    {F : BrownianPath d → ℝ} (hmF : AEStronglyMeasurable F μ)
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hR : ∀ ω,
      |F ω - (∑ i, L i ω * (ω (t + s) i - ω t i)) - (1 / 2 : ℝ) *
        (∑ i, ∑ j, H i j ω *
          ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)))| ≤
        ε * ‖ω (t + s) - ω t‖ ^ 2 + C * ‖ω (t + s) - ω t‖ ^ 4) :
    Integrable F μ ∧ |∫ ω, F ω ∂μ| ≤
      ε * (d : ℝ) * (s : ℝ) + C * (3 * (d : ℝ) ^ 2 * (s : ℝ) ^ 2) := by
  let lin : BrownianPath d → ℝ := fun ω ↦ ∑ i, L i ω * (ω (t + s) i - ω t i)
  let quad : BrownianPath d → ℝ := fun ω ↦ ∑ i, ∑ j, H i j ω *
    ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j))
  have hilin : Integrable lin μ := integrable_finset_sum _ (fun i _ ↦
    standardBrownianLaw_integrable_predictable_linear hμ t s (hL i) (hiL i) i)
  have hiquad : Integrable quad μ := integrable_finset_sum _ (fun i _ ↦
    integrable_finset_sum _ (fun j _ ↦
      standardBrownianLaw_integrable_predictable_quadratic hμ t s (hH i j) (hiH i j) i j))
  have hlinzero : (∫ ω, lin ω ∂μ) = 0 := by
    dsimp [lin]
    rw [integral_finset_sum _ (fun i _ ↦
      standardBrownianLaw_integrable_predictable_linear hμ t s (hL i) (hiL i) i)]
    apply Finset.sum_eq_zero
    intro i hi
    exact standardBrownianLaw_integral_predictable_linear hμ t s (hL i) i
  have hquadzero : (∫ ω, quad ω ∂μ) = 0 :=
    standardBrownianLaw_integral_predictable_trace_zero hμ t s H hH hiH htrace
  have hsq := (standardBrownianLaw_integrable_norm_sq (standardBrownianLaw_shift hμ t) s).comp_measurable
    (measurable_shiftedBrownianPath t)
  have hfour := (standardBrownianLaw_integrable_norm_fourth (standardBrownianLaw_shift hμ t) s).comp_measurable
    (measurable_shiftedBrownianPath t)
  change Integrable (fun ω ↦ ‖ω (t + s) - ω t‖ ^ 2) μ at hsq
  change Integrable (fun ω ↦ ‖ω (t + s) - ω t‖ ^ 4) μ at hfour
  have hm2 : AEStronglyMeasurable (fun ω : BrownianPath d ↦ ‖ω s‖ ^ 2)
      (μ.map (shiftedBrownianPath t)) :=
    ((continuous_eval_const s).norm.pow 2).aestronglyMeasurable
  have hm4 : AEStronglyMeasurable (fun ω : BrownianPath d ↦ ‖ω s‖ ^ 4)
      (μ.map (shiftedBrownianPath t)) :=
    ((continuous_eval_const s).norm.pow 4).aestronglyMeasurable
  have hmeansq : (∫ ω, ‖ω (t + s) - ω t‖ ^ 2 ∂μ) = (d : ℝ) * (s : ℝ) := by
    have h := standardBrownianLaw_integral_norm_sq (standardBrownianLaw_shift hμ t) s
    rw [integral_map (measurable_shiftedBrownianPath t).aemeasurable hm2] at h
    exact h
  have hmeanfour : (∫ ω, ‖ω (t + s) - ω t‖ ^ 4 ∂μ) ≤
      3 * (d : ℝ) ^ 2 * (s : ℝ) ^ 2 := by
    have h := standardBrownianLaw_integral_norm_fourth_le (standardBrownianLaw_shift hμ t) s
    rw [integral_map (measurable_shiftedBrownianPath t).aemeasurable hm4] at h
    exact h
  let R : BrownianPath d → ℝ := fun ω ↦ F ω - lin ω - (1 / 2 : ℝ) * quad ω
  have hibound : Integrable (fun ω ↦
      ε * ‖ω (t + s) - ω t‖ ^ 2 + C * ‖ω (t + s) - ω t‖ ^ 4) μ :=
    (hsq.const_mul ε).add (hfour.const_mul C)
  have hmR : AEStronglyMeasurable R μ :=
    (hmF.sub hilin.aestronglyMeasurable).sub (hiquad.const_mul (1 / 2 : ℝ)).aestronglyMeasurable
  have hiboundR : ∀ ω, ‖R ω‖ ≤
      ε * ‖ω (t + s) - ω t‖ ^ 2 + C * ‖ω (t + s) - ω t‖ ^ 4 := hR
  have hiR : Integrable R μ := hibound.mono' hmR (Filter.Eventually.of_forall hiboundR)
  have hiF : Integrable F μ := by
    have h := (hiR.add hilin).add (hiquad.const_mul (1 / 2 : ℝ))
    exact h.congr (Filter.Eventually.of_forall (fun ω ↦ by dsimp [R]; ring))
  refine ⟨hiF, ?_⟩
  have hmean : (∫ ω, R ω ∂μ) = ∫ ω, F ω ∂μ := by
    have hsub : (∫ ω, F ω - lin ω ∂μ) = ∫ ω, F ω ∂μ := by
      calc
        _ = (∫ ω, F ω ∂μ) - (∫ ω, lin ω ∂μ) := integral_sub hiF hilin
        _ = _ := by rw [hlinzero, sub_zero]
    calc
      _ = (∫ ω, F ω - lin ω ∂μ) - (∫ ω, (1 / 2 : ℝ) * quad ω ∂μ) :=
        integral_sub (hiF.sub hilin) (hiquad.const_mul (1 / 2 : ℝ))
      _ = _ := by rw [hsub, integral_const_mul, hquadzero, mul_zero, sub_zero]
  rw [← hmean, ← Real.norm_eq_abs]
  calc
    ‖∫ ω, R ω ∂μ‖ ≤ ∫ ω,
        ε * ‖ω (t + s) - ω t‖ ^ 2 + C * ‖ω (t + s) - ω t‖ ^ 4 ∂μ :=
      norm_integral_le_of_norm_le hibound (Filter.Eventually.of_forall hiboundR)
    _ = ε * ((d : ℝ) * (s : ℝ)) + C * (∫ ω, ‖ω (t + s) - ω t‖ ^ 4 ∂μ) := by
      rw [integral_add (hsq.const_mul ε) (hfour.const_mul C),
        integral_const_mul, integral_const_mul, hmeansq]
    _ ≤ _ := add_le_add (le_of_eq (by ring)) (mul_le_mul_of_nonneg_left hmeanfour hC)

end BouRabeeGwynne
