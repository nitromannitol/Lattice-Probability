/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/BrownianPredictableMoments.lean, BouRabeeGwynne/BrownianPredictableTaylor.lean.
-/

import LatticeProb.Prob.BrownianFiniteStopping
import LatticeProb.Prob.BrownianHessianTaylor
import LatticeProb.Prob.BrownianIncrementMoments
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration

/-!
# Predictable Brownian increments and the predictable Taylor bound

A coefficient measurable at time `t` is independent of the path shifted by `t`, with the whole
past retained. Against the increment `ω (t + s) - ω t` it has the moments of a fresh Gaussian
increment, so its linear term has mean zero and a zero-trace quadratic term has mean zero.
These identities integrate a pointwise Taylor remainder with predictable coefficients.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- A random variable with centred Gaussian law of variance `v` is in `L²`. -/
private lemma memLp_two_of_hasLaw_centred_gaussian {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω'} {X : Ω' → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) :
    MemLp X 2 μ := by
  have h : MemLp id (2 : ℝ≥0∞) (gaussianReal 0 v) := memLp_id_gaussianReal' _ (by norm_num)
  rw [← hX.map_eq] at h
  exact (memLp_map_measure_iff aestronglyMeasurable_id hX.aemeasurable).mp h

/-- A coefficient measurable with respect to the natural filtration at time `t` is independent
of the Brownian path shifted by `t`. -/
lemma standardBrownianLaw_indepFun_shift_coefficient {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0)
    {C : BrownianPath d → ℝ} (hC : Measurable[brownianNaturalFiltration d t] C) :
    IndepFun (shiftedBrownianPath t) C μ := by
  have hpast : Measurable[MeasurableSpace.comap
      (fun (ω : BrownianPath d) (s : Set.Iic t) ↦ ω s) inferInstance] C := by
    exact (brownianNaturalFiltration_eq_comap d t) ▸ hC
  apply (IndepFun_iff _ _ _).mpr
  intro S A hS hA
  exact (standardBrownianLaw_indepFun_shiftedPath hμ t).meas_inter hS
    (hpast.comap_le A hA)

/-- A coefficient known at time t has zero expectation against the next
Brownian increment, with the whole past retained. -/
theorem standardBrownianLaw_integral_predictable_linear {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    {C : BrownianPath d → ℝ} (hC : Measurable[brownianNaturalFiltration d t] C)
    (i : Fin d) :
    (∫ ω, C ω * (ω (t + s) i - ω t i) ∂μ) = 0 := by
  have hmC : Measurable C := hC.mono ((brownianNaturalFiltration d).le t) le_rfl
  have hmeval : Measurable (fun ω : BrownianPath d ↦ ω s i) :=
    (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω s i)).measurable
  have hind := (standardBrownianLaw_indepFun_shift_coefficient hμ t hC).symm.comp
    measurable_id hmeval
  have hmean : (∫ ω, ω (t + s) i - ω t i ∂μ) = 0 :=
    ((hμ.2.1 i).shift t).integral_eval s
  exact (hind.integral_fun_mul_eq_mul_integral hmC.aestronglyMeasurable
    (hmeval.comp (measurable_shiftedBrownianPath t)).aestronglyMeasurable).trans
      (by
        change (∫ ω, C ω ∂μ) * (∫ ω, ω (t + s) i - ω t i ∂μ) = 0
        rw [hmean, mul_zero])

/-- The conditional covariance of the next actual increment is s times the
identity; the past coefficient may encode a stopping event and a Hessian entry. -/
theorem standardBrownianLaw_integral_predictable_quadratic {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    {C : BrownianPath d → ℝ} (hC : Measurable[brownianNaturalFiltration d t] C)
    (i j : Fin d) :
    (∫ ω, C ω * ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) ∂μ) =
      (∫ ω, C ω ∂μ) * (if i = j then (s : ℝ) else 0) := by
  have hmC : Measurable C := hC.mono ((brownianNaturalFiltration d).le t) le_rfl
  have hmquad : Measurable (fun ω : BrownianPath d ↦ ω s i * ω s j) :=
    (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω s i * ω s j)).measurable
  have hind := (standardBrownianLaw_indepFun_shift_coefficient hμ t hC).symm.comp
    measurable_id hmquad
  have hmoment : (∫ ω, (ω (t + s) i - ω t i) * (ω (t + s) j - ω t j) ∂μ) =
      if i = j then (s : ℝ) else 0 := by
    have hm := standardBrownianLaw_integral_coordinate_mul
      (standardBrownianLaw_shift hμ t) s i j
    rw [integral_map (measurable_shiftedBrownianPath t).aemeasurable
      hmquad.aestronglyMeasurable] at hm
    exact hm
  exact (hind.integral_fun_mul_eq_mul_integral hmC.aestronglyMeasurable
    (hmquad.comp (measurable_shiftedBrownianPath t)).aestronglyMeasurable).trans
      (by
        change (∫ ω, C ω ∂μ) *
          (∫ ω, (ω (t + s) i - ω t i) * (ω (t + s) j - ω t j) ∂μ) = _
        rw [hmoment])

/-- The full predictable quadratic term cancels when its actual coefficient
matrix has zero trace. Integrability of the coefficients is explicit. -/
theorem standardBrownianLaw_integral_predictable_trace_zero {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    (H : Fin d → Fin d → BrownianPath d → ℝ)
    (hH : ∀ i j, Measurable[brownianNaturalFiltration d t] (H i j))
    (hHint : ∀ i j, Integrable (H i j) μ)
    (htrace : ∀ ω, ∑ i, H i i ω = 0) :
    (∫ ω, ∑ i, ∑ j, H i j ω *
      ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) ∂μ) = 0 := by
  have hincrement (i j : Fin d) : Integrable (fun ω : BrownianPath d ↦
      (ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) μ := by
    have htwo (k : Fin d) :
        MemLp (fun ω : BrownianPath d ↦ ω (t + s) k - ω t k) 2 μ :=
      memLp_two_of_hasLaw_centred_gaussian ((hμ.2.1 k).hasLaw_sub (t + s) t)
    exact (htwo i).integrable_mul (htwo j)
  have hint (i j : Fin d) : Integrable (fun ω : BrownianPath d ↦ H i j ω *
      ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j))) μ := by
    have hmquad : Measurable (fun ω : BrownianPath d ↦ ω s i * ω s j) :=
      (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω s i * ω s j)).measurable
    have hind := (standardBrownianLaw_indepFun_shift_coefficient hμ t (hH i j)).symm.comp
      measurable_id hmquad
    exact hind.integrable_mul (hHint i j) (hincrement i j)
  calc
    _ = ∑ i, ∑ j, (∫ ω, H i j ω ∂μ) * (if i = j then (s : ℝ) else 0) := by
      rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hint i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ ↦ hint i j)]
      apply Finset.sum_congr rfl
      intro j _
      exact standardBrownianLaw_integral_predictable_quadratic hμ t s (hH i j) i j
    _ = (s : ℝ) * ∑ i, ∫ ω, H i i ω ∂μ := by simp [Finset.mul_sum, mul_comm]
    _ = (s : ℝ) * ∫ ω, ∑ i, H i i ω ∂μ := by
      rw [integral_finsetSum _ (fun i _ ↦ hHint i i)]
    _ = 0 := by simp only [htrace, integral_zero, mul_zero]

/-- Integrability of a predictable linear term, given that the coefficient is integrable. -/
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

/-- Integrability of a predictable quadratic term, given that the coefficient is integrable. -/
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
      memLp_two_of_hasLaw_centred_gaussian ((hμ.2.1 k).hasLaw_sub (t + s) t)
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
    {ε C : ℝ} (hC : 0 ≤ C)
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
  have hilin : Integrable lin μ := integrable_finsetSum _ (fun i _ ↦
    standardBrownianLaw_integrable_predictable_linear hμ t s (hL i) (hiL i) i)
  have hiquad : Integrable quad μ := integrable_finsetSum _ (fun i _ ↦
    integrable_finsetSum _ (fun j _ ↦
      standardBrownianLaw_integrable_predictable_quadratic hμ t s (hH i j) (hiH i j) i j))
  have hlinzero : (∫ ω, lin ω ∂μ) = 0 := by
    dsimp [lin]
    rw [integral_finsetSum _ (fun i _ ↦
      standardBrownianLaw_integrable_predictable_linear hμ t s (hL i) (hiL i) i)]
    apply Finset.sum_eq_zero
    intro i _
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

namespace BrownianPredictableTaylorExample

/-- For a deterministic coefficient `c`, the predictable linear moment vanishes under any
standard Brownian law `μ`, which is a binder. -/
theorem standardBrownianLaw_integral_constant_linear {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    (c : ℝ) (i : Fin d) :
    (∫ ω, c * (ω (t + s) i - ω t i) ∂μ) = 0 :=
  standardBrownianLaw_integral_predictable_linear hμ t s (C := fun _ ↦ c)
    measurable_const i

end BrownianPredictableTaylorExample

end LatticeProb
