import LatticeProb.Prob.BrownianDirichlet.Trace
import LatticeProb.Analysis.HessianTaylorRemainder
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Compensated predictable Taylor errors

Compactly supported twice continuously differentiable functions have uniformly small
compensated Brownian increments, with generator equal to half the scaled Laplacian.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Laplacian Set
open scoped NNReal ENNReal

namespace LatticeProb

/-- Integrate a predictable Taylor remainder while retaining the Hessian trace. -/
private theorem predictable_compensated_taylor_bound {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    (L : Fin d → BrownianPath d → ℝ) (H : Fin d → Fin d → BrownianPath d → ℝ)
    (hL : ∀ i, Measurable[brownianNaturalFiltration d t] (L i))
    (hH : ∀ i j, Measurable[brownianNaturalFiltration d t] (H i j))
    (hiL : ∀ i, Integrable (L i) μ) (hiH : ∀ i j, Integrable (H i j) μ)
    {F : BrownianPath d → ℝ} (hmF : AEStronglyMeasurable F μ)
    {ε C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ ω,
      |F ω - (∑ i, L i ω * (ω (t + s) i - ω t i)) - (1 / 2 : ℝ) *
        (∑ i, ∑ j, H i j ω *
          ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)))| ≤
        ε * ‖ω (t + s) - ω t‖ ^ 2 + C * ‖ω (t + s) - ω t‖ ^ 4) :
    Integrable F μ ∧ |(∫ ω, F ω ∂μ) -
      (1 / 2 : ℝ) * (s : ℝ) * (∫ ω, ∑ i, H i i ω ∂μ)| ≤
      ε * (d : ℝ) * (s : ℝ) + C * (3 * (d : ℝ) ^ 2 * (s : ℝ) ^ 2) := by
  let lin : BrownianPath d → ℝ := fun ω ↦ ∑ i, L i ω * (ω (t + s) i - ω t i)
  let quad : BrownianPath d → ℝ := fun ω ↦ ∑ i, ∑ j, H i j ω *
    ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j))
  have hilin : Integrable lin μ := integrable_finsetSum _ (fun i _ ↦
    standardBrownianLaw_integrable_predictable_linear hμ t s (hL i) (hiL i) i)
  have hiquad : Integrable quad μ := integrable_finsetSum _ (fun i _ ↦
    integrable_finsetSum _ (fun j _ ↦
      standardBrownianLaw_integrable_predictable_quadratic hμ t s (hH i j) (hiH i j) i j))
  have hlinzero : (∫ ω, lin ω ∂μ) = 0 :=
    standardBrownianLaw_integral_predictable_linear_sum hμ t s L hL hiL
  have hquadmean : (∫ ω, quad ω ∂μ) =
      (s : ℝ) * ∫ ω, ∑ i, H i i ω ∂μ :=
    standardBrownianLaw_integral_predictable_hessian hμ t s H hH hiH
  have hsq :=
    (standardBrownianLaw_integrable_norm_sq (standardBrownianLaw_shift hμ t) s).comp_measurable
      (measurable_shiftedBrownianPath t)
  have hfour :=
    (standardBrownianLaw_integrable_norm_fourth
      (standardBrownianLaw_shift hμ t) s).comp_measurable (measurable_shiftedBrownianPath t)
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
  have hmean : (∫ ω, R ω ∂μ) = (∫ ω, F ω ∂μ) -
      (1 / 2 : ℝ) * (s : ℝ) * (∫ ω, ∑ i, H i i ω ∂μ) := by
    have hsub : (∫ ω, F ω - lin ω ∂μ) = ∫ ω, F ω ∂μ := by
      calc
        _ = (∫ ω, F ω ∂μ) - (∫ ω, lin ω ∂μ) := integral_sub hiF hilin
        _ = _ := by rw [hlinzero, sub_zero]
    calc
      _ = (∫ ω, F ω - lin ω ∂μ) - (∫ ω, (1 / 2 : ℝ) * quad ω ∂μ) :=
        integral_sub (hiF.sub hilin) (hiquad.const_mul (1 / 2 : ℝ))
      _ = _ := by rw [hsub, integral_const_mul, hquadmean]; ring
  rw [← hmean, ← Real.norm_eq_abs]
  calc
    ‖∫ ω, R ω ∂μ‖ ≤ ∫ ω,
        ε * ‖ω (t + s) - ω t‖ ^ 2 + C * ‖ω (t + s) - ω t‖ ^ 4 ∂μ :=
      norm_integral_le_of_norm_le hibound (Filter.Eventually.of_forall hiboundR)
    _ = ε * ((d : ℝ) * (s : ℝ)) + C * (∫ ω, ‖ω (t + s) - ω t‖ ^ 4 ∂μ) := by
      rw [integral_add (hsq.const_mul ε) (hfour.const_mul C),
        integral_const_mul, integral_const_mul, hmeansq]
    _ ≤ _ := add_le_add (le_of_eq (by ring)) (mul_le_mul_of_nonneg_left hmeanfour hC)

/-- Compactly supported continuous observables are integrable under finite laws. -/
private lemma integrable_continuous_comp_of_compactSupport
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : E → ℝ} (hf : Continuous f) (hsupp : HasCompactSupport f)
    {X : Ω → E} (hX : Measurable X) : Integrable (fun ω ↦ f (X ω)) μ := by
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hf
  exact (integrable_const M).mono' (hf.measurable.comp hX).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω ↦ hM (X ω)))

/-- The coordinate Taylor remainder after scalar scaling preserves Euclidean norms. -/
private lemma scaled_coordinate_taylor_remainder {d : ℕ} {f : Euc d → ℝ}
    {σ η C : ℝ} (hσ : 0 < σ)
    (hR : ∀ x y, |f (x + y) - f x - fderiv ℝ f x y - (1 / 2 : ℝ) *
      fderiv ℝ (fderiv ℝ f) x y y| ≤ η * ‖y‖ ^ 2 + C * ‖y‖ ^ 4)
    (x z : Euc d) :
    let b := EuclideanSpace.basisFun (Fin d) ℝ
    |f (x + σ • z) - f x - (∑ i, σ * fderiv ℝ f x (b i) * z i) -
      (1 / 2 : ℝ) * (∑ i, ∑ j, σ ^ 2 *
        fderiv ℝ (fderiv ℝ f) x (b i) (b j) * (z i * z j))| ≤
      (η * σ ^ 2) * ‖z‖ ^ 2 + (C * σ ^ 4) * ‖z‖ ^ 4 := by
  classical
  dsimp only
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hlin : ∑ i, fderiv ℝ f (x) (b i) * (z i) =
      fderiv ℝ f (x) (z) := by
    rw [continuousLinearMap_eq_sum_euclidean_coordinates]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  have hquad : ∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) (x) (b i) (b j) *
      ((z i) * (z j)) =
        fderiv ℝ (fderiv ℝ f) (x) (z) (z) :=
    (bilinear_eq_sum_euclidean_coordinates (bilinearIteratedFDerivTwo ℝ f (x))
      (z) (z)).symm
  have hl : (∑ i, σ * fderiv ℝ f (x) (b i) *
      (z i)) =
      σ * fderiv ℝ f (x) (z) := by
    rw [← hlin, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hq : (∑ i, ∑ j, σ ^ 2 *
      fderiv ℝ (fderiv ℝ f) (x) (b i) (b j) *
      ((z i) * (z j))) =
      σ ^ 2 * fderiv ℝ (fderiv ℝ f) (x)
        (z) (z) := by
    rw [← hquad]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hl, hq]
  have hr := hR (x) (σ • (z))
  simp only [map_smul, smul_apply, smul_eq_mul,
    norm_smul, Real.norm_of_nonneg hσ.le, mul_pow] at hr
  convert hr using 1
  · apply congrArg abs
    ring
  · ring

/-- First and second coordinate derivatives of a compactly supported C² function
are continuous and compactly supported. -/
private lemma compactSupport_derivative_entries {d : ℕ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f) :
    let b := EuclideanSpace.basisFun (Fin d) ℝ
    (∀ i, Continuous (fun x ↦ fderiv ℝ f x (b i))) ∧
    (∀ i j, Continuous (fun x ↦ fderiv ℝ (fderiv ℝ f) x (b i) (b j))) ∧
    (∀ i, HasCompactSupport (fun x ↦ fderiv ℝ f x (b i))) ∧
    (∀ i j, HasCompactSupport (fun x ↦ fderiv ℝ (fderiv ℝ f) x (b i) (b j))) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDcont : Continuous (fderiv ℝ f) := hDf.continuous
  have hHcont : Continuous (fderiv ℝ (fderiv ℝ f)) := hDf.continuous_fderiv (by norm_num)
  have hLc (i : Fin d) : Continuous (fun x : Euc d ↦ fderiv ℝ f x (b i)) := by fun_prop
  have hHc (i j : Fin d) :
      Continuous (fun x : Euc d ↦ fderiv ℝ (fderiv ℝ f) x (b i) (b j)) := by fun_prop
  have hLs (i : Fin d) : HasCompactSupport (fun x : Euc d ↦ fderiv ℝ f x (b i)) :=
    hsupp.fderiv_apply (𝕜 := ℝ) (b i)
  have hHs (i j : Fin d) :
      HasCompactSupport (fun x : Euc d ↦ fderiv ℝ (fderiv ℝ f) x (b i) (b j)) := by
    have h : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) :=
      (hsupp.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)
    exact h.comp_left (g := fun Q : Euc d →L[ℝ] Euc d →L[ℝ] ℝ ↦ Q (b i) (b j)) (by simp)
  exact ⟨hLc, hHc, hLs, hHs⟩

/-- Evaluation of a continuous function on a measurable scaled Brownian increment
is measurable, including a measurable past-event indicator. -/
private lemma measurable_taylor_difference {d : ℕ} {f : Euc d → ℝ}
    (hf : Continuous f) {X : BrownianPath d → Euc d} (hX : Measurable X)
    {A : Set (BrownianPath d)} (hA : MeasurableSet A) (σ : ℝ) (t s : ℝ≥0) :
    Measurable (A.indicator (fun ω ↦
      f (X ω + σ • (ω (t + s) - ω t)) - f (X ω))) := by
  have hinc : Measurable (fun ω : BrownianPath d ↦ ω (t + s) - ω t) :=
    (continuous_eval_const (t + s)).measurable.sub (continuous_eval_const t).measurable
  have hscaled : Measurable (fun ω : BrownianPath d ↦ σ • (ω (t + s) - ω t)) :=
    hinc.const_smul σ
  exact ((hf.measurable.comp (hX.add hscaled)).sub (hf.measurable.comp hX)).indicator hA

/-- Uniform compensated Taylor control, including integrability of each past-tested
increment. The covariance normalization gives generator `(σ² / 2) Δ`. -/
private theorem compensated_taylor_control {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ (t s : ℝ≥0) (X : BrownianPath d → Euc d)
      (A : Set (BrownianPath d)),
      Measurable[brownianNaturalFiltration d t] X →
      MeasurableSet[brownianNaturalFiltration d t] A →
      Integrable (A.indicator (fun ω ↦
        f (X ω + σ • (ω (t + s) - ω t)) - f (X ω) -
          (s : ℝ) * (σ ^ 2 / 2 * Δ f (X ω)))) μ ∧
      |∫ ω, A.indicator (fun ω ↦
        f (X ω + σ • (ω (t + s) - ω t)) - f (X ω) -
          (s : ℝ) * (σ ^ 2 / 2 * Δ f (X ω))) ω ∂μ| ≤
        ε * (s : ℝ) + C * (s : ℝ) ^ 2 := by
  classical
  letI : IsProbabilityMeasure μ := hμ.1
  let η := ε / (σ ^ 2 * (d : ℝ) + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨C, hC, hR⟩ := uniform_taylor_remainder_of_contDiff_compactSupport hf hsupp hη
  refine ⟨C * σ ^ 4 * (3 * (d : ℝ) ^ 2), by positivity, fun t s X A hX hA ↦ ?_⟩
  have hXall : Measurable X := hX.mono ((brownianNaturalFiltration d).le t) le_rfl
  have hAall : MeasurableSet A := (brownianNaturalFiltration d).le t _ hA
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let L : Fin d → BrownianPath d → ℝ := fun i ↦
    A.indicator (fun ω ↦ σ * fderiv ℝ f (X ω) (b i))
  let H : Fin d → Fin d → BrownianPath d → ℝ := fun i j ↦
    A.indicator (fun ω ↦ σ ^ 2 * fderiv ℝ (fderiv ℝ f) (X ω) (b i) (b j))
  obtain ⟨hLc, hHc, hLs, hHs⟩ := compactSupport_derivative_entries hf hsupp
  have hLm (i : Fin d) : Measurable[brownianNaturalFiltration d t] (L i) :=
    (measurable_const.mul ((hLc i).measurable.comp hX)).indicator hA
  have hHm (i j : Fin d) : Measurable[brownianNaturalFiltration d t] (H i j) :=
    (measurable_const.mul ((hHc i j).measurable.comp hX)).indicator hA
  have hLi (i : Fin d) : Integrable (L i) μ := by
    have hi : Integrable (fun ω ↦ fderiv ℝ f (X ω) (b i)) μ :=
      integrable_continuous_comp_of_compactSupport (hLc i) (hLs i) hXall
    exact (hi.const_mul σ).indicator hAall
  have hHi (i j : Fin d) : Integrable (H i j) μ := by
    have hi : Integrable (fun ω ↦ fderiv ℝ (fderiv ℝ f) (X ω) (b i) (b j)) μ :=
      integrable_continuous_comp_of_compactSupport (hHc i j) (hHs i j) hXall
    exact (hi.const_mul (σ ^ 2)).indicator hAall
  have htraceF (x : Euc d) : ∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i) = Δ f x := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
    apply Finset.sum_congr rfl
    intro i hi
    exact bilinearIteratedFDerivTwo_eq_iteratedFDeriv f x _ _
  have htrace (ω : BrownianPath d) : ∑ i, H i i ω =
      σ ^ 2 * A.indicator (fun ω ↦ Δ f (X ω)) ω := by
    by_cases hω : ω ∈ A
    · simp only [H, indicator_of_mem hω, ← Finset.mul_sum, htraceF]
    · simp only [H, indicator_of_notMem hω, mul_zero, Finset.sum_const_zero]
  let F : BrownianPath d → ℝ :=
    A.indicator (fun ω ↦ f (X ω + σ • (ω (t + s) - ω t)) - f (X ω))
  have hmF : AEStronglyMeasurable F μ :=
    (measurable_taylor_difference hf.continuous hXall hAall σ t s).aestronglyMeasurable
  have hrem (ω : BrownianPath d) :
      |F ω - (∑ i, L i ω * (ω (t + s) i - ω t i)) - (1 / 2 : ℝ) *
        (∑ i, ∑ j, H i j ω *
          ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)))| ≤
        (η * σ ^ 2) * ‖ω (t + s) - ω t‖ ^ 2 +
        (C * σ ^ 4) * ‖ω (t + s) - ω t‖ ^ 4 := by
    by_cases hω : ω ∈ A
    · simp only [F, L, H, indicator_of_mem hω]
      exact scaled_coordinate_taylor_remainder hσ hR (X ω) (ω (t + s) - ω t)
    · simp only [F, L, H, indicator_of_notMem hω, zero_mul, mul_zero, Finset.sum_const_zero,
        sub_zero, abs_zero]
      positivity
  have h := predictable_compensated_taylor_bound hμ t s L H hLm hHm hLi hHi
    hmF (mul_nonneg hC (pow_nonneg hσ.le 4)) hrem
  let D : BrownianPath d → ℝ := A.indicator (fun ω ↦ Δ f (X ω))
  have hiD : Integrable D μ := by
    have hsum := integrable_finsetSum Finset.univ (fun i _ ↦ hHi i i)
    have heq : (fun ω ↦ ∑ i, H i i ω) = fun ω ↦ σ ^ 2 * D ω :=
      funext htrace
    rw [heq] at hsum
    have hn : σ ^ 2 ≠ 0 := pow_ne_zero _ hσ.ne'
    exact (hsum.const_mul (σ ^ 2)⁻¹).congr
      (Filter.Eventually.of_forall (fun ω ↦ by dsimp; field_simp [hn]))
  have heq (ω : BrownianPath d) :
      A.indicator (fun ω ↦ f (X ω + σ • (ω (t + s) - ω t)) - f (X ω) -
        (s : ℝ) * (σ ^ 2 / 2 * Δ f (X ω))) ω =
        F ω - ((s : ℝ) * (σ ^ 2 / 2)) * D ω := by
    by_cases hω : ω ∈ A
    · simp only [F, D, indicator_of_mem hω]
      ring
    · simp only [F, D, indicator_of_notMem hω, mul_zero, sub_self]
  have hi := h.1.sub (hiD.const_mul ((s : ℝ) * (σ ^ 2 / 2)))
  refine ⟨hi.congr (Filter.Eventually.of_forall (fun ω ↦ (heq ω).symm)), ?_⟩
  simp_rw [heq]
  rw [integral_sub h.1 (hiD.const_mul _), integral_const_mul]
  have hmean : (1 / 2 : ℝ) * (s : ℝ) * (∫ ω, ∑ i, H i i ω ∂μ) =
      ((s : ℝ) * (σ ^ 2 / 2)) * ∫ ω, D ω ∂μ := by
    simp_rw [htrace]
    rw [integral_const_mul]
    ring
  rw [hmean] at h
  refine h.2.trans ?_
  have hηle : η * σ ^ 2 * (d : ℝ) ≤ ε := by
    have hp : 0 < σ ^ 2 * (d : ℝ) + 1 := by positivity
    dsimp [η]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).2
    nlinarith [sq_nonneg σ, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  calc
    _ ≤ ε * (s : ℝ) + (C * σ ^ 4) *
        (3 * (d : ℝ) ^ 2 * (s : ℝ) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right hηle s.coe_nonneg) le_rfl
    _ = _ := by ring

/-- A compactly supported C² function has integrable compensated predictable increments. -/
theorem integrable_taylor_increment {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 < σ) (t s : ℝ≥0)
    (Y : BrownianPath d → Euc d) (H : Set (BrownianPath d))
    (hY : Measurable[brownianNaturalFiltration d t] Y)
    (hH : MeasurableSet[brownianNaturalFiltration d t] H) :
    Integrable (H.indicator (fun ω ↦
      f (Y ω + σ • (ω (t + s) - ω t)) - f (Y ω) -
        (s : ℝ) * (σ ^ 2 / 2 * Δ f (Y ω)))) μ := by
  obtain ⟨C, _, hC⟩ := compensated_taylor_control hμ hf hc hσ zero_lt_one
  exact (hC t s Y H hY hH).1

/-- The predictable Taylor error has arbitrarily small linear coefficient and a
uniform quadratic remainder in time, for Brownian covariance `t I`. -/
theorem taylor_increment_error {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ (t s : ℝ≥0) (Y : BrownianPath d → Euc d)
      (H : Set (BrownianPath d)),
      Measurable[brownianNaturalFiltration d t] Y →
      MeasurableSet[brownianNaturalFiltration d t] H →
      |∫ ω, H.indicator (fun ω ↦
        f (Y ω + σ • (ω (t + s) - ω t)) - f (Y ω) -
          (s : ℝ) * (σ ^ 2 / 2 * Δ f (Y ω))) ω ∂μ| ≤
        ε * (s : ℝ) + C * (s : ℝ) ^ 2 := by
  obtain ⟨C, hC, h⟩ := compensated_taylor_control hμ hf hc hσ hε
  exact ⟨C, hC, fun t s Y H hY hH ↦ (h t s Y H hY hH).2⟩

/-- The error estimate applies to a nonzero smooth bump under an existing
one-dimensional Brownian law, with scale one and a deterministic starting point. -/
theorem exists_brownian_bump_taylor_bound :
    let b : ContDiffBump (0 : Euc 1) := ⟨1, 2, one_pos, one_lt_two⟩
    ∃ μ : Measure (BrownianPath 1), IsStandardBrownianLaw μ ∧ b (0 : Euc 1) = 1 ∧
      ∀ ε : ℝ, 0 < ε → ∃ C ≥ 0, ∀ t s : ℝ≥0,
        Integrable (fun ω : BrownianPath 1 ↦
          b (ω (t + s) - ω t) - b 0 - (s : ℝ) * (1 / 2 * Δ (⇑b) 0)) μ ∧
        |∫ ω, b (ω (t + s) - ω t) - b 0 -
          (s : ℝ) * (1 / 2 * Δ (⇑b) 0) ∂μ| ≤ ε * (s : ℝ) + C * (s : ℝ) ^ 2 := by
  intro b
  obtain ⟨μ, hμ⟩ := BrownianPathCoordsExample.exists_isStandardBrownianLaw_one
  refine ⟨μ, hμ, b.one_of_mem_closedBall (by simp [b]), ?_⟩
  intro ε hε
  obtain ⟨C, hC, h⟩ := taylor_increment_error hμ b.contDiff b.hasCompactSupport
    (σ := 1) zero_lt_one hε
  refine ⟨C, hC, fun t s ↦ ?_⟩
  have hi := integrable_taylor_increment hμ b.contDiff b.hasCompactSupport
    (σ := 1) zero_lt_one t s (fun _ ↦ 0) univ measurable_const MeasurableSet.univ
  have he := h t s (fun _ ↦ 0) univ measurable_const MeasurableSet.univ
  simpa only [indicator_univ, one_smul, zero_add, one_pow] using And.intro hi he

end LatticeProb
