/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianStoppedStep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianPredictableTaylor
import LatticeProb.Bonanno.BouRabeeGwynne.HessianTaylorRemainder

/-!
# Actual stopped Brownian one-step harmonic error

The event deciding whether to take a step and the current position are
measurable in the full natural filtration. Compactly supported C² harmonic
functions give the predictable coefficients and the pointwise remainder;
neither the martingale property nor a conditional drift estimate is assumed.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Laplacian Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

private lemma integrable_continuous_comp_of_compactSupport
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : E → ℝ} (hf : Continuous f) (hsupp : HasCompactSupport f)
    {X : Ω → E} (hX : Measurable X) : Integrable (fun ω ↦ f (X ω)) μ := by
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hf
  exact (integrable_const M).mono' (hf.measurable.comp hX).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω ↦ hM (X ω)))

theorem standardBrownianLaw_stopped_harmonic_step_bound {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {U : Set (Euc d)} (hh : IsHarmonicOn f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ (t s : ℝ≥0) (X : BrownianPath d → Euc d) (A : Set (BrownianPath d)),
      Measurable[brownianNaturalFiltration d t] X →
      MeasurableSet[brownianNaturalFiltration d t] A →
      (∀ ω ∈ A, X ω ∈ U) →
      Integrable (A.indicator (fun ω ↦ f (X ω + (ω (t + s) - ω t)) - f (X ω))) μ ∧
      |∫ ω, A.indicator (fun ω ↦ f (X ω + (ω (t + s) - ω t)) - f (X ω)) ω ∂μ| ≤
        ε * (d : ℝ) * (s : ℝ) + C * (s : ℝ) ^ 2 := by
  classical
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨C, hC, hR⟩ := uniform_taylor_remainder_of_contDiff_compactSupport hf hsupp hε
  refine ⟨C * (3 * (d : ℝ) ^ 2), by positivity, fun t s X A hX hA hAX ↦ ?_⟩
  have hXall : Measurable X := hX.mono ((brownianNaturalFiltration d).le t) le_rfl
  have hAall : MeasurableSet A := (brownianNaturalFiltration d).le t _ hA
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let L : Fin d → BrownianPath d → ℝ := fun i ↦
    A.indicator (fun ω ↦ fderiv ℝ f (X ω) (b i))
  let H : Fin d → Fin d → BrownianPath d → ℝ := fun i j ↦
    A.indicator (fun ω ↦ fderiv ℝ (fderiv ℝ f) (X ω) (b i) (b j))
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
  have hLm (i : Fin d) : Measurable[brownianNaturalFiltration d t] (L i) :=
    ((hLc i).measurable.comp hX).indicator hA
  have hHm (i j : Fin d) : Measurable[brownianNaturalFiltration d t] (H i j) :=
    ((hHc i j).measurable.comp hX).indicator hA
  have hLi (i : Fin d) : Integrable (L i) μ :=
    (integrable_continuous_comp_of_compactSupport (hLc i) (hLs i) hXall).indicator hAall
  have hHi (i j : Fin d) : Integrable (H i j) μ :=
    (integrable_continuous_comp_of_compactSupport (hHc i j) (hHs i j) hXall).indicator hAall
  have htraceF (x : Euc d) : ∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i) = Δ f x := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
    apply Finset.sum_congr rfl
    intro i hi
    exact bilinearIteratedFDerivTwo_eq_iteratedFDeriv f x _ _
  have htrace (ω : BrownianPath d) : ∑ i, H i i ω = 0 := by
    by_cases hω : ω ∈ A
    · simp only [H, indicator_of_mem hω]
      rw [htraceF, hh.laplacian_eq_zero (hAX ω hω)]
    · simp [H, indicator_of_notMem hω]
  let F : BrownianPath d → ℝ :=
    A.indicator (fun ω ↦ f (X ω + (ω (t + s) - ω t)) - f (X ω))
  have hmF : AEStronglyMeasurable F μ := by
    have hinc : Measurable (fun ω : BrownianPath d ↦ ω (t + s) - ω t) :=
      (continuous_eval_const (t + s)).measurable.sub (continuous_eval_const t).measurable
    exact ((hf.continuous.measurable.comp (hXall.add hinc)).sub
      (hf.continuous.measurable.comp hXall)).indicator hAall |>.aestronglyMeasurable
  have hrem (ω : BrownianPath d) :
      |F ω - (∑ i, L i ω * (ω (t + s) i - ω t i)) - (1 / 2 : ℝ) *
        (∑ i, ∑ j, H i j ω *
          ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)))| ≤
        ε * ‖ω (t + s) - ω t‖ ^ 2 + C * ‖ω (t + s) - ω t‖ ^ 4 := by
    by_cases hω : ω ∈ A
    · simp only [F, L, H, indicator_of_mem hω]
      have hlin : ∑ i, fderiv ℝ f (X ω) (b i) * (ω (t + s) i - ω t i) =
          fderiv ℝ f (X ω) (ω (t + s) - ω t) := by
        rw [continuousLinearMap_eq_sum_euclidean_coordinates]
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
      have hquad : ∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) (X ω) (b i) (b j) *
          ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) =
            fderiv ℝ (fderiv ℝ f) (X ω) (ω (t + s) - ω t) (ω (t + s) - ω t) :=
        (bilinear_eq_sum_euclidean_coordinates (bilinearIteratedFDerivTwo ℝ f (X ω))
          (ω (t + s) - ω t) (ω (t + s) - ω t)).symm
      rw [hlin, hquad]
      exact hR (X ω) (ω (t + s) - ω t)
    · simp only [F, L, H, indicator_of_notMem hω, zero_mul, mul_zero, Finset.sum_const_zero,
        sub_zero, abs_zero]
      positivity
  have h := standardBrownianLaw_predictable_taylor_bound hμ t s L H hLm hHm hLi hHi
    htrace hmF hε.le hC hrem
  exact ⟨h.1, h.2.trans_eq (by ring)⟩

end BouRabeeGwynne
