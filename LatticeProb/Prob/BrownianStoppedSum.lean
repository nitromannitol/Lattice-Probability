/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/BrownianStoppedStep.lean, BouRabeeGwynne/BrownianStoppedSum.lean.
-/

import LatticeProb.Prob.BrownianPredictableTaylor
import LatticeProb.Prob.BrownianPathSpace
import LatticeProb.Prob.BrownianHessianTaylor
import LatticeProb.Prob.DyadicExitApprox
import LatticeProb.Analysis.HarmonicBridge
import LatticeProb.Analysis.HessianTaylorRemainder
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Stopped Brownian harmonic steps and dyadic stopped sums

The one-step stopped Taylor bound for a compactly supported `C²` function that is harmonic
on a set `U`, and its telescoping sum along the dyadic approximation of a bounded stopping time.
The step decision is the event that the stopping time is still in the future, and the endpoint
is the upper dyadic approximation of the stopping time.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Laplacian Set
open scoped NNReal ENNReal

namespace LatticeProb

private lemma integrable_continuous_comp_of_compactSupport
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : E → ℝ} (hf : Continuous f) (hsupp : HasCompactSupport f)
    {X : Ω → E} (hX : Measurable X) : Integrable (fun ω ↦ f (X ω)) μ := by
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hf
  exact (integrable_const M).mono' (hf.measurable.comp hX).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω ↦ hM (X ω)))

/-- The one-step stopped harmonic error. For a standard Brownian law `μ` and a function `f` that is
`C²` with compact support and harmonic on `U`, there is a constant `C ≥ 0`, uniform over all
times, coefficients, and events, such that for a coefficient `X` and an event `A` measurable at
time `t` with `X ω ∈ U` on `A`, the increment `A.indicator (f (X + Δω) - f X)` is integrable and
its mean is at most `ε * d * s + C * s ^ 2`. -/
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
    htrace hmF hC hrem
  exact ⟨h.1, h.2.trans_eq (by ring)⟩

/-- Telescoping over a truncated index range: the increments `g (j + 1) - g j` kept by the
indicator `j < k` and summed over `j < m` equal `g (min m k) - g 0`. -/
lemma sum_stopped_differences (g : ℕ → ℝ) (m k : ℕ) :
    (∑ j ∈ Finset.range m, if j < k then g (j + 1) - g j else 0) =
      g (min m k) - g 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : m < k
    · rw [if_pos h, Nat.min_eq_left h.le, Nat.min_eq_left (Nat.succ_le_of_lt h)]
      ring
    · have hk : k ≤ m := Nat.le_of_not_gt h
      rw [if_neg h, Nat.min_eq_right hk, Nat.min_eq_right (hk.trans (Nat.le_succ m))]
      ring

/-- The dyadic telescoping identity. The increment of `g ω` between the dyadic stopping time
`dyadicStoppingTime σ n ω` and `0` is the sum over the indices `j < ⌈N * 2ⁿ⌉₊` of the increments
between the grid points `j / 2ⁿ` and `(j + 1) / 2ⁿ`, kept exactly when `j / 2ⁿ < σ ω`. -/
lemma dyadic_stopped_difference_eq_sum {Ω : Type*}
    (g : Ω → ℝ≥0 → ℝ) (σ : Ω → ℝ≥0) {N : ℝ≥0}
    (hN : ∀ ω, σ ω ≤ N) (n : ℕ) (ω : Ω) :
    g ω (dyadicStoppingTime σ n ω) - g ω 0 =
      ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊,
        if (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω then
          g ω ((j + 1 : ℕ) / (2 : ℝ≥0) ^ n) - g ω ((j : ℝ≥0) / (2 : ℝ≥0) ^ n)
        else 0 := by
  have hk : ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊ ≤ ⌈N * (2 : ℝ≥0) ^ n⌉₊ :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right (hN ω) (by positivity))
  have hthreshold (j : ℕ) : j < ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊ ↔
      (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω := by
    rw [Nat.lt_ceil, div_lt_iff₀ (by positivity : 0 < (2 : ℝ≥0) ^ n)]
  have h := sum_stopped_differences (fun j ↦ g ω ((j : ℝ≥0) / (2 : ℝ≥0) ^ n))
    ⌈N * (2 : ℝ≥0) ^ n⌉₊ ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊
  simpa only [Nat.min_eq_right hk, hthreshold, Nat.cast_zero, zero_div, dyadicStoppingTime]
    using h.symm

/-- For a stopping time `σ` with values in `ℝ≥0`, the event `{t < σ}` is measurable at time `t`. -/
lemma measurableSet_before_nnreal_stopping {d : ℕ} {σ : BrownianPath d → ℝ≥0}
    (hσ : IsStoppingTime (brownianNaturalFiltration d) (fun ω ↦ (σ ω : ℝ≥0∞)))
    (t : ℝ≥0) : MeasurableSet[brownianNaturalFiltration d t] {ω | t < σ ω} := by
  have h := (hσ t).compl
  change MeasurableSet[brownianNaturalFiltration d t]
    ({ω : BrownianPath d | (σ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)}ᶜ) at h
  simpa only [compl_setOf, not_le, ENNReal.coe_lt_coe] using h

/-- Summing the proved one-step bounds up to an actual bounded stopping time.
The constant is uniform over the stopping time, starting point, and dyadic mesh. -/
theorem standardBrownianLaw_dyadic_stopped_harmonic_bound {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {U : Set (Euc d)} (hh : IsHarmonicOn f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ (σ : BrownianPath d → ℝ≥0),
      IsStoppingTime (brownianNaturalFiltration d) (fun ω ↦ (σ ω : ℝ≥0∞)) →
      ∀ N : ℝ≥0, (∀ ω, σ ω ≤ N) → ∀ z : Euc d,
      (∀ ω t, t < σ ω → z + ω t ∈ U) → ∀ n : ℕ,
      Integrable (fun ω ↦ f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0)) μ ∧
      |∫ ω, f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0) ∂μ| ≤
        (⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) *
          (ε * (d : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) +
            C * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hstep⟩ := standardBrownianLaw_stopped_harmonic_step_bound hμ hf hsupp hh hε
  refine ⟨C, hC, fun σ hσ N hN z hstay n ↦ ?_⟩
  let D : ℕ → BrownianPath d → ℝ := fun j ω ↦
    if (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω then
      f (z + ω ((j + 1 : ℕ) / (2 : ℝ≥0) ^ n)) - f (z + ω ((j : ℝ≥0) / (2 : ℝ≥0) ^ n))
    else 0
  let B : ℝ := ε * (d : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) +
    C * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ^ 2
  have hD (j : ℕ) : Integrable (D j) μ ∧ |∫ ω, D j ω ∂μ| ≤ B := by
    let t : ℝ≥0 := (j : ℝ≥0) / (2 : ℝ≥0) ^ n
    let s : ℝ≥0 := 1 / (2 : ℝ≥0) ^ n
    have htime : t + s = (j + 1 : ℕ) / (2 : ℝ≥0) ^ n := by
      dsimp [t, s]
      rw [← add_div, Nat.cast_add, Nat.cast_one]
    have hXm : Measurable[brownianNaturalFiltration d t]
        (fun ω : BrownianPath d ↦ z + ω t) := by
      apply measurable_const.add
      exact (comap_measurable (fun ω : BrownianPath d ↦ ω t)).mono
        (le_iSup₂_of_le t le_rfl le_rfl) le_rfl
    have h := hstep t s (fun ω ↦ z + ω t) {ω | t < σ ω} hXm
      (measurableSet_before_nnreal_stopping hσ t) (fun ω hω ↦ hstay ω t hω)
    have heq : {ω | t < σ ω}.indicator
        (fun ω ↦ f ((z + ω t) + (ω (t + s) - ω t)) - f (z + ω t)) = D j := by
      funext ω
      by_cases hω : t < σ ω
      · rw [indicator_of_mem (show ω ∈ {ω | t < σ ω} from hω)]
        dsimp [D]
        rw [if_pos hω, ← htime]
        congr 2
        abel
      · rw [indicator_of_notMem (show ω ∉ {ω | t < σ ω} from hω)]
        exact (if_neg hω).symm
    rw [heq] at h
    exact h
  have heq : (fun ω ↦ f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0)) =
      fun ω ↦ ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, D j ω := by
    funext ω
    exact dyadic_stopped_difference_eq_sum (fun ω t ↦ f (z + ω t)) σ hN n ω
  rw [heq]
  refine ⟨integrable_finsetSum _ (fun j _ ↦ (hD j).1), ?_⟩
  rw [integral_finsetSum _ (fun j _ ↦ (hD j).1)]
  calc
    |∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, ∫ ω, D j ω ∂μ| ≤
        ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, |∫ ω, D j ω ∂μ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, B :=
      Finset.sum_le_sum (fun j _ ↦ (hD j).2)
    _ = _ := by simp [B, mul_add]

namespace BrownianStoppedSumExample

/-- Concrete finite check of `sum_stopped_differences` with `g n = n ^ 2`, `m = 4`, `k = 2`:
only the increments at `j = 0, 1` are kept, giving `g 2 - g 0 = 4`. -/
theorem sum_stopped_differences_concrete :
    (∑ j ∈ Finset.range 4, if j < 2 then ((j + 1 : ℕ) : ℝ) ^ 2 - (j : ℝ) ^ 2 else 0) = 4 := by
  rw [sum_stopped_differences (fun n : ℕ ↦ (n : ℝ) ^ 2) 4 2]
  norm_num

/-- The one-step stopped harmonic bound for a constant stopping time `c`, using the event `{t < c}`
that the stopping time is still in the future at time `t`. The law `μ` is a binder, and the
starting point `x` is a fixed point of `U`. -/
theorem stopped_step_bound_constant_time {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : HasCompactSupport f) {U : Set (Euc d)} (hh : IsHarmonicOn f U) {ε : ℝ}
    (hε : 0 < ε) {x : Euc d} (hx : x ∈ U) (c t : ℝ≥0) :
    ∃ C ≥ 0, ∀ s : ℝ≥0,
      Integrable ({_ω : BrownianPath d | t < c}.indicator
        (fun ω ↦ f (x + (ω (t + s) - ω t)) - f x)) μ ∧
      |∫ ω, {_ω : BrownianPath d | t < c}.indicator
        (fun ω ↦ f (x + (ω (t + s) - ω t)) - f x) ω ∂μ| ≤
        ε * (d : ℝ) * (s : ℝ) + C * (s : ℝ) ^ 2 := by
  obtain ⟨C, hC, h⟩ := standardBrownianLaw_stopped_harmonic_step_bound hμ hf hsupp hh hε
  exact ⟨C, hC, fun s ↦ h t s (fun _ ↦ x) {ω | t < c} measurable_const
    (MeasurableSet.const _) (fun _ _ ↦ hx)⟩

end BrownianStoppedSumExample

end LatticeProb
