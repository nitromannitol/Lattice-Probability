/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/BrownianStoppedSum.lean, BouRabeeGwynne/BrownianStoppedLimit.lean
(harmonic case; extended here by the Laplacian drift term).
-/

import LatticeProb.Prob.BrownianStoppedLimit

/-!
# Dynkin's formula for Brownian motion at a bounded stopping time

For a standard Brownian law `μ` on `BrownianPath d`, a `C²` function `f` with compact support,
a starting point `z` and a bounded stopping time `σ`,
`∫ f (z + ω σ) - f z ∂μ = (1 / 2) ∫ ∫_0^σ Δ f (z + ω u) du ∂μ`.

The proof sums the second-order Taylor expansion of `f` along the upper dyadic approximation of
`σ`. The linear and off-diagonal quadratic terms have mean zero by the independence of the
increments from the past; the diagonal quadratic terms give, step by step, `(s / 2) Δ f` at the
current position, hence a Riemann sum of `Δ f` along the path, which converges pathwise to the
time integral.

## Main results

* `standardBrownianLaw_stopped_dynkin_step_bound`: one step, with error `ε d s + C s²`.
* `standardBrownianLaw_dyadic_stopped_dynkin_bound`: the sum along the dyadic grid.
* `tendsto_dyadic_riemannSum`: dyadic left Riemann sums of a continuous function converge.
* `standardBrownianLaw_bounded_stopped_dynkin`: Dynkin's formula for a bounded stopping time.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Laplacian Set Filter
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- The Laplacian on `Euc d` as the trace of the second derivative in the standard basis. -/
lemma laplacian_eq_sum_fderiv_fderiv_basisFun {d : ℕ} (f : Euc d → ℝ) :
    Δ f = fun x ↦ ∑ i, fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.basisFun (Fin d) ℝ i)
      (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  funext x
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  exact (bilinearIteratedFDerivTwo_eq_iteratedFDeriv f x _ _).symm

/-- The Laplacian of a `C²` function is continuous. -/
lemma continuous_laplacian_of_contDiff_two {d : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Δ f) := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hHcont : Continuous (fderiv ℝ (fderiv ℝ f)) := hDf.continuous_fderiv (by norm_num)
  rw [laplacian_eq_sum_fderiv_fderiv_basisFun]
  fun_prop

/-- The Laplacian of a `C²` function with compact support is bounded. -/
lemma exists_bound_laplacian_of_contDiff_compactSupport {d : ℕ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f) :
    ∃ M, ∀ x, ‖Δ f x‖ ≤ M := by
  have hs : HasCompactSupport (Δ f) := by
    have h : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) :=
      (hsupp.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)
    rw [laplacian_eq_sum_fderiv_fderiv_basisFun]
    exact h.comp_left (g := fun Q : Euc d →L[ℝ] Euc d →L[ℝ] ℝ ↦
      ∑ i, Q (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i))
      (by simp)
  exact hs.exists_bound_of_continuous (continuous_laplacian_of_contDiff_two hf)

/-- The one-step stopped Dynkin error. For a standard Brownian law `μ` and a function `f` that is
`C²` with compact support, there is a constant `C ≥ 0`, uniform over all times, coefficients
and events, such that for a coefficient `X` and an event `A` measurable at time `t`, the stopped
increment `A.indicator (f (X + (ω (t + s) - ω t)) - f X)` is integrable and its mean differs from
`(s / 2) ∫ A.indicator (Δ f X)` by at most `ε * d * s + C * s ^ 2`. -/
theorem standardBrownianLaw_stopped_dynkin_step_bound {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ (t s : ℝ≥0) (X : BrownianPath d → Euc d) (A : Set (BrownianPath d)),
      Measurable[brownianNaturalFiltration d t] X →
      MeasurableSet[brownianNaturalFiltration d t] A →
      Integrable (A.indicator (fun ω ↦ f (X ω + (ω (t + s) - ω t)) - f (X ω))) μ ∧
      |(∫ ω, A.indicator (fun ω ↦ f (X ω + (ω (t + s) - ω t)) - f (X ω)) ω ∂μ) -
        (s : ℝ) / 2 * ∫ ω, A.indicator (fun ω ↦ Δ f (X ω)) ω ∂μ| ≤
        ε * (d : ℝ) * (s : ℝ) + C * (s : ℝ) ^ 2 := by
  classical
  have : IsProbabilityMeasure μ := hμ.1
  obtain ⟨C, hC, hR⟩ := uniform_taylor_remainder_of_contDiff_compactSupport hf hsupp hε
  refine ⟨C * (3 * (d : ℝ) ^ 2), by positivity, fun t s X A hX hA ↦ ?_⟩
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
  have hbdd {g : Euc d → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) :
      Integrable (fun ω ↦ g (X ω)) μ := by
    obtain ⟨M, hM⟩ := hgs.exists_bound_of_continuous hg
    exact (integrable_const M).mono' (hg.measurable.comp hXall).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω ↦ hM (X ω)))
  have hLm (i : Fin d) : Measurable[brownianNaturalFiltration d t] (L i) :=
    ((hLc i).measurable.comp hX).indicator hA
  have hHm (i j : Fin d) : Measurable[brownianNaturalFiltration d t] (H i j) :=
    ((hHc i j).measurable.comp hX).indicator hA
  have hLi (i : Fin d) : Integrable (L i) μ := (hbdd (hLc i) (hLs i)).indicator hAall
  have hHi (i j : Fin d) : Integrable (H i j) μ := (hbdd (hHc i j) (hHs i j)).indicator hAall
  have hdiag (ω : BrownianPath d) :
      ∑ i, H i i ω = A.indicator (fun ω ↦ Δ f (X ω)) ω := by
    by_cases hω : ω ∈ A
    · simp only [H, indicator_of_mem hω]
      rw [laplacian_eq_sum_fderiv_fderiv_basisFun f]
    · simp [H, indicator_of_notMem hω]
  -- the off-diagonal part of the Hessian coefficients has zero trace
  let H' : Fin d → Fin d → BrownianPath d → ℝ := fun i j ↦ if i = j then 0 else H i j
  have hH'm (i j : Fin d) : Measurable[brownianNaturalFiltration d t] (H' i j) := by
    by_cases hij : i = j
    · have h0 : H' i j = 0 := by simp [H', hij]
      rw [h0]
      exact measurable_const
    · have h0 : H' i j = H i j := by simp [H', hij]
      rw [h0]
      exact hHm i j
  have hH'i (i j : Fin d) : Integrable (H' i j) μ := by
    by_cases hij : i = j
    · have h0 : H' i j = 0 := by simp [H', hij]
      rw [h0]
      exact integrable_const (0 : ℝ)
    · have h0 : H' i j = H i j := by simp [H', hij]
      rw [h0]
      exact hHi i j
  have htrace' (ω : BrownianPath d) : ∑ i, H' i i ω = 0 := by simp [H']
  -- the diagonal quadratic term
  let Q : BrownianPath d → ℝ := fun ω ↦
    ∑ i, H i i ω * ((ω (t + s) i - ω t i) * (ω (t + s) i - ω t i))
  have hQterm (i : Fin d) : Integrable (fun ω : BrownianPath d ↦
      H i i ω * ((ω (t + s) i - ω t i) * (ω (t + s) i - ω t i))) μ :=
    standardBrownianLaw_integrable_predictable_quadratic hμ t s (hHm i i) (hHi i i) i i
  have hQi : Integrable Q μ := integrable_finsetSum _ (fun i _ ↦ hQterm i)
  have hQint : ∫ ω, Q ω ∂μ = (s : ℝ) * ∫ ω, A.indicator (fun ω ↦ Δ f (X ω)) ω ∂μ := by
    calc ∫ ω, Q ω ∂μ = ∑ i, ∫ ω, H i i ω *
          ((ω (t + s) i - ω t i) * (ω (t + s) i - ω t i)) ∂μ :=
          integral_finsetSum _ (fun i _ ↦ hQterm i)
      _ = ∑ i, (s : ℝ) * ∫ ω, H i i ω ∂μ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [standardBrownianLaw_integral_predictable_quadratic hμ t s (hHm i i) i i]
          simp [mul_comm]
      _ = (s : ℝ) * ∫ ω, ∑ i, H i i ω ∂μ := by
          rw [integral_finsetSum _ (fun i _ ↦ hHi i i), Finset.mul_sum]
      _ = _ := by simp only [hdiag]
  have hsplit (ω : BrownianPath d) :
      ∑ i, ∑ j, H i j ω * ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) =
        ∑ i, ∑ j, H' i j ω * ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) + Q ω := by
    calc ∑ i, ∑ j, H i j ω * ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) =
          ∑ i, ∑ j, (H' i j ω * ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) +
            if i = j then H i i ω * ((ω (t + s) i - ω t i) * (ω (t + s) i - ω t i))
            else 0) := by
          refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ ?_))
          by_cases hij : i = j
          · subst hij
            simp [H']
          · simp [H', hij]
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, reduceIte, Q]
  let G : BrownianPath d → ℝ :=
    A.indicator (fun ω ↦ f (X ω + (ω (t + s) - ω t)) - f (X ω))
  let F : BrownianPath d → ℝ := fun ω ↦ G ω - (1 / 2 : ℝ) * Q ω
  have hmG : AEStronglyMeasurable G μ := by
    have hinc : Measurable (fun ω : BrownianPath d ↦ ω (t + s) - ω t) :=
      (continuous_eval_const (t + s)).measurable.sub (continuous_eval_const t).measurable
    exact ((hf.continuous.measurable.comp (hXall.add hinc)).sub
      (hf.continuous.measurable.comp hXall)).indicator hAall |>.aestronglyMeasurable
  have hmF : AEStronglyMeasurable F μ := hmG.sub (hQi.aestronglyMeasurable.const_mul _)
  have hremG (ω : BrownianPath d) :
      |G ω - (∑ i, L i ω * (ω (t + s) i - ω t i)) - (1 / 2 : ℝ) *
        (∑ i, ∑ j, H i j ω *
          ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)))| ≤
        ε * ‖ω (t + s) - ω t‖ ^ 2 + C * ‖ω (t + s) - ω t‖ ^ 4 := by
    by_cases hω : ω ∈ A
    · simp only [G, L, H, indicator_of_mem hω]
      have hlin : ∑ i, fderiv ℝ f (X ω) (b i) * (ω (t + s) i - ω t i) =
          fderiv ℝ f (X ω) (ω (t + s) - ω t) := by
        rw [continuousLinearMap_eq_sum_euclidean_coordinates]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      have hquad : ∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) (X ω) (b i) (b j) *
          ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) =
            fderiv ℝ (fderiv ℝ f) (X ω) (ω (t + s) - ω t) (ω (t + s) - ω t) :=
        (bilinear_eq_sum_euclidean_coordinates (bilinearIteratedFDerivTwo ℝ f (X ω))
          (ω (t + s) - ω t) (ω (t + s) - ω t)).symm
      rw [hlin, hquad]
      exact hR (X ω) (ω (t + s) - ω t)
    · simp only [G, L, H, indicator_of_notMem hω, zero_mul, mul_zero, Finset.sum_const_zero,
        sub_zero, abs_zero]
      positivity
  have hrem (ω : BrownianPath d) :
      |F ω - (∑ i, L i ω * (ω (t + s) i - ω t i)) - (1 / 2 : ℝ) *
        (∑ i, ∑ j, H' i j ω *
          ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)))| ≤
        ε * ‖ω (t + s) - ω t‖ ^ 2 + C * ‖ω (t + s) - ω t‖ ^ 4 := by
    have heq : F ω - (∑ i, L i ω * (ω (t + s) i - ω t i)) - (1 / 2 : ℝ) *
        (∑ i, ∑ j, H' i j ω * ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j))) =
        G ω - (∑ i, L i ω * (ω (t + s) i - ω t i)) - (1 / 2 : ℝ) *
        (∑ i, ∑ j, H i j ω * ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j))) := by
      rw [hsplit ω]
      simp only [F]
      ring
    rw [heq]
    exact hremG ω
  have h := standardBrownianLaw_predictable_taylor_bound hμ t s L H' hLm hH'm hLi hH'i
    htrace' hmF hC hrem
  have hGF : G = fun ω ↦ F ω + (1 / 2 : ℝ) * Q ω := by
    funext ω
    simp only [F]
    ring
  have hGi : Integrable G μ := by
    rw [hGF]
    exact h.1.add (hQi.const_mul _)
  refine ⟨hGi, ?_⟩
  have hGint : ∫ ω, G ω ∂μ = (∫ ω, F ω ∂μ) + (1 / 2 : ℝ) * ∫ ω, Q ω ∂μ := by
    rw [hGF, integral_add h.1 (hQi.const_mul _), integral_const_mul]
  change |(∫ ω, G ω ∂μ) - _| ≤ _
  rw [hGint, hQint]
  have hcancel : (∫ ω, F ω ∂μ) + (1 / 2 : ℝ) *
      ((s : ℝ) * ∫ ω, A.indicator (fun ω ↦ Δ f (X ω)) ω ∂μ) -
      (s : ℝ) / 2 * ∫ ω, A.indicator (fun ω ↦ Δ f (X ω)) ω ∂μ = ∫ ω, F ω ∂μ := by ring
  rw [hcancel]
  exact h.2.trans_eq (by ring)

/-- Summing the one-step Dynkin bounds along the upper dyadic approximation of a bounded
stopping time. The drift is the dyadic left Riemann sum of `Δ f` along the path, cut at the
stopping time. The constant is uniform over the stopping time, the starting point and the
mesh. -/
theorem standardBrownianLaw_dyadic_stopped_dynkin_bound {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ (σ : BrownianPath d → ℝ≥0),
      IsStoppingTime (brownianNaturalFiltration d) (fun ω ↦ (σ ω : ℝ≥0∞)) →
      ∀ N : ℝ≥0, (∀ ω, σ ω ≤ N) → ∀ (z : Euc d) (n : ℕ),
      Integrable (fun ω ↦ f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0)) μ ∧
      |(∫ ω, f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0) ∂μ) -
        (1 / 2 : ℝ) * ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊,
          ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) *
            ∫ ω, {ω | (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω}.indicator
              (fun ω ↦ Δ f (z + ω ((j : ℝ≥0) / (2 : ℝ≥0) ^ n))) ω ∂μ| ≤
        (⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) *
          (ε * (d : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) +
            C * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hstep⟩ := standardBrownianLaw_stopped_dynkin_step_bound hμ hf hsupp hε
  refine ⟨C, hC, fun σ hσ N hN z n ↦ ?_⟩
  let s : ℝ≥0 := 1 / (2 : ℝ≥0) ^ n
  let D : ℕ → BrownianPath d → ℝ := fun j ω ↦
    if (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω then
      f (z + ω ((j + 1 : ℕ) / (2 : ℝ≥0) ^ n)) - f (z + ω ((j : ℝ≥0) / (2 : ℝ≥0) ^ n))
    else 0
  let E : ℕ → ℝ := fun j ↦ ∫ ω, {ω | (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω}.indicator
    (fun ω ↦ Δ f (z + ω ((j : ℝ≥0) / (2 : ℝ≥0) ^ n))) ω ∂μ
  let B : ℝ := ε * (d : ℝ) * (s : ℝ) + C * (s : ℝ) ^ 2
  have hD (j : ℕ) : Integrable (D j) μ ∧ |(∫ ω, D j ω ∂μ) - (s : ℝ) / 2 * E j| ≤ B := by
    let t : ℝ≥0 := (j : ℝ≥0) / (2 : ℝ≥0) ^ n
    have htime : t + s = (j + 1 : ℕ) / (2 : ℝ≥0) ^ n := by
      dsimp [t, s]
      rw [← add_div, Nat.cast_add, Nat.cast_one]
    have hXm : Measurable[brownianNaturalFiltration d t]
        (fun ω : BrownianPath d ↦ z + ω t) := by
      apply measurable_const.add
      exact (comap_measurable (fun ω : BrownianPath d ↦ ω t)).mono
        (le_iSup₂_of_le t le_rfl le_rfl) le_rfl
    have h := hstep t s (fun ω ↦ z + ω t) {ω | t < σ ω} hXm
      (measurableSet_before_nnreal_stopping hσ t)
    have heq : {ω | t < σ ω}.indicator
        (fun ω ↦ f ((z + ω t) + (ω (t + s) - ω t)) - f (z + ω t)) = D j := by
      funext ω
      by_cases hω : t < σ ω
      · rw [indicator_of_mem (show ω ∈ {ω | t < σ ω} from hω)]
        dsimp [D]
        simp only [show (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω from hω, reduceIte]
        rw [← htime]
        congr 2
        abel
      · rw [indicator_of_notMem (show ω ∉ {ω | t < σ ω} from hω)]
        dsimp [D]
        simp only [show ¬ (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω from hω, reduceIte]
    rw [heq] at h
    exact h
  have heq : (fun ω ↦ f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0)) =
      fun ω ↦ ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, D j ω := by
    funext ω
    exact dyadic_stopped_difference_eq_sum (fun ω t ↦ f (z + ω t)) σ hN n ω
  rw [heq]
  refine ⟨integrable_finsetSum _ (fun j _ ↦ (hD j).1), ?_⟩
  rw [integral_finsetSum _ (fun j _ ↦ (hD j).1)]
  change |(∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, ∫ ω, D j ω ∂μ) -
    (1 / 2 : ℝ) * ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, (s : ℝ) * E j| ≤ _
  have hsum : (∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, ∫ ω, D j ω ∂μ) -
      (1 / 2 : ℝ) * ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, (s : ℝ) * E j =
      ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, ((∫ ω, D j ω ∂μ) - (s : ℝ) / 2 * E j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ ↦ by ring)
  rw [hsum]
  calc
    |∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, ((∫ ω, D j ω ∂μ) - (s : ℝ) / 2 * E j)| ≤
        ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, |(∫ ω, D j ω ∂μ) - (s : ℝ) / 2 * E j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, B :=
      Finset.sum_le_sum (fun j _ ↦ (hD j).2)
    _ = _ := by simp [B, s, mul_add]

/-- The error of a left Riemann sum with mesh `s` over `[0, k s]`, when `h` oscillates by less
than `ε'` on `[0, a + 1]` at distances below `δ > s` and `k s ≤ a + 1`. -/
lemma abs_riemannSum_sub_integral_le {h : ℝ → ℝ} (hh : Continuous h) {a s δ ε' : ℝ} (k : ℕ)
    (hs : 0 < s) (hε' : 0 ≤ ε') (hk : (k : ℝ) * s ≤ a + 1)
    (hδ : ∀ x ∈ Icc (0 : ℝ) (a + 1), ∀ y ∈ Icc (0 : ℝ) (a + 1),
      dist x y < δ → dist (h x) (h y) < ε') (hsδ : s < δ) :
    |(∑ j ∈ Finset.range k, s * h (j * s)) - ∫ u in (0 : ℝ)..(k * s), h u| ≤ (a + 1) * ε' := by
  have hint : ∀ j < k, IntervalIntegrable h volume ((j : ℝ) * s) (((j + 1 : ℕ) : ℝ) * s) :=
    fun j _ ↦ hh.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ ↦ (j : ℝ) * s) hint
  simp only [Nat.cast_zero, zero_mul] at hsum
  rw [← hsum, ← Finset.sum_sub_distrib]
  have hterm : ∀ j ∈ Finset.range k,
      |s * h (j * s) - ∫ x in (j : ℝ) * s..((j + 1 : ℕ) : ℝ) * s, h x| ≤ s * ε' := by
    intro j hj
    have hjk : j + 1 ≤ k := Finset.mem_range.1 hj
    have hlen : ((j + 1 : ℕ) : ℝ) * s - j * s = s := by push_cast; ring
    have hle : (j : ℝ) * s ≤ ((j + 1 : ℕ) : ℝ) * s := by linarith
    have hconst : s * h (j * s) = ∫ _ in (j : ℝ) * s..((j + 1 : ℕ) : ℝ) * s, h (j * s) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, hlen]
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
      (hh.intervalIntegrable _ _), ← Real.norm_eq_abs]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (j : ℝ) * s) (b := ((j + 1 : ℕ) : ℝ) * s) (C := ε')
      (f := fun x ↦ h (j * s) - h x) (by
        intro x hx
        rw [uIoc_of_le hle] at hx
        obtain ⟨hx1, hx2⟩ := hx
        have hjs0 : 0 ≤ (j : ℝ) * s := by positivity
        have hkb : ((j + 1 : ℕ) : ℝ) * s ≤ a + 1 := by
          refine le_trans ?_ hk
          gcongr
        have hmem1 : (j : ℝ) * s ∈ Icc (0 : ℝ) (a + 1) := ⟨hjs0, by linarith⟩
        have hmem2 : x ∈ Icc (0 : ℝ) (a + 1) := ⟨by linarith, by linarith⟩
        have hd : dist ((j : ℝ) * s) x < δ := by
          rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
        have := hδ _ hmem1 _ hmem2 hd
        rw [Real.dist_eq] at this
        rw [Real.norm_eq_abs]
        exact this.le)
    rw [hlen, abs_of_pos hs] at hb
    linarith
  calc
    |∑ j ∈ Finset.range k, (s * h (j * s) - ∫ x in (j : ℝ) * s..((j + 1 : ℕ) : ℝ) * s, h x)| ≤
        ∑ j ∈ Finset.range k,
          |s * h (j * s) - ∫ x in (j : ℝ) * s..((j + 1 : ℕ) : ℝ) * s, h x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, s * ε' := Finset.sum_le_sum hterm
    _ = (k * s) * ε' := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ (a + 1) * ε' := mul_le_mul_of_nonneg_right hk hε'

/-- Dyadic left Riemann sums of a continuous function on `[0, a]` converge to its integral. -/
theorem tendsto_dyadic_riemannSum {h : ℝ → ℝ} (hh : Continuous h) (a : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range ⌈a * (2 : ℝ≥0) ^ n⌉₊,
      ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) * h (((j : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ))
      atTop (𝓝 (∫ u in (0 : ℝ)..(a : ℝ), h u)) := by
  have hpt (n j : ℕ) : (((j : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) =
      j * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
    push_cast
    ring
  simp only [hpt]
  have hs_pos (n : ℕ) : 0 < ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by positivity
  have hs : Tendsto (fun n : ℕ ↦ ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
    simpa [one_div, Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))
  have hlo (n : ℕ) : (a : ℝ) ≤
      (⌈a * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
    have h1 : a ≤ (⌈a * (2 : ℝ≥0) ^ n⌉₊ : ℝ≥0) * (1 / (2 : ℝ≥0) ^ n) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      exact Nat.le_ceil _
    exact_mod_cast h1
  have hhi (n : ℕ) : (⌈a * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ≤
      a + ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
    have hq : 0 < (2 : ℝ≥0) ^ n := by positivity
    have h1 : (⌈a * (2 : ℝ≥0) ^ n⌉₊ : ℝ≥0) * (1 / (2 : ℝ≥0) ^ n) ≤
        a + 1 / (2 : ℝ≥0) ^ n := by
      calc
        _ = (⌈a * (2 : ℝ≥0) ^ n⌉₊ : ℝ≥0) / (2 : ℝ≥0) ^ n := by rw [mul_one_div]
        _ ≤ (a * (2 : ℝ≥0) ^ n + 1) / (2 : ℝ≥0) ^ n :=
          div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le hq.le
        _ = a + 1 / (2 : ℝ≥0) ^ n := by
          rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hq)]
    exact_mod_cast h1
  have hI : Continuous (fun x : ℝ ↦ ∫ u in (0 : ℝ)..x, h u) :=
    continuous_iff_continuousAt.2 fun x ↦
      (hh.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt
  have hb : Tendsto (fun n : ℕ ↦
      (⌈a * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (𝓝 (a : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hlo hhi
    simpa using (tendsto_const_nhds (x := (a : ℝ))).add hs
  have hIb := (hI.tendsto (a : ℝ)).comp hb
  have herr : Tendsto (fun n : ℕ ↦
      (∑ j ∈ Finset.range ⌈a * (2 : ℝ≥0) ^ n⌉₊, ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) *
        h (j * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ))) -
      ∫ u in (0 : ℝ)..((⌈a * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)), h u)
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have huc := (isCompact_Icc (a := (0 : ℝ)) (b := (a : ℝ) + 1)).uniformContinuousOn_of_continuous
      hh.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    have ha1 : 0 < (a : ℝ) + 1 := by positivity
    obtain ⟨δ, hδ, hδh⟩ := huc (ε / (2 * ((a : ℝ) + 1))) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.eventually (gt_mem_nhds (lt_min hδ one_pos)))
    refine ⟨N, fun n hn ↦ ?_⟩
    have hsn := hN n hn
    have hk : (⌈a * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ≤ a + 1 :=
      (hhi n).trans (by linarith [min_le_right δ 1])
    have herr1 := abs_riemannSum_sub_integral_le hh ⌈a * (2 : ℝ≥0) ^ n⌉₊ (hs_pos n)
      (by positivity) hk hδh (lt_of_lt_of_le hsn (min_le_left _ _))
    rw [Real.dist_eq, sub_zero]
    calc _ ≤ ((a : ℝ) + 1) * (ε / (2 * ((a : ℝ) + 1))) := herr1
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  simpa only [sub_add_cancel, zero_add, Function.comp_def] using herr.add hIb

/-- Splitting off the indices below a threshold. -/
lemma sum_range_ite_lt_eq (g : ℕ → ℝ) {m k : ℕ} (hk : k ≤ m) :
    (∑ j ∈ Finset.range m, if j < k then g j else 0) = ∑ j ∈ Finset.range k, g j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **Dynkin's formula** for Brownian motion at a bounded stopping time. For a standard Brownian
law `μ`, a `C²` function `f` with compact support, a stopping time `σ ≤ N` and a starting point
`z`, `∫ f (z + ω σ) - f (z + ω 0) ∂μ = (1 / 2) ∫ ∫_0^σ Δ f (z + ω u) du ∂μ`. -/
theorem standardBrownianLaw_bounded_stopped_dynkin {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {σ : BrownianPath d → ℝ≥0}
    (hσ : IsStoppingTime (brownianNaturalFiltration d) (fun ω ↦ (σ ω : ℝ≥0∞)))
    (N : ℝ≥0) (hN : ∀ ω, σ ω ≤ N) (z : Euc d) :
    (∫ ω, f (z + ω (σ ω)) - f (z + ω 0) ∂μ) =
      (1 / 2 : ℝ) * ∫ ω, (∫ u in (0 : ℝ)..(σ ω : ℝ), Δ f (z + ω u.toNNReal)) ∂μ := by
  have : IsProbabilityMeasure μ := hμ.1
  have hσm : Measurable σ := measurable_nnreal_brownian_stopping hσ
  have hΔc : Continuous (Δ f) := continuous_laplacian_of_contDiff_two hf
  obtain ⟨M', hM'⟩ := exists_bound_laplacian_of_contDiff_compactSupport hf hsupp
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' 0)
  let s : ℕ → ℝ := fun n ↦ ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)
  have hs0 (n : ℕ) : 0 ≤ s n := NNReal.coe_nonneg _
  let E : ℕ → ℕ → BrownianPath d → ℝ := fun n j ω ↦
    {ω | (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω}.indicator
      (fun ω ↦ Δ f (z + ω ((j : ℝ≥0) / (2 : ℝ≥0) ^ n))) ω
  have hEm (n j : ℕ) : Measurable (E n j) :=
    (hΔc.measurable.comp (measurable_const.add
      (continuous_eval_const ((j : ℝ≥0) / (2 : ℝ≥0) ^ n)).measurable)).indicator
      (measurableSet_lt measurable_const hσm)
  have hEb (n j : ℕ) (ω : BrownianPath d) : ‖E n j ω‖ ≤ M' :=
    (norm_indicator_le_norm_self _ _).trans (hM' _)
  have hEi (n j : ℕ) : Integrable (E n j) μ :=
    (integrable_const M').mono' (hEm n j).aestronglyMeasurable
      (Filter.Eventually.of_forall (hEb n j))
  let R : ℕ → BrownianPath d → ℝ := fun n ω ↦
    ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, s n * E n j ω
  have hRint (n : ℕ) : ∫ ω, R n ω ∂μ =
      ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, s n * ∫ ω, E n j ω ∂μ := by
    rw [integral_finsetSum _ (fun j _ ↦ (hEi n j).const_mul _)]
    exact Finset.sum_congr rfl (fun j _ ↦ integral_const_mul _ _)
  -- the pathwise Riemann sums
  let J : BrownianPath d → ℝ := fun ω ↦
    ∫ u in (0 : ℝ)..(σ ω : ℝ), Δ f (z + ω u.toNNReal)
  have hRlim (ω : BrownianPath d) : Tendsto (fun n ↦ R n ω) atTop (𝓝 (J ω)) := by
    have hcont : Continuous (fun u : ℝ ↦ Δ f (z + ω u.toNNReal)) :=
      hΔc.comp (continuous_const.add (ω.continuous.comp continuous_real_toNNReal))
    refine (tendsto_dyadic_riemannSum hcont (σ ω)).congr (fun n ↦ ?_)
    have hk : ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊ ≤ ⌈N * (2 : ℝ≥0) ^ n⌉₊ :=
      Nat.ceil_mono (mul_le_mul_of_nonneg_right (hN ω) (by positivity))
    have hthreshold (j : ℕ) : j < ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊ ↔
        (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω := by
      rw [Nat.lt_ceil, div_lt_iff₀ (by positivity : 0 < (2 : ℝ≥0) ^ n)]
    have hR : R n ω = ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊,
        if j < ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊ then
          s n * Δ f (z + ω ((j : ℝ≥0) / (2 : ℝ≥0) ^ n)) else 0 := by
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      by_cases hj : (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω
      · have hj' : j < ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊ := (hthreshold j).2 hj
        simp only [E, hj', reduceIte]
        rw [indicator_of_mem (show ω ∈ {ω | (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω} from hj)]
      · have hj' : ¬ j < ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊ := fun h ↦ hj ((hthreshold j).1 h)
        simp only [E, hj', reduceIte]
        rw [indicator_of_notMem (show ω ∉ {ω | (j : ℝ≥0) / (2 : ℝ≥0) ^ n < σ ω} from hj),
          mul_zero]
    rw [hR, sum_range_ite_lt_eq _ hk]
    simp only [Real.toNNReal_coe, s]
  have hRb (n : ℕ) (ω : BrownianPath d) : ‖R n ω‖ ≤ ((N : ℝ) + 1) * M' := by
    have hlength : (⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * s n ≤ (N : ℝ) + 1 := by
      show (⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ≤ (N : ℝ) + 1
      exact_mod_cast dyadic_grid_length_le N n
    calc ‖R n ω‖ ≤ ∑ j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, ‖s n * E n j ω‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range ⌈N * (2 : ℝ≥0) ^ n⌉₊, s n * M' := by
          refine Finset.sum_le_sum (fun j _ ↦ ?_)
          rw [norm_mul, Real.norm_of_nonneg (hs0 n)]
          exact mul_le_mul_of_nonneg_left (hEb n j ω) (hs0 n)
      _ = ((⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * s n) * M' := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ ((N : ℝ) + 1) * M' := mul_le_mul_of_nonneg_right hlength hM'0
  have hJlim : Tendsto (fun n ↦ ∫ ω, R n ω ∂μ) atTop (𝓝 (∫ ω, J ω ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ ((N : ℝ) + 1) * M')
      (fun n ↦ ?_) (integrable_const _) (fun n ↦ Filter.Eventually.of_forall (hRb n))
      (Filter.Eventually.of_forall hRlim)
    exact (Finset.measurable_sum _ (fun j _ ↦ measurable_const.mul (hEm n j))).aestronglyMeasurable
  -- the stopped values
  let a : ℕ → ℝ := fun n ↦ ∫ ω,
    f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0) ∂μ
  let I : ℝ := ∫ ω, f (z + ω (σ ω)) - f (z + ω 0) ∂μ
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hf.continuous
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun ω : BrownianPath d ↦
      f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0)) μ := by
    have hm := measurable_brownian_random_evaluation (measurable_nnreal_brownian_stopping
      (isStoppingTime_dyadicStoppingTime _ hσ n))
    exact ((hf.continuous.measurable.comp (measurable_const.add hm)).sub
      (hf.continuous.measurable.comp (measurable_const.add
        (continuous_eval_const (0 : ℝ≥0)).measurable))).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖f (z + ω (dyadicStoppingTime σ n ω)) - f (z + ω 0)‖ ≤ 2 * M := by
    filter_upwards [] with ω
    exact (norm_sub_le _ _).trans
      (by linarith [hM (z + ω (dyadicStoppingTime σ n ω)), hM (z + ω 0)])
  have hlim : Tendsto a atTop (𝓝 I) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * M) hmeas (integrable_const _)
      hbound
    filter_upwards [] with ω
    exact (((hf.continuous.comp (continuous_const.add ω.continuous)).tendsto (σ ω)).comp
      (tendsto_dyadicStoppingTime σ ω)).sub tendsto_const_nhds
  have hs : Tendsto s atTop (𝓝 0) := by
    simpa [s, one_div, Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))
  have hdiff : Tendsto (fun n ↦ a n - (1 / 2 : ℝ) * ∫ ω, R n ω ∂μ) atTop
      (𝓝 (I - (1 / 2 : ℝ) * ∫ ω, J ω ∂μ)) := hlim.sub (hJlim.const_mul _)
  have hI (ε : ℝ) (hε : 0 < ε) :
      |I - (1 / 2 : ℝ) * ∫ ω, J ω ∂μ| ≤ ε * (d : ℝ) * ((N : ℝ) + 1) := by
    obtain ⟨C, hC, hsum⟩ := standardBrownianLaw_dyadic_stopped_dynkin_bound hμ hf hsupp hε
    have hboundn (n : ℕ) : |a n - (1 / 2 : ℝ) * ∫ ω, R n ω ∂μ| ≤
        ε * (d : ℝ) * ((N : ℝ) + 1) + C * ((N : ℝ) + 1) * s n := by
      have hb := (hsum σ hσ N hN z n).2
      rw [← hRint n] at hb
      have hlength : (⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * s n ≤ (N : ℝ) + 1 := by
        show (⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ≤ (N : ℝ) + 1
        exact_mod_cast dyadic_grid_length_le N n
      apply hb.trans
      calc
        _ = (ε * (d : ℝ)) * ((⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * s n) +
            (C * s n) * ((⌈N * (2 : ℝ≥0) ^ n⌉₊ : ℝ) * s n) := by
          simp only [s]
          ring
        _ ≤ (ε * (d : ℝ)) * ((N : ℝ) + 1) + (C * s n) * ((N : ℝ) + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left hlength (by positivity))
            (mul_le_mul_of_nonneg_left hlength (mul_nonneg hC (hs0 n)))
        _ = _ := by ring
    have hrhs : Tendsto (fun n : ℕ ↦ ε * (d : ℝ) * ((N : ℝ) + 1) +
        C * ((N : ℝ) + 1) * s n) atTop (𝓝 (ε * (d : ℝ) * ((N : ℝ) + 1))) := by
      simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (tendsto_const_nhds.mul hs)
    exact le_of_tendsto_of_tendsto' (continuous_abs.tendsto _ |>.comp hdiff) hrhs hboundn
  have hzero : |I - (1 / 2 : ℝ) * ∫ ω, J ω ∂μ| = 0 := by
    apply le_antisymm _ (abs_nonneg _)
    by_contra hpos
    have hpos : 0 < |I - (1 / 2 : ℝ) * ∫ ω, J ω ∂μ| := lt_of_not_ge hpos
    let K : ℝ := (d : ℝ) * ((N : ℝ) + 1)
    have hK : 0 ≤ K := by dsimp [K]; positivity
    let ε : ℝ := |I - (1 / 2 : ℝ) * ∫ ω, J ω ∂μ| / (2 * (K + 1))
    have hε : 0 < ε := by dsimp [ε]; positivity
    have heq : ε * (K + 1) = |I - (1 / 2 : ℝ) * ∫ ω, J ω ∂μ| / 2 := by dsimp [ε]; field_simp
    have hb := hI ε hε
    have hb' : |I - (1 / 2 : ℝ) * ∫ ω, J ω ∂μ| ≤ ε * K := by dsimp [K]; nlinarith [hb]
    nlinarith
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

end LatticeProb
