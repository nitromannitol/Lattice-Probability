import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Mollification of weak solutions of the Laplace equation

`IsWeakSolutionLaplace μ U u s` says that `u` is a weak solution of `Δ u = s` in `U`.
If `u` is continuous on the open set `U` and `s` is essentially bounded and measurable on `U`, then the
mollifications of `u` and `s` by a sequence of smooth nonnegative functions of integral one with
shrinking supports satisfy `Δ (u ⋆ ρ n) = s ⋆ ρ n` pointwise on the set of points whose
`ε n`-neighbourhood lies in `U`, the bound `|s ⋆ ρ n| ≤ M`, locally uniform convergence of
`u ⋆ ρ n` to `u` and local `L^p` convergence of `s ⋆ ρ n` to `s`, `1 ≤ p < ∞`.
-/

open MeasureTheory Metric Filter Topology Set
open scoped InnerProductSpace ContDiff Convolution
open Laplacian

namespace LatticeProb.PegdenSmart

/-- `u` is a weak solution of `Δ u = s` in `U`: `∫ u Δψ = ∫ s ψ` for every smooth function `ψ`
with compact support contained in `U`. -/
def IsWeakSolutionLaplace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (μ : Measure E) (U : Set E) (u s : E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∫ x, u x * Δ ψ x ∂μ = ∫ x, s x * ψ x ∂μ

section Convolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The convolution at `x` only depends on the values of the first function on the ball of radius `ε`
around `x`, if the second function vanishes outside the ball of radius `ε` around the origin. -/
theorem convolution_eq_of_eqOn {f₁ f₂ ρ : E → ℝ} {x : E} {ε : ℝ} (hρ : ∀ y, ε < ‖y‖ → ρ y = 0)
    (h : EqOn f₁ f₂ (closedBall x ε)) :
    (f₁ ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x = (f₂ ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x := by
  simp only [convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ closedBall x ε
  · simp [h ht]
  · have : ε < ‖x - t‖ := by
      rw [mem_closedBall, not_le, dist_eq_norm'] at ht
      exact ht
    simp [hρ _ this]

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The Laplacian of a function with `ρ = 0` outside the ball of radius `ε` vanishes there too. -/
theorem laplacian_eq_zero_of_eq_zero {ρ : E → ℝ} {ε : ℝ} (hρ : ∀ y, ε < ‖y‖ → ρ y = 0) {y : E}
    (hy : ε < ‖y‖) : Δ ρ y = 0 := by
  have hev : ρ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hy] with z hz
    exact hρ z hz
  rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
  simp

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The Laplacian commutes with the reflection `t ↦ x - t`. -/
theorem laplacian_comp_sub_left {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (x t : E) :
    Δ (fun t => ρ (x - t)) t = Δ ρ (x - t) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun t => ρ (x - t)) = (fun z => ρ (x + z)) ∘ ⇑(-(ContinuousLinearMap.id ℝ E)) := by
    funext t
    simp [sub_eq_add_neg]
  have hc : ContDiff ℝ ∞ (fun z => ρ (x + z)) := hρ.comp (contDiff_const.add contDiff_id)
  have h2 : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by simp
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc _ h2, iteratedFDeriv_comp_add_left]
  simp [iteratedFDeriv_two_apply, sub_eq_add_neg]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_fderiv_apply {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (v : E) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ ρ y v) :=
  (hρ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The directional derivative of a convolution with a smooth compactly supported function. -/
theorem fderiv_convolution_apply {g ρ : E → ℝ} (hg : LocallyIntegrable g μ) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (x v : E) :
    fderiv ℝ (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x v =
      (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] fun y => fderiv ℝ ρ y v) x := by
  have h1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have h := hρc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hg h1 x
  have hint := (hρc.fderiv (𝕜 := ℝ)).convolutionExists_right ((ContinuousLinearMap.mul ℝ ℝ).precompR E) hg
    (hρ.continuous_fderiv (by simp)) x
  rw [h.fderiv, convolution_def, convolution_def, ContinuousLinearMap.integral_apply hint]
  simp

/-- The second derivative of a convolution with a smooth compactly supported function. -/
theorem fderiv_fderiv_convolution_apply {g ρ : E → ℝ} (hg : LocallyIntegrable g μ)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (x w v : E) :
    fderiv ℝ (fderiv ℝ (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ)) x w v =
      (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] fun y => fderiv ℝ (fun y' => fderiv ℝ ρ y' v) y w) x := by
  set G := g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ with hGdef
  have hG : ContDiff ℝ ∞ G :=
    hρc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hg hρ
  have hd : DifferentiableAt ℝ (fderiv ℝ G) x :=
    (hG.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have h1 : fderiv ℝ (fderiv ℝ G) x w v = fderiv ℝ (fun y => fderiv ℝ G y v) x w := by
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  have h2 : (fun y => fderiv ℝ G y v) =
      g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] fun y => fderiv ℝ ρ y v := by
    funext y
    exact fderiv_convolution_apply hg hρ hρc y v
  rw [h1, h2]
  exact fderiv_convolution_apply hg (contDiff_fderiv_apply hρ v) (hρc.fderiv_apply (𝕜 := ℝ) v) x w

/-- The Laplacian of a convolution with a smooth compactly supported function. -/
theorem laplacian_convolution {g ρ : E → ℝ} (hg : LocallyIntegrable g μ) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (x : E) :
    Δ (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x = (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] Δ ρ) x := by
  set b := stdOrthonormalBasis ℝ E with hb
  have hΔρ : Δ ρ = fun y => ∑ i, fderiv ℝ (fun y' => fderiv ℝ ρ y' (b i)) y (b i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    funext y
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hd : DifferentiableAt ℝ (fderiv ℝ ρ) y :=
      (hρ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y
    rw [fderiv_clm_apply hd (differentiableAt_const (b i))]
    simp [hb]
  have hint : ∀ i, Integrable
      (fun t => g t * fderiv ℝ (fun y' => fderiv ℝ ρ y' (b i)) (x - t) (b i)) μ := by
    intro i
    have h := ((hρc.fderiv_apply (𝕜 := ℝ) (b i)).fderiv_apply (𝕜 := ℝ) (b i)).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) hg
      (contDiff_fderiv_apply (contDiff_fderiv_apply hρ (b i)) (b i)).continuous x
    simpa [ConvolutionExistsAt] using h
  rw [hΔρ, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [fderiv_fderiv_convolution_apply hg hρ hρc]
  simp only [convolution_def, ContinuousLinearMap.mul_apply', Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint i]

/-- Local structure of the mollification of a function that is continuous on an open set `U`: near a
point `x₀` whose `ε`-neighbourhood lies in `U` it coincides with the convolution of an integrable function
with the mollifier. -/
theorem exists_local_conv {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContinuousOn u U)
    {ρ : E → ℝ} {ε : ℝ} (hε : 0 < ε) (hρ : ∀ y, ε < ‖y‖ → ρ y = 0) {x₀ : E}
    (hx₀ : closedBall x₀ ε ⊆ U) :
    ∃ η > 0, ∃ g : E → ℝ, Integrable g μ ∧ EqOn g u (closedBall x₀ ε) ∧
      ∀ x ∈ ball x₀ η, ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x =
        (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x := by
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_closedBall x₀ ε).exists_thickening_subset_open hU hx₀
  rw [thickening_closedBall hδ hε.le] at hthick
  have hK : closedBall x₀ (ε + δ / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hthick
  refine ⟨δ / 2, half_pos hδ, (closedBall x₀ (ε + δ / 2)).indicator u, ?_, ?_, ?_⟩
  · exact (integrable_indicator_iff measurableSet_closedBall).mpr
      ((hu.mono hK).integrableOn_compact (isCompact_closedBall _ _))
  · intro t ht
    exact indicator_of_mem (closedBall_subset_closedBall (by linarith) ht) u
  · intro x hx
    refine convolution_eq_of_eqOn hρ fun t ht => ?_
    have htK : t ∈ closedBall x₀ (ε + δ / 2) := by
      rw [mem_closedBall] at ht ⊢
      have := mem_ball.mp hx
      linarith [dist_triangle t x x₀]
    rw [indicator_of_mem (hK htK), indicator_of_mem htK]

/-- The mollification of a function that is continuous on `U` is smooth on the set of points whose
`ε`-neighbourhood lies in `U`. -/
theorem contDiffOn_mollify {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContinuousOn u U)
    {ρ : E → ℝ} {ε : ℝ} (hε : 0 < ε) (hρs : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρ : ∀ y, ε < ‖y‖ → ρ y = 0) :
    ContDiffOn ℝ ∞ ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ)
      {x | closedBall x ε ⊆ U} := by
  refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
  obtain ⟨η, hη, g, hg, -, hloc⟩ := exists_local_conv (μ := μ) hU hu hε hρ hx₀
  refine ⟨ball x₀ η, isOpen_ball, mem_ball_self hη, ?_⟩
  have hG : ContDiff ℝ ∞ (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) :=
    hρc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hg.locallyIntegrable hρs
  exact hG.contDiffOn.congr fun x hx => hloc x hx.2

/-- The Laplacian of the mollification of a weak solution is the mollification of the right-hand
side. -/
theorem laplacian_mollify {U : Set E} (hU : IsOpen U) {u s : E → ℝ} (hu : ContinuousOn u U)
    {ρ : E → ℝ} {ε : ℝ} (hε : 0 < ε) (hρs : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρ : ∀ y, ε < ‖y‖ → ρ y = 0) (hweak : IsWeakSolutionLaplace μ U u s) {x₀ : E}
    (hx₀ : closedBall x₀ ε ⊆ U) :
    Δ ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x₀ =
      ((U.indicator s) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x₀ := by
  obtain ⟨η, hη, g, hg, hgu, hloc⟩ := exists_local_conv (μ := μ) hU hu hε hρ hx₀
  have hev : ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) =ᶠ[𝓝 x₀]
      (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) := by
    filter_upwards [ball_mem_nhds x₀ hη] with x hx using hloc x hx
  rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds,
    laplacian_convolution hg.locallyIntegrable hρs hρc]
  have hψ : ContDiff ℝ ∞ (fun t => ρ (x₀ - t)) := hρs.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun t => ρ (x₀ - t)) :=
    hρc.comp_homeomorph (Homeomorph.subLeft x₀)
  have hψU : tsupport (fun t => ρ (x₀ - t)) ⊆ U := by
    refine (closure_minimal (fun t ht => ?_) isClosed_closedBall).trans hx₀
    by_contra hnot
    rw [mem_closedBall, not_le, dist_eq_norm'] at hnot
    exact ht (hρ _ hnot)
  have h := hweak _ hψ hψc hψU
  simp only [laplacian_comp_sub_left hρs x₀] at h
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  have h1 : ∫ t, g t * Δ ρ (x₀ - t) ∂μ = ∫ t, u t * Δ ρ (x₀ - t) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ closedBall x₀ ε
    · simp only [hgu ht]
    · have : ε < ‖x₀ - t‖ := by
        rw [mem_closedBall, not_le, dist_eq_norm'] at ht
        exact ht
      simp [laplacian_eq_zero_of_eq_zero hρ this]
  have h2 : ∫ t, s t * ρ (x₀ - t) ∂μ = ∫ t, U.indicator s t * ρ (x₀ - t) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ closedBall x₀ ε
    · simp only [indicator_of_mem (hx₀ ht)]
    · have : ε < ‖x₀ - t‖ := by
        rw [mem_closedBall, not_le, dist_eq_norm'] at ht
        exact ht
      simp [hρ _ this]
  rw [h1, h, h2]

/-- A convolution with a nonnegative mollifier of integral one is bounded by any almost everywhere
bound of the function. -/
theorem abs_convolution_le {f ρ : E → ℝ} {M : ℝ} (hρ0 : ∀ y, 0 ≤ ρ y) (hρi : Integrable ρ μ)
    (hρ1 : ∫ y, ρ y ∂μ = 1) (hf : ∀ᵐ t ∂μ, |f t| ≤ M) (x : E) :
    |(f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x| ≤ M := by
  have hρx : Integrable (fun t => ρ (x - t)) μ := hρi.comp_sub_left x
  have hint : ∫ t, ρ (x - t) ∂μ = 1 := by rw [integral_sub_left_eq_self ρ μ x, hρ1]
  have hbound := norm_integral_le_of_norm_le (hρx.const_mul M)
    (f := fun t => f t * ρ (x - t)) (by
      filter_upwards [hf] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 _)]
      exact mul_le_mul_of_nonneg_right ht (hρ0 _))
  rw [integral_const_mul, hint, mul_one, Real.norm_eq_abs] at hbound
  simpa only [convolution_def, ContinuousLinearMap.mul_apply'] using hbound

/-- The mollification error at `x` is at most the oscillation of the function on the support of the
mollifier. -/
theorem abs_convolution_sub_le {g ρ : E → ℝ} {ε δ : ℝ} {x : E} (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ : ∀ y, ε < ‖y‖ → ρ y = 0) (hρi : Integrable ρ μ) (hρ1 : ∫ y, ρ y ∂μ = 1)
    (hgi : Integrable (fun t => g t * ρ (x - t)) μ)
    (h : ∀ t ∈ closedBall x ε, |g t - g x| ≤ δ) :
    |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x - g x| ≤ δ := by
  have hρx : Integrable (fun t => ρ (x - t)) μ := hρi.comp_sub_left x
  have hint : ∫ t, ρ (x - t) ∂μ = 1 := by rw [integral_sub_left_eq_self ρ μ x, hρ1]
  have h1 : (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x - g x =
      ∫ t, (g t - g x) * ρ (x - t) ∂μ := by
    simp only [convolution_def, ContinuousLinearMap.mul_apply']
    have : ∫ t, (g t - g x) * ρ (x - t) ∂μ =
        ∫ t, g t * ρ (x - t) ∂μ - ∫ t, g x * ρ (x - t) ∂μ := by
      simp only [sub_mul]
      exact integral_sub hgi (hρx.const_mul (g x))
    rw [this, integral_const_mul, hint, mul_one]
  rw [h1]
  have hbound := norm_integral_le_of_norm_le (hρx.const_mul δ)
    (f := fun t => (g t - g x) * ρ (x - t)) (Filter.Eventually.of_forall fun t => by
      by_cases ht : t ∈ closedBall x ε
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 _)]
        exact mul_le_mul_of_nonneg_right (h t ht) (hρ0 _)
      · have : ε < ‖x - t‖ := by
          rw [mem_closedBall, not_le, dist_eq_norm'] at ht
          exact ht
        simp [hρ _ this])
  rw [integral_const_mul, hint, mul_one, Real.norm_eq_abs] at hbound
  exact hbound

/-- Locally uniform convergence of the mollifications of a function that is continuous on `U`. -/
theorem tendstoUniformlyOn_mollify {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContinuousOn u U) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {ρ : ℕ → E → ℝ}
    (hρs : ∀ n, ContDiff ℝ ∞ (ρ n)) (hρc : ∀ n, HasCompactSupport (ρ n))
    (hρ0 : ∀ n y, 0 ≤ ρ n y) (hρ1 : ∀ n, ∫ y, ρ n y ∂μ = 1)
    (hρ : ∀ n y, ε n < ‖y‖ → ρ n y = 0) {C : Set E} (hC : IsCompact C) (hCU : C ⊆ U) :
    TendstoUniformlyOn (fun n => (U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) u atTop
      C := by
  obtain ⟨δ, hδ, hthick⟩ := hC.exists_thickening_subset_open hU hCU
  have hKU : cthickening (δ / 2) C ⊆ U :=
    (cthickening_subset_thickening' hδ (half_lt_self hδ) C).trans hthick
  have hK : IsCompact (cthickening (δ / 2) C) := hC.cthickening
  have huc := hK.uniformContinuousOn_of_continuous (hu.mono hKU)
  have hg : Integrable ((cthickening (δ / 2) C).indicator u) μ :=
    (integrable_indicator_iff hK.isClosed.measurableSet).mpr
      ((hu.mono hKU).integrableOn_compact hK)
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  obtain ⟨θ, hθ, hθu⟩ := Metric.uniformContinuousOn_iff.mp huc (e / 2) (half_pos he)
  have hev : ∀ᶠ n in atTop, ε n < min θ (δ / 2) :=
    hε.eventually (gt_mem_nhds (lt_min hθ (half_pos hδ)))
  filter_upwards [hev] with n hn x hx
  have hεn : ε n < θ := hn.trans_le (min_le_left _ _)
  have hεδ : ε n < δ / 2 := hn.trans_le (min_le_right _ _)
  have hxK : x ∈ cthickening (δ / 2) C := self_subset_cthickening C hx
  have hsub : closedBall x (ε n) ⊆ cthickening (δ / 2) C := fun t ht =>
    mem_cthickening_of_dist_le t x _ C hx ((mem_closedBall.mp ht).trans hεδ.le)
  have hconv : ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x =
      (((cthickening (δ / 2) C).indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x :=
    convolution_eq_of_eqOn (hρ n) fun t ht => by
      rw [indicator_of_mem (hKU (hsub ht)), indicator_of_mem (hsub ht)]
  have hρi : Integrable (ρ n) μ := (hρs n).continuous.integrable_of_hasCompactSupport (hρc n)
  have hgi : Integrable (fun t => (cthickening (δ / 2) C).indicator u t * ρ n (x - t)) μ := by
    have := (hρc n).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hg.locallyIntegrable
      (hρs n).continuous x
    simpa [ConvolutionExistsAt] using this
  have hbound := abs_convolution_sub_le (hρ0 n) (hρ n) hρi (hρ1 n) hgi (δ := e / 2)
    (fun t ht => by
      rw [indicator_of_mem (hsub ht), indicator_of_mem hxK, ← Real.dist_eq]
      exact (hθu t (hsub ht) x hxK ((mem_closedBall.mp ht).trans_lt hεn)).le)
  rw [indicator_of_mem hxK] at hbound
  rw [hconv, Real.dist_eq, abs_sub_comm]
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- Convolution is additive in the first argument (for a continuous compactly supported kernel). -/
theorem convolution_sub_left {φ ψ ρ : E → ℝ} (hφ : LocallyIntegrable φ μ)
    (hψ : LocallyIntegrable ψ μ) (hρc : HasCompactSupport ρ) (hρ : Continuous ρ) (x : E) :
    ((φ - ψ) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x =
      (φ ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x - (ψ ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x := by
  have h1 := hρc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hφ hρ x
  have h2 := hρc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hψ hρ x
  simp only [ConvolutionExistsAt, ContinuousLinearMap.mul_apply'] at h1 h2
  simp only [convolution_def, ContinuousLinearMap.mul_apply', Pi.sub_apply, sub_mul]
  exact integral_sub h1 h2

/-- Young's inequality in `L¹` for a nonnegative kernel of integral one. -/
theorem integral_abs_convolution_le {φ ρ : E → ℝ} (hφ : Integrable φ μ) (hρi : Integrable ρ μ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y ∂μ = 1) :
    ∫ x, |(φ ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x| ∂μ ≤ ∫ x, |φ x| ∂μ := by
  have h1 : Integrable (φ ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) μ :=
    hφ.integrable_convolution _ hρi
  have h2 : Integrable (fun x => |φ x|) μ := hφ.abs
  have h3 : Integrable ((fun x => |φ x|) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) μ :=
    h2.integrable_convolution _ hρi
  calc ∫ x, |(φ ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x| ∂μ
      ≤ ∫ x, ((fun x => |φ x|) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x ∂μ := by
        refine integral_mono h1.abs h3 fun x => ?_
        simp only [convolution_def, ContinuousLinearMap.mul_apply']
        calc |∫ t, φ t * ρ (x - t) ∂μ| = ‖∫ t, φ t * ρ (x - t) ∂μ‖ := (Real.norm_eq_abs _).symm
          _ ≤ ∫ t, ‖φ t * ρ (x - t)‖ ∂μ := norm_integral_le_integral_norm _
          _ = ∫ t, |φ t| * ρ (x - t) ∂μ := by
            congr 1
            funext t
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 _)]
    _ = ∫ x, |φ x| ∂μ := by
        rw [integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) h2 hρi, hρ1]
        simp

/-- Mollification converges in `L¹` for a continuous function with compact support. -/
theorem tendsto_integral_abs_mollify_sub_of_continuous {g : E → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {ρ : ℕ → E → ℝ}
    (hρc : ∀ n, HasCompactSupport (ρ n)) (hρcont : ∀ n, Continuous (ρ n))
    (hρ0 : ∀ n y, 0 ≤ ρ n y) (hρ1 : ∀ n, ∫ y, ρ n y ∂μ = 1)
    (hρ : ∀ n y, ε n < ‖y‖ → ρ n y = 0) :
    Tendsto (fun n => ∫ x, |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x| ∂μ) atTop
      (𝓝 0) := by
  have hS : IsCompact (cthickening (1 : ℝ) (tsupport g)) := hgc.cthickening
  have hK₂ : IsCompact (cthickening (2 : ℝ) (tsupport g)) := hgc.cthickening
  have hgi : Integrable g μ := hg.integrable_of_hasCompactSupport hgc
  have huc := hK₂.uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.tendsto_nhds]
  intro e he
  set V : ℝ := (μ (cthickening (1 : ℝ) (tsupport g))).toReal with hVdef
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hη : 0 < e / (2 * (V + 1)) := by positivity
  obtain ⟨θ, hθ, hθu⟩ := Metric.uniformContinuousOn_iff.mp huc _ hη
  have hev : ∀ᶠ n in atTop, ε n < min θ 1 := hε.eventually (gt_mem_nhds (lt_min hθ one_pos))
  filter_upwards [hev] with n hn
  have hεn : ε n < θ := hn.trans_le (min_le_left _ _)
  have hε1 : ε n < 1 := hn.trans_le (min_le_right _ _)
  have hρi : Integrable (ρ n) μ := (hρcont n).integrable_of_hasCompactSupport (hρc n)
  have hint : Integrable (fun x => |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x|) μ :=
    ((hgi.integrable_convolution _ hρi).sub hgi).abs
  have hpt : ∀ x, |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x| ≤
      (cthickening (1 : ℝ) (tsupport g)).indicator (fun _ => e / (2 * (V + 1))) x := by
    intro x
    by_cases hx : x ∈ cthickening (1 : ℝ) (tsupport g)
    · rw [indicator_of_mem hx]
      have hxK : x ∈ cthickening (2 : ℝ) (tsupport g) := cthickening_mono (by norm_num) _ hx
      refine abs_convolution_sub_le (hρ0 n) (hρ n) hρi (hρ1 n) ?_ fun t ht => ?_
      · have := (hρc n).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
          hgi.locallyIntegrable (hρcont n) x
        simpa [ConvolutionExistsAt] using this
      · have htK : t ∈ cthickening (2 : ℝ) (tsupport g) := by
          have h1 : t ∈ cthickening (ε n) (cthickening (1 : ℝ) (tsupport g)) :=
            mem_cthickening_of_dist_le t x _ _ hx (mem_closedBall.mp ht)
          have h2 := cthickening_cthickening_subset (s := tsupport g) (ε := ε n) (δ := 1)
            (dist_nonneg.trans (mem_closedBall.mp ht)) zero_le_one h1
          exact cthickening_mono (by linarith) _ h2
        have := hθu t htK x hxK ((mem_closedBall.mp ht).trans_lt hεn)
        rw [Real.dist_eq] at this
        exact this.le
    · rw [indicator_of_notMem hx]
      have hgx : g x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hx (self_subset_cthickening _ h)
      have hconv : (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x = 0 := by
        simp only [convolution_def, ContinuousLinearMap.mul_apply']
        refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
        by_cases ht : g t = 0
        · simp [ht]
        · have htS : t ∈ tsupport g := subset_tsupport _ ht
          have h1 : 1 < ‖x - t‖ := by
            rw [← dist_eq_norm]
            by_contra hle
            exact hx (mem_cthickening_of_dist_le x t 1 _ htS (not_lt.mp hle))
          simp [hρ n _ (hε1.trans h1)]
      simp [hgx, hconv]
  have hbound : ∫ x, |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x| ∂μ ≤
      e / (2 * (V + 1)) * V := by
    calc _ ≤ ∫ x, (cthickening (1 : ℝ) (tsupport g)).indicator
          (fun _ => e / (2 * (V + 1))) x ∂μ :=
          integral_mono hint ((integrable_indicator_iff hS.isClosed.measurableSet).mpr
            (integrableOn_const hS.measure_lt_top.ne)) hpt
      _ = e / (2 * (V + 1)) * V := by
          rw [integral_indicator_const _ hS.isClosed.measurableSet]
          simp [Measure.real, hVdef, mul_comm]
  have hnn : 0 ≤ ∫ x, |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x| ∂μ :=
    integral_nonneg fun x => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  refine hbound.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- Mollification converges in `L¹` for an integrable function. -/
theorem tendsto_integral_abs_mollify_sub {h : E → ℝ} (hh : Integrable h μ) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) {ρ : ℕ → E → ℝ} (hρc : ∀ n, HasCompactSupport (ρ n))
    (hρcont : ∀ n, Continuous (ρ n)) (hρ0 : ∀ n y, 0 ≤ ρ n y) (hρ1 : ∀ n, ∫ y, ρ n y ∂μ = 1)
    (hρ : ∀ n y, ε n < ‖y‖ → ρ n y = 0) :
    Tendsto (fun n => ∫ x, |(h ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - h x| ∂μ) atTop
      (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨g, hgc, hg1, hgcont, hgmem⟩ := MemLp.exists_hasCompactSupport_eLpNorm_sub_le
    (μ := μ) (p := 1) ENNReal.one_ne_top (memLp_one_iff_integrable.mpr hh)
    (ε := ENNReal.ofReal (e / 4)) (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hgi : Integrable g μ := hgcont.integrable_of_hasCompactSupport hgc
  have hsub : Integrable (h - g) μ := hh.sub hgi
  have hN0 : ∫ x, |h x - g x| ∂μ ≤ e / 4 := by
    have h1 : ENNReal.ofReal (∫ x, ‖(h - g) x‖ ∂μ) = eLpNorm (h - g) 1 μ := by
      rw [ofReal_integral_norm_eq_lintegral_enorm hsub, eLpNorm_one_eq_lintegral_enorm]
      exact hsub.aestronglyMeasurable
    rw [← h1] at hg1
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hg1
    simpa [Real.norm_eq_abs] using this
  have hR2 := tendsto_integral_abs_mollify_sub_of_continuous (μ := μ) hgcont hgc hε hρc hρcont
    hρ0 hρ1 hρ
  have hev := (Metric.tendsto_nhds.mp hR2) (e / 4) (by positivity)
  filter_upwards [hev] with n hn
  have hρi : Integrable (ρ n) μ := (hρcont n).integrable_of_hasCompactSupport (hρc n)
  have hconvh := hh.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hρi
  have hconvg := hgi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hρi
  have hconvhg := hsub.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hρi
  have hb : ∫ x, |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x| ∂μ < e / 4 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)] at hn
    exact hn
  have hpt : ∀ x, |(h ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - h x| ≤
      |((h - g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x| +
        |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x| + |h x - g x| := by
    intro x
    have e1 := convolution_sub_left (μ := μ) hh.locallyIntegrable hgi.locallyIntegrable (hρc n)
      (hρcont n) x
    have e2 : (h ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - h x =
        ((h - g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x +
          ((g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x) + (g x - h x) := by
      rw [e1]
      ring
    rw [e2]
    calc _ ≤ |((h - g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x| +
        |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x| + |g x - h x| := abs_add_three _ _ _
      _ = _ := by rw [abs_sub_comm (g x) (h x)]
  have hint1 : Integrable (fun x => |((h - g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x|) μ :=
    hconvhg.abs
  have hint2 : Integrable
      (fun x => |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x|) μ := (hconvg.sub hgi).abs
  have hint3 : Integrable (fun x => |h x - g x|) μ := (hh.sub hgi).abs
  have hint0 : Integrable
      (fun x => |(h ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - h x|) μ := (hconvh.sub hh).abs
  have hy := integral_abs_convolution_le hsub hρi (hρ0 n) (hρ1 n)
  have hsum : ∫ x, |(h ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - h x| ∂μ ≤
      ∫ x, (|((h - g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x| +
        |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x| + |h x - g x|) ∂μ :=
    integral_mono hint0 ((hint1.add hint2).add hint3) hpt
  have hI12 : Integrable (fun x => |((h - g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x| +
      |(g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - g x|) μ := hint1.add hint2
  rw [integral_add hI12 hint3, integral_add hint1 hint2] at hsum
  have hy' : ∫ x, |((h - g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x| ∂μ ≤ e / 4 := by
    refine hy.trans ?_
    simpa using hN0
  have hnn : 0 ≤ ∫ x, |(h ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - h x| ∂μ :=
    integral_nonneg fun x => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] in
/-- An `L^p` norm of an essentially bounded function is controlled by its `L¹` norm. -/
theorem eLpNorm_le_of_ae_bound {f : E → ℝ} {A : ℝ} (hA : 0 ≤ A) (hfm : AEStronglyMeasurable f μ)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ A)
    {p : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) :
    eLpNorm f p μ ≤ (ENNReal.ofReal (A ^ (p.toReal - 1)) * ∫⁻ x, ‖f x‖ₑ ∂μ) ^ (1 / p.toReal) := by
  have hq : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp hp1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (zero_lt_one.trans_le hp1).ne' hp hfm]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  calc ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (A ^ (p.toReal - 1)) * ‖f x‖ₑ ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hf] with x hx
        rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : |f x| ^ p.toReal = |f x| ^ (p.toReal - 1) * |f x| := by
          rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith), sub_add_cancel]
        rw [h1]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (abs_nonneg _) hx (by linarith)) (abs_nonneg _)
    _ = ENNReal.ofReal (A ^ (p.toReal - 1)) * ∫⁻ x, ‖f x‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Local `L^p` convergence of the mollifications of an essentially bounded measurable function. -/
theorem tendsto_eLpNorm_mollify_sub {U : Set E} (hU : IsOpen U) {s : E → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hs : ∀ᵐ x ∂μ.restrict U, |s x| ≤ M) (hsm : AEStronglyMeasurable s (μ.restrict U))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {ρ : ℕ → E → ℝ}
    (hρc : ∀ n, HasCompactSupport (ρ n)) (hρcont : ∀ n, Continuous (ρ n))
    (hρ0 : ∀ n y, 0 ≤ ρ n y) (hρ1 : ∀ n, ∫ y, ρ n y ∂μ = 1)
    (hρ : ∀ n y, ε n < ‖y‖ → ρ n y = 0) {C : Set E} (hC : IsCompact C) (hCU : C ⊆ U)
    {p : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) :
    Tendsto (fun n => eLpNorm (C.indicator fun x =>
      ((U.indicator s) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - s x) p μ) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hthick⟩ := hC.exists_thickening_subset_open hU hCU
  have hK : IsCompact (cthickening (δ / 2) C) := hC.cthickening
  have hKU : cthickening (δ / 2) C ⊆ U :=
    (cthickening_subset_thickening' hδ (half_lt_self hδ) C).trans hthick
  have hhi : Integrable ((cthickening (δ / 2) C).indicator s) μ := by
    refine Integrable.mono' ((integrable_indicator_iff hK.isClosed.measurableSet).mpr
      (integrableOn_const hK.measure_lt_top.ne) : Integrable
        ((cthickening (δ / 2) C).indicator fun _ => M) μ)
      ((aestronglyMeasurable_indicator_iff hK.isClosed.measurableSet).mpr
        (hsm.mono_measure (Measure.restrict_mono hKU le_rfl))) ?_
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hs] with x hx
    by_cases hxK : x ∈ cthickening (δ / 2) C
    · rw [indicator_of_mem hxK, indicator_of_mem hxK, Real.norm_eq_abs]
      exact hx (hKU hxK)
    · rw [indicator_of_notMem hxK, indicator_of_notMem hxK]
      simp
  have hL1 := tendsto_integral_abs_mollify_sub hhi hε hρc hρcont hρ0 hρ1 hρ
  set q := p.toReal with hq
  have hq1 : 1 ≤ q := by simpa using ENNReal.toReal_mono hp hp1
  have hsU : ∀ᵐ t ∂μ, |(U.indicator s) t| ≤ M := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hs] with t ht
    by_cases htU : t ∈ U
    · rw [indicator_of_mem htU]
      exact ht htU
    · rw [indicator_of_notMem htU]
      simpa using hM
  have hsC : ∀ᵐ x ∂μ, x ∈ C → |s x| ≤ M := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hs] with x hx hxC using hx (hCU hxC)
  have hup : Tendsto (fun n => (ENNReal.ofReal ((2 * M) ^ (q - 1)) *
      ENNReal.ofReal (∫ x, |((cthickening (δ / 2) C).indicator s ⋆[ContinuousLinearMap.mul ℝ ℝ, μ]
        ρ n) x - (cthickening (δ / 2) C).indicator s x| ∂μ)) ^ (1 / q)) atTop (𝓝 0) := by
    have h1 := ENNReal.tendsto_ofReal hL1
    rw [ENNReal.ofReal_zero] at h1
    have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((2 * M) ^ (q - 1))) h1
      (Or.inr ENNReal.ofReal_ne_top)
    have h3 := ((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto _).comp h2
    rw [mul_zero, ENNReal.zero_rpow_of_pos (show 0 < 1 / q by positivity)] at h3
    exact h3
  have hev : ∀ᶠ n in atTop, ε n < δ / 2 := hε.eventually (gt_mem_nhds (half_pos hδ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Filter.Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [hev] with n hn
  have hρi : Integrable (ρ n) μ := (hρcont n).integrable_of_hasCompactSupport (hρc n)
  have hconv := (hhi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hρi)
  have hdiff : Integrable (fun x => ((cthickening (δ / 2) C).indicator s ⋆[
      ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - (cthickening (δ / 2) C).indicator s x) μ :=
    hconv.sub hhi
  have hD : (C.indicator fun x => ((U.indicator s) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x -
      s x) = C.indicator fun x => ((cthickening (δ / 2) C).indicator s ⋆[
        ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - (cthickening (δ / 2) C).indicator s x := by
    funext x
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      have hxK : x ∈ cthickening (δ / 2) C := self_subset_cthickening C hx
      have hsub : closedBall x (ε n) ⊆ cthickening (δ / 2) C := fun t ht =>
        mem_cthickening_of_dist_le t x _ C hx ((mem_closedBall.mp ht).trans (hn.le))
      rw [convolution_eq_of_eqOn (f₂ := (cthickening (δ / 2) C).indicator s) (hρ n) fun t ht => by
        rw [indicator_of_mem (hKU (hsub ht)), indicator_of_mem (hsub ht)], indicator_of_mem hxK]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  rw [hD]
  have hmeas : AEStronglyMeasurable (C.indicator fun x => ((cthickening (δ / 2) C).indicator s ⋆[
      ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - (cthickening (δ / 2) C).indicator s x) μ :=
    hdiff.aestronglyMeasurable.indicator hC.isClosed.measurableSet
  have hbound : ∀ᵐ x ∂μ, |(C.indicator fun x => ((cthickening (δ / 2) C).indicator s ⋆[
      ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - (cthickening (δ / 2) C).indicator s x) x| ≤
      2 * M := by
    rw [← hD]
    filter_upwards [hsC] with x hx
    by_cases hxC : x ∈ C
    · rw [indicator_of_mem hxC]
      calc _ ≤ |((U.indicator s) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x| + |s x| :=
            abs_sub _ _
        _ ≤ M + M := add_le_add (abs_convolution_le (hρ0 n) hρi (hρ1 n) hsU x) (hx hxC)
        _ = 2 * M := by ring
    · rw [indicator_of_notMem hxC]
      simpa using (by linarith : 0 ≤ 2 * M)
  refine (eLpNorm_le_of_ae_bound (by linarith) hmeas hbound hp1 hp).trans ?_
  refine ENNReal.rpow_le_rpow (mul_le_mul' le_rfl ?_) (by positivity)
  calc ∫⁻ x, ‖(C.indicator fun x => ((cthickening (δ / 2) C).indicator s ⋆[
        ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - (cthickening (δ / 2) C).indicator s x) x‖ₑ ∂μ
      ≤ ∫⁻ x, ‖(((cthickening (δ / 2) C).indicator s ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x -
        (cthickening (δ / 2) C).indicator s x)‖ₑ ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hxC : x ∈ C
        · rw [indicator_of_mem hxC]
        · rw [indicator_of_notMem hxC]
          simp
    _ = ENNReal.ofReal (∫ x, |((cthickening (δ / 2) C).indicator s ⋆[
        ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x - (cthickening (δ / 2) C).indicator s x| ∂μ) := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm hdiff]
        simp [Real.norm_eq_abs]

end Convolution

/-- Mollification of a weak solution of `Δ u = s` in an open set `U`, with `u` continuous on `U` and `s`
measurable with `|s| ≤ M` almost everywhere on `U`. For a sequence `ρ n` of smooth nonnegative functions
of integral one with support in the ball of radius `ε n → 0`, the mollifications `u ⋆ ρ n` and `s ⋆ ρ n`
(computed from the values on `U`) satisfy: `u ⋆ ρ n` is smooth and `Δ (u ⋆ ρ n) = s ⋆ ρ n` on
`{x | closedBall x (ε n) ⊆ U}`; `|s ⋆ ρ n| ≤ M`; `u ⋆ ρ n → u` uniformly on compact subsets of `U`;
`s ⋆ ρ n → s` in `L^p` on compact subsets of `U`, `1 ≤ p < ∞`. -/
theorem weakLaplace_mollify {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (U : Set E) (u s : E → ℝ) (M : ℝ) (ε : ℕ → ℝ) (ρ : ℕ → E → ℝ)
    (hU : IsOpen U) (hu : ContinuousOn u U) (hM : 0 ≤ M) (hs : ∀ᵐ x ∂μ.restrict U, |s x| ≤ M)
    (hsm : AEStronglyMeasurable s (μ.restrict U)) (hweak : IsWeakSolutionLaplace μ U u s)
    (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hρ : ∀ n, ContDiff ℝ ∞ (ρ n) ∧ HasCompactSupport (ρ n) ∧
      tsupport (ρ n) ⊆ closedBall 0 (ε n) ∧ (∀ x, 0 ≤ ρ n x) ∧ ∫ x, ρ n x ∂μ = 1) :
    (∀ n, ContDiffOn ℝ ∞ (convolution (U.indicator u) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) μ)
        {x | closedBall x (ε n) ⊆ U}) ∧
    (∀ n, ∀ x ∈ {x | closedBall x (ε n) ⊆ U},
      Δ (convolution (U.indicator u) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) μ) x =
        convolution (U.indicator s) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) μ x) ∧
    (∀ n x, |convolution (U.indicator s) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) μ x| ≤ M) ∧
    (∀ C : Set E, IsCompact C → C ⊆ U →
      TendstoUniformlyOn
        (fun n => convolution (U.indicator u) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) μ) u atTop C) ∧
    (∀ p : ENNReal, 1 ≤ p → p ≠ ⊤ → ∀ C : Set E, IsCompact C → C ⊆ U →
      Tendsto (fun n => eLpNorm (C.indicator fun x =>
        convolution (U.indicator s) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) μ x - s x) p μ)
        atTop (𝓝 0)) := by
  have hρs : ∀ n, ContDiff ℝ ∞ (ρ n) := fun n => (hρ n).1
  have hρc : ∀ n, HasCompactSupport (ρ n) := fun n => (hρ n).2.1
  have hρ0 : ∀ n y, 0 ≤ ρ n y := fun n y => (hρ n).2.2.2.1 y
  have hρ1 : ∀ n, ∫ y, ρ n y ∂μ = 1 := fun n => (hρ n).2.2.2.2
  have hρz : ∀ n y, ε n < ‖y‖ → ρ n y = 0 := fun n y hy =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := (hρ n).2.2.1 h
      rw [mem_closedBall, dist_zero_right] at this
      linarith
  have hρcont : ∀ n, Continuous (ρ n) := fun n => (hρs n).continuous
  have hsU : ∀ᵐ t ∂μ, |(U.indicator s) t| ≤ M := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hs] with t ht
    by_cases htU : t ∈ U
    · rw [indicator_of_mem htU]
      exact ht htU
    · rw [indicator_of_notMem htU]
      simpa using hM
  refine ⟨fun n => contDiffOn_mollify hU hu (hε0 n) (hρs n) (hρc n) (hρz n),
    fun n x hx => laplacian_mollify hU hu (hε0 n) (hρs n) (hρc n) (hρz n) hweak hx,
    fun n x => abs_convolution_le (hρ0 n)
      ((hρcont n).integrable_of_hasCompactSupport (hρc n)) (hρ1 n) hsU x,
    fun C hC hCU => tendstoUniformlyOn_mollify hU hu hε hρs hρc hρ0 hρ1 hρz hC hCU,
    fun p hp1 hp C hC hCU => tendsto_eLpNorm_mollify_sub hU hM hs hsm hε hρc hρcont hρ0 hρ1 hρz
      hC hCU hp1 hp⟩

end LatticeProb.PegdenSmart
