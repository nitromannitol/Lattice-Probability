import Mathlib
import LatticeProb.WhiteNoise

/-!
# Space-time mollification of weak solutions of the heat equation

For the operator `L = (2d)⁻¹ Δ` of `LatticeProb.WhiteNoise.contOp` on `ℝ × ℝ ^ d`, a continuous weak
solution `u` of `∂_s u = L u` in an open set `U` is mollified by convolution with smooth nonnegative
kernels `ρ n` of integral one supported in the closed ball of radius `ε n`. Where the mollifier fits in
`U` the mollification is smooth, and testing the weak equation against the translated reflections
`q ↦ ρ n (p - q)` shows that it solves the heat equation there classically. As `ε n → 0` the
mollifications converge to `u` uniformly on compact subsets of `U`.

The general convolution facts are stated on a finite-dimensional normed space, since `ℝ × ℝ ^ d`
carries the sup norm and is not an inner product space.
-/

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
open LatticeProb.WhiteNoise

namespace LatticeProb.Heat

/-- `u` is a weak solution of `∂_s u = (2d)⁻¹ Δ u` in the open set `U`: the equation holds against every
smooth compactly supported test function with support in `U`. -/
def IsWeakHeat (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))) (u : ℝ × (Fin d → ℝ) → ℝ) : Prop :=
  ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    -∫ p : ℝ × (Fin d → ℝ), u p * deriv (fun s => ψ (s, p.2)) p.1
      = ∫ p : ℝ × (Fin d → ℝ), u p * contOp d (fun x => ψ (p.1, x)) p.2

/-- `u` is a classical solution of `∂_s u = (2d)⁻¹ Δ u` at every point of `U`. -/
def IsClassicalHeat (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))) (u : ℝ × (Fin d → ℝ) → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) u U ∧ ∀ p ∈ U, HasDerivAt (fun s => u (s, p.2))
    (contOp d (fun x => u (p.1, x)) p.2) p.1

section Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
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


end Convolution


section Heat

variable {d : ℕ}

/-- The time direction `(1, 0)` of `ℝ × ℝ ^ d`. -/
def timeDir (d : ℕ) : ℝ × (Fin d → ℝ) := (1, 0)

/-- The `i`-th space direction `(0, eᵢ)` of `ℝ × ℝ ^ d`. -/
def spaceDir (d : ℕ) (i : Fin d) : ℝ × (Fin d → ℝ) := (0, Pi.single i 1)

/-- The kernel `(2d)⁻¹ Σᵢ ∂²ᵢ ρ` of the operator `L` applied in the space variables. -/
noncomputable def spaceOp (d : ℕ) (ρ : ℝ × (Fin d → ℝ) → ℝ) (y : ℝ × (Fin d → ℝ)) : ℝ :=
  (∑ i : Fin d, fderiv ℝ (fun z => fderiv ℝ ρ z (spaceDir d i)) y (spaceDir d i)) / (2 * d)

theorem hasDerivAt_slice_time {F : ℝ × (Fin d → ℝ) → ℝ} (hF : Differentiable ℝ F) (s : ℝ)
    (x : Fin d → ℝ) : HasDerivAt (fun s => F (s, x)) (fderiv ℝ F (s, x) (timeDir d)) s :=
  (hF _).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))

theorem hasDerivAt_slice_space {F : ℝ × (Fin d → ℝ) → ℝ} (hF : Differentiable ℝ F) (s : ℝ)
    (x : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    HasDerivAt (fun t => F (s, Function.update x i t))
      (fderiv ℝ F (s, Function.update x i t) (spaceDir d i)) t :=
  (hF _).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t s).prodMk (hasDerivAt_update x i t))

/-- The Laplacian of a space slice of a smooth function is the sum of its second derivatives in
the space directions. -/
theorem lap_slice {F : ℝ × (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (s : ℝ) (x : Fin d → ℝ) :
    lap (fun x => F (s, x)) x =
      ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ F y (spaceDir d i)) (s, x) (spaceDir d i) := by
  unfold lap
  refine Finset.sum_congr rfl fun i _ => ?_
  show deriv (fun t => deriv (fun t' => F (s, Function.update x i t')) t) (x i) = _
  have h1 : (fun t => deriv (fun t' => F (s, Function.update x i t')) t) =
      fun t => fderiv ℝ F (s, Function.update x i t) (spaceDir d i) := by
    funext t
    exact (hasDerivAt_slice_space (hF.differentiable (by simp)) s x i t).deriv
  rw [h1]
  have hG : Differentiable ℝ (fun y => fderiv ℝ F y (spaceDir d i)) :=
    (contDiff_fderiv_apply hF _).differentiable (by simp)
  have h2 := hasDerivAt_slice_space hG s x i (x i)
  rw [Function.update_eq_self] at h2
  exact h2.deriv

/-- The Laplacian at `x` only depends on the function near `x`. -/
theorem lap_congr_of_eventuallyEq {φ₁ φ₂ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (h : φ₁ =ᶠ[𝓝 x] φ₂) : lap φ₁ x = lap φ₂ x := by
  unfold lap
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc := (hasDerivAt_update x i (x i)).continuousAt.tendsto
  rw [Function.update_eq_self] at hc
  have h1 : (fun t => φ₁ (Function.update x i t)) =ᶠ[𝓝 (x i)] fun t => φ₂ (Function.update x i t) :=
    h.comp_tendsto hc
  exact h1.deriv.deriv_eq

/-- The derivative of the reflection `q ↦ ρ (p - q)`. -/
theorem fderiv_comp_sub_left_apply {ρ : ℝ × (Fin d → ℝ) → ℝ} (hρ : Differentiable ℝ ρ)
    (p q v : ℝ × (Fin d → ℝ)) :
    fderiv ℝ (fun q => ρ (p - q)) q v = -fderiv ℝ ρ (p - q) v := by
  have h : HasFDerivAt (fun q => ρ (p - q))
      ((fderiv ℝ ρ (p - q)).comp (-ContinuousLinearMap.id ℝ (ℝ × (Fin d → ℝ)))) q :=
    (hρ _).hasFDerivAt.comp q ((hasFDerivAt_id q).const_sub p)
  rw [h.fderiv]
  simp

/-- The second derivatives of the reflection `q ↦ ρ (p - q)`. -/
theorem fderiv_fderiv_comp_sub_left_apply {ρ : ℝ × (Fin d → ℝ) → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (p q v w : ℝ × (Fin d → ℝ)) :
    fderiv ℝ (fun q => fderiv ℝ (fun q' => ρ (p - q')) q v) q w =
      fderiv ℝ (fun y => fderiv ℝ ρ y v) (p - q) w := by
  have h1 : (fun q => fderiv ℝ (fun q' => ρ (p - q')) q v) = fun q => -fderiv ℝ ρ (p - q) v := by
    funext q
    exact fderiv_comp_sub_left_apply (hρ.differentiable (by simp)) p q v
  rw [h1]
  have hD : Differentiable ℝ (fun y => fderiv ℝ ρ y v) :=
    (contDiff_fderiv_apply hρ v).differentiable (by simp)
  have h2 : (fun q => -fderiv ℝ ρ (p - q) v) = -(fun q => (fun y => fderiv ℝ ρ y v) (p - q)) := rfl
  rw [h2, fderiv_neg]
  simp [fderiv_comp_sub_left_apply hD p q w]

/-- A function vanishing outside `tsupport ρ` together with its derivatives vanishes at points of norm
larger than `ε` when `tsupport ρ ⊆ closedBall 0 ε`. -/
theorem fderiv_apply_eq_zero_of_lt {ρ : ℝ × (Fin d → ℝ) → ℝ} {ε : ℝ}
    (hsupp : tsupport ρ ⊆ closedBall 0 ε) {y : ℝ × (Fin d → ℝ)} (hy : ε < ‖y‖) (v) :
    fderiv ℝ ρ y v = 0 := by
  have hyt : y ∉ tsupport ρ := fun h => by
    have := hsupp h
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have : fderiv ℝ ρ y = 0 := by
    by_contra hne
    exact hyt (tsupport_fderiv_subset ℝ (subset_tsupport _ hne))
  rw [this]
  simp

theorem tsupport_fderiv_apply_subset {ρ : ℝ × (Fin d → ℝ) → ℝ} (v : ℝ × (Fin d → ℝ)) :
    tsupport (fun y => fderiv ℝ ρ y v) ⊆ tsupport ρ := by
  refine (closure_mono fun y hy => ?_).trans (tsupport_fderiv_subset ℝ)
  by_contra h
  rw [Function.notMem_support] at h
  apply hy
  show fderiv ℝ ρ y v = 0
  rw [h]
  simp

theorem spaceOp_eq_zero_of_lt {ρ : ℝ × (Fin d → ℝ) → ℝ} {ε : ℝ}
    (hsupp : tsupport ρ ⊆ closedBall 0 ε) {y : ℝ × (Fin d → ℝ)} (hy : ε < ‖y‖) :
    spaceOp d ρ y = 0 := by
  unfold spaceOp
  rw [Finset.sum_eq_zero fun i _ => ?_, zero_div]
  exact fderiv_apply_eq_zero_of_lt ((tsupport_fderiv_apply_subset _).trans hsupp) hy _

end Heat


section Main

variable {d : ℕ}

instance isAddHaarMeasure_volume_spaceTime :
    (volume : Measure (ℝ × (Fin d → ℝ))).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- A mollification of a continuous weak solution solves the heat equation classically at every
point `p` whose closed `ε`-ball lies in `U`. The weak equation tested against the reflection
`q ↦ ρ (p - q)` identifies the time derivative and the space operator of the mollification. -/
theorem heat_mollify_pde {U : Set (ℝ × (Fin d → ℝ))} (hU : IsOpen U) {u : ℝ × (Fin d → ℝ) → ℝ}
    (hu : ContinuousOn u U) (hweak : IsWeakHeat d U u) {ρ : ℝ × (Fin d → ℝ) → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hρs : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hsupp : tsupport ρ ⊆ closedBall 0 ε) (hρz : ∀ y, ε < ‖y‖ → ρ y = 0)
    {p : ℝ × (Fin d → ℝ)} (hp : closedBall p ε ⊆ U) :
    HasDerivAt (fun s => ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) (s, p.2))
      (contOp d (fun x => ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) (p.1, x))
        p.2) p.1 := by
  obtain ⟨η, hη, g, hg, hgu, hloc⟩ := exists_local_conv (μ := volume) hU hu hε hρz hp
  have hGs : ContDiff ℝ ∞ (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) :=
    hρc.contDiff_convolution_right _ hg.locallyIntegrable hρs
  have hev : (fun q => ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) q)
      =ᶠ[𝓝 p] (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) :=
    Filter.eventually_of_mem (ball_mem_nhds p hη) fun q hq => hloc q hq
  have hts : Tendsto (fun s : ℝ => ((s, p.2) : ℝ × (Fin d → ℝ))) (𝓝 p.1) (𝓝 p) := by
    have h := (continuous_id.prodMk continuous_const :
      Continuous fun s : ℝ => ((s, p.2) : ℝ × (Fin d → ℝ))).tendsto p.1
    simpa using h
  have hxs : Tendsto (fun x : Fin d → ℝ => ((p.1, x) : ℝ × (Fin d → ℝ))) (𝓝 p.2) (𝓝 p) := by
    have h := (continuous_const.prodMk continuous_id :
      Continuous fun x : Fin d → ℝ => ((p.1, x) : ℝ × (Fin d → ℝ))).tendsto p.2
    simpa using h
  have hlapeq : contOp d (fun x => ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ)
      (p.1, x)) p.2 = contOp d (fun x => (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) (p.1, x)) p.2 := by
    have h := lap_congr_of_eventuallyEq (hev.comp_tendsto hxs)
    unfold contOp
    exact congrArg (fun r => r / (2 * (d : ℝ))) h
  rw [hlapeq]
  refine HasDerivAt.congr_of_eventuallyEq ?_ (hev.comp_tendsto hts)
  have hderiv := hasDerivAt_slice_time (hGs.differentiable (by simp)) p.1 p.2
  refine hderiv.congr_deriv ?_
  -- the two sides as integrals against `g`
  have hconv : ∀ (F : ℝ × (Fin d → ℝ) → ℝ),
      (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] F) p = ∫ q, g q * F (p - q) := fun F => by
    rw [convolution_def]
    rfl
  have hug : ∀ F : ℝ × (Fin d → ℝ) → ℝ, (∀ y, ε < ‖y‖ → F y = 0) →
      ∫ q, u q * F (p - q) = ∫ q, g q * F (p - q) := fun F hF => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    by_cases hq : q ∈ closedBall p ε
    · show u q * F (p - q) = g q * F (p - q)
      rw [hgu hq]
    · have hlt : ε < ‖p - q‖ := by
        rw [mem_closedBall, dist_comm, dist_eq_norm, not_le] at hq
        exact hq
      show u q * F (p - q) = g q * F (p - q)
      rw [hF _ hlt, mul_zero, mul_zero]
  -- the weak equation tested against the reflection of `ρ`
  set ψ : ℝ × (Fin d → ℝ) → ℝ := fun q => ρ (p - q) with hψ_def
  have hψs : ContDiff ℝ ∞ ψ := hρs.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hρc.comp_homeomorph (Homeomorph.subLeft p)
  have hψU : tsupport ψ ⊆ U := by
    refine (closure_minimal (fun q hq => ?_) isClosed_closedBall).trans hp
    by_contra hqn
    rw [mem_closedBall, dist_eq_norm, not_le, ← norm_neg, neg_sub] at hqn
    exact hq (hρz _ hqn)
  have hw := hweak ψ hψs hψc hψU
  have htime : ∀ q : ℝ × (Fin d → ℝ), deriv (fun s => ψ (s, q.2)) q.1 =
      -fderiv ℝ ρ (p - q) (timeDir d) := fun q => by
    rw [(hasDerivAt_slice_time (hψs.differentiable (by simp)) q.1 q.2).deriv]
    exact fderiv_comp_sub_left_apply (hρs.differentiable (by simp)) p q _
  have hspace : ∀ q : ℝ × (Fin d → ℝ), contOp d (fun x => ψ (q.1, x)) q.2 =
      spaceOp d ρ (p - q) := fun q => by
    unfold contOp spaceOp
    rw [lap_slice hψs q.1 q.2]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact fderiv_fderiv_comp_sub_left_apply hρs p q _ _
  simp_rw [htime, hspace, mul_neg, integral_neg, neg_neg] at hw
  -- the time side
  have hT : fderiv ℝ (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) (p.1, p.2) (timeDir d)
      = ∫ q, g q * spaceOp d ρ (p - q) := by
    rw [Prod.mk.eta, fderiv_convolution_apply hg.locallyIntegrable hρs hρc, hconv,
      ← hug _ fun y hy => fderiv_apply_eq_zero_of_lt hsupp hy _, hw,
      hug _ fun y hy => spaceOp_eq_zero_of_lt hsupp hy]
  rw [hT]
  -- the space side
  unfold contOp
  rw [lap_slice hGs p.1 p.2, Prod.mk.eta]
  have hD : ∀ i : Fin d, fderiv ℝ (fun y => fderiv ℝ (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) y
      (spaceDir d i)) p (spaceDir d i) = ∫ q, g q *
        fderiv ℝ (fun z => fderiv ℝ ρ z (spaceDir d i)) (p - q) (spaceDir d i) := fun i => by
    have h1 : (fun y => fderiv ℝ (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) y (spaceDir d i)) =
        g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun z => fderiv ℝ ρ z (spaceDir d i) := by
      funext y
      exact fderiv_convolution_apply hg.locallyIntegrable hρs hρc y _
    rw [h1, fderiv_convolution_apply hg.locallyIntegrable (contDiff_fderiv_apply hρs _)
      (hρc.fderiv_apply ℝ _), hconv]
  simp_rw [hD]
  have hint : ∀ i : Fin d, Integrable (fun q => g q *
      fderiv ℝ (fun z => fderiv ℝ ρ z (spaceDir d i)) (p - q) (spaceDir d i)) := fun i =>
    ((hρc.fderiv_apply ℝ _).fderiv_apply ℝ _).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) hg.locallyIntegrable
      ((contDiff_fderiv_apply (contDiff_fderiv_apply hρs _) _).continuous) p |>.integrable
  unfold spaceOp
  simp_rw [mul_div_assoc']
  rw [integral_div, ← integral_finsetSum _ fun i _ => hint i]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp [Finset.mul_sum]

/-- **Space-time mollification of continuous weak solutions of the heat equation.** The
mollifications of a continuous weak solution of `∂_s u = (2d)⁻¹ Δ u` in `U` are classical solutions
on the set of points whose closed `ε n`-ball lies in `U`, and converge to `u` uniformly on compact
subsets of `U`. -/
theorem heat_mollify : ∀ (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))) (u : ℝ × (Fin d → ℝ) → ℝ) (ε : ℕ → ℝ)
    (ρ : ℕ → ℝ × (Fin d → ℝ) → ℝ), IsOpen U → ContinuousOn u U → IsWeakHeat d U u →
    (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ρ n) ∧ HasCompactSupport (ρ n) ∧
      tsupport (ρ n) ⊆ closedBall 0 (ε n) ∧ (∀ x, 0 ≤ ρ n x) ∧ ∫ x, ρ n x = 1) →
    (∀ n, IsClassicalHeat d {p | closedBall p (ε n) ⊆ U}
      (convolution (U.indicator u) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) volume)) ∧
    (∀ C : Set (ℝ × (Fin d → ℝ)), IsCompact C → C ⊆ U →
      TendstoUniformlyOn
        (fun n => convolution (U.indicator u) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) volume) u atTop C) := by
  intro d U u ε ρ hU hu hweak hε hεt hρ
  have hρz : ∀ n y, ε n < ‖y‖ → ρ n y = 0 := fun n y hy => by
    by_contra hne
    have h := (hρ n).2.2.1 (subset_tsupport _ hne)
    rw [mem_closedBall, dist_zero_right] at h
    linarith
  refine ⟨fun n => ⟨?_, fun p hp => ?_⟩, fun C hC hCU => ?_⟩
  · exact contDiffOn_mollify (μ := volume) hU hu (hε n) (hρ n).1 (hρ n).2.1 (hρz n)
  · exact heat_mollify_pde hU hu hweak (hε n) (hρ n).1 (hρ n).2.1 (hρ n).2.2.1 (hρz n) hp
  · exact tendstoUniformlyOn_mollify (μ := volume) hU hu hεt (fun n => (hρ n).1)
      (fun n => (hρ n).2.1) (fun n => (hρ n).2.2.2.1) (fun n => (hρ n).2.2.2.2) hρz hC hCU

end Main

end LatticeProb.Heat
