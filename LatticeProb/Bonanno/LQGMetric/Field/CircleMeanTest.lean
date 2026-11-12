import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Circle means of test functions

For `ψ : ℂ → ℝ` and `ε ∈ ℝ`, the circle mean
`circleMeanFun ψ ε x = (2π)⁻¹ ∫₀^{2π} ψ(x - ε e^{iθ}) dθ`
is the average of `ψ` over the circle of radius `|ε|` about `x`. It is the adjoint of the circle average of a
distribution: `∫ ψ(z) h_ε(z) dz = (h, circleMeanFun ψ ε)` for the circle-average process `h_ε` of `h`.

* `hasFDerivAt_circleSubIntegral`, `iteratedFDeriv_circleSubIntegral`: differentiation in `x` commutes with the
  circle integral `circleSubIntegral F ε x = ∫₀^{2π} F(x - ε e^{iθ}) dθ` of a smooth compactly supported `F`;
* `circleMeanTest φ ε ∈ 𝓓(ℂ)` for `φ ∈ 𝓓(ℂ)`, with `circleMeanTest φ 0 = φ`;
* `continuous_circleMeanTest`: `ε ↦ circleMeanTest φ ε` is continuous into `𝓓(ℂ)`;
* `tendsto_circleMeanTest_zero`: `circleMeanTest φ ε → φ` in `𝓓(ℂ)` as `ε → 0`.

The continuity clamps the radius to a compact interval, so that all the circle means are supported in one compact
set `K`, and applies `continuous_testFamK` in `𝓓_K`: the iterated derivatives
`D^i (circleMeanFun φ ε) = circleSubIntegral (D^i ((2π)⁻¹ φ)) ε` are jointly continuous in `(ε, x)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions Real

namespace LQGMetric

section circleSub

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- the circle integral `x ↦ ∫₀^{2π} F(x - ε e^{iθ}) dθ` (not normalised) -/
def circleSubIntegral (F : ℂ → E) (ε : ℝ) (x : ℂ) : E :=
  ∫ θ in (0 : ℝ)..2 * π, F (x - circleMap 0 ε θ)

theorem circleSubIntegral_eq_integral (F : ℂ → E) (ε : ℝ) (x : ℂ) :
    circleSubIntegral F ε x = ∫ θ in Ioc (0 : ℝ) (2 * π), F (x - circleMap 0 ε θ) := by
  rw [circleSubIntegral, intervalIntegral.integral_of_le (by positivity)]

omit [NormedSpace ℝ E] in
/-- the integrand vanishes when `x` is farther than `R + |ε|` from the origin and `F` lives in `closedBall 0 R` -/
theorem apply_sub_circleMap_eq_zero {F : ℂ → E} {R : ℝ} (hR : tsupport F ⊆ closedBall 0 R) {ε : ℝ} {x : ℂ}
    (hx : R + |ε| < ‖x‖) (θ : ℝ) : F (x - circleMap 0 ε θ) = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have h1 := hR hmem
  rw [mem_closedBall, dist_zero_right] at h1
  have h2 : ‖x‖ ≤ ‖x - circleMap 0 ε θ‖ + ‖circleMap 0 ε θ‖ := by
    simpa using norm_add_le (x - circleMap 0 ε θ) (circleMap 0 ε θ)
  rw [norm_circleMap_zero] at h2
  linarith

/-- a continuous linear map commutes with the circle integral -/
theorem circleSubIntegral_clm {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E]
    [CompleteSpace E']
    (L : E →L[ℝ] E') {F : ℂ → E} (hF : Continuous F) (ε : ℝ) (x : ℂ) :
    circleSubIntegral (fun z => L (F z)) ε x = L (circleSubIntegral F ε x) := by
  unfold circleSubIntegral
  exact L.intervalIntegral_comp_comm
    ((hF.comp (continuous_const.sub (continuous_circleMap 0 ε))).intervalIntegrable _ _)

/-- the circle integral of a continuous function is jointly continuous in the radius and the centre -/
theorem continuous_circleSubIntegral_uncurry {F : ℂ → E} (hF : Continuous F) :
    Continuous fun p : ℝ × ℂ => circleSubIntegral F p.1 p.2 := by
  unfold circleSubIntegral
  have hc : Continuous fun q : (ℝ × ℂ) × ℝ => q.1.2 - circleMap 0 q.1.1 q.2 := by
    simp only [circleMap]
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℝ × ℂ) (θ : ℝ) => F (p.2 - circleMap 0 p.1 θ)) (hF.comp hc) _ _

/-- **Differentiation under the circle integral.** -/
theorem hasFDerivAt_circleSubIntegral {F : ℂ → E} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (ε : ℝ) (x₀ : ℂ) :
    HasFDerivAt (circleSubIntegral F ε) (circleSubIntegral (fderiv ℝ F) ε x₀) x₀ := by
  have e : circleSubIntegral F ε = fun x => ∫ θ in Ioc (0 : ℝ) (2 * π), F (x - circleMap 0 ε θ) :=
    funext (circleSubIntegral_eq_integral F ε)
  rw [e, circleSubIntegral_eq_integral]
  have hg : Continuous (circleMap 0 ε) := continuous_circleMap 0 ε
  obtain ⟨C, hC⟩ := (hF.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hFc.fderiv (𝕜 := ℝ))
  obtain ⟨C0, hC0⟩ := hF.continuous.bounded_above_of_compact_support hFc
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := univ)
    (F := fun x θ => F (x - circleMap 0 ε θ)) (F' := fun x θ => fderiv ℝ F (x - circleMap 0 ε θ))
    (bound := fun _ => C) Filter.univ_mem ?_ ?_ ?_ ?_ (integrable_const C) ?_
  · exact Eventually.of_forall fun x =>
      (hF.continuous.comp (continuous_const.sub hg)).aestronglyMeasurable
  · exact (integrable_const C0).mono'
      (hF.continuous.comp (continuous_const.sub hg)).aestronglyMeasurable
      (ae_of_all _ fun θ => hC0 _)
  · exact ((hF.continuous_fderiv one_ne_zero).comp (continuous_const.sub hg)).aestronglyMeasurable
  · exact ae_of_all _ fun θ x _ => hC _
  · refine ae_of_all _ fun θ x _ => ?_
    have h1 : HasFDerivAt F (fderiv ℝ F (x - circleMap 0 ε θ)) (x - circleMap 0 ε θ) :=
      (hF.differentiable one_ne_zero _).hasFDerivAt
    have h2 := h1.comp x ((hasFDerivAt_id x).sub_const (circleMap 0 ε θ))
    simp only [ContinuousLinearMap.comp_id] at h2
    exact h2

variable [CompleteSpace E]

/-- **The iterated derivatives of a circle integral** are the circle integrals of the iterated derivatives. -/
theorem iteratedFDeriv_circleSubIntegral {F : ℂ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFc : HasCompactSupport F) (ε : ℝ) (i : ℕ) :
    iteratedFDeriv ℝ i (circleSubIntegral F ε) = circleSubIntegral (iteratedFDeriv ℝ i F) ε := by
  induction i with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
    funext x
    exact (circleSubIntegral_clm
      ((continuousMultilinearCurryFin0 ℝ ℂ E).symm.toContinuousLinearEquiv.toContinuousLinearMap)
      hF.continuous ε x).symm
  | succ i ih =>
    have hFi : ContDiff ℝ 1 (iteratedFDeriv ℝ i F) :=
      hF.iteratedFDeriv_right (by exact_mod_cast le_top)
    have hFic : HasCompactSupport (iteratedFDeriv ℝ i F) := hFc.iteratedFDeriv i
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    rw [Function.comp_apply, (hasFDerivAt_circleSubIntegral hFi hFic ε x).fderiv]
    exact (circleSubIntegral_clm
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => ℂ) E).symm.toContinuousLinearEquiv
        |>.toContinuousLinearMap) (hFi.continuous_fderiv one_ne_zero) ε x).symm

/-- the circle integral of a smooth compactly supported function is smooth -/
theorem contDiff_circleSubIntegral {F : ℂ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFc : HasCompactSupport F) (ε : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (circleSubIntegral F ε) := by
  refine contDiff_of_differentiable_iteratedFDeriv fun m _ => ?_
  rw [iteratedFDeriv_circleSubIntegral hF hFc ε m]
  exact fun x => (hasFDerivAt_circleSubIntegral (hF.iteratedFDeriv_right (by exact_mod_cast le_top))
    (hFc.iteratedFDeriv m) ε x).differentiableAt

end circleSub

/-! ### The circle mean -/

/-- the circle mean `circleMeanFun ψ ε x = (2π)⁻¹ ∫₀^{2π} ψ(x - ε e^{iθ}) dθ`, the average of `ψ` over the circle of
radius `|ε|` about `x` -/
def circleMeanFun (ψ : ℂ → ℝ) (ε : ℝ) (x : ℂ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ψ (x - circleMap 0 ε θ)

theorem circleMeanFun_eq (ψ : ℂ → ℝ) (ε : ℝ) :
    circleMeanFun ψ ε = circleSubIntegral (fun z => (2 * π)⁻¹ * ψ z) ε := by
  funext x
  simp only [circleMeanFun, circleSubIntegral, intervalIntegral.integral_const_mul]

/-- the circle mean of radius `0` is the identity -/
theorem circleMeanFun_zero (ψ : ℂ → ℝ) : circleMeanFun ψ 0 = ψ := by
  funext x
  simp only [circleMeanFun, circleMap_zero_radius, Function.const_apply, sub_zero,
    intervalIntegral.integral_const, smul_eq_mul]
  field_simp

theorem circleMeanFun_eq_zero {ψ : ℂ → ℝ} {R : ℝ} (hR : tsupport ψ ⊆ closedBall 0 R) {ε : ℝ} {x : ℂ}
    (hx : R + |ε| < ‖x‖) : circleMeanFun ψ ε x = 0 := by
  simp [circleMeanFun, apply_sub_circleMap_eq_zero hR hx]

theorem contDiff_circleMeanFun {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (ε : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (circleMeanFun ψ ε) := by
  rw [circleMeanFun_eq]
  exact contDiff_circleSubIntegral (contDiff_const.mul hψ)
    (hc.mono (Function.support_mul_subset_right _ _)) ε

theorem hasCompactSupport_circleMeanFun {ψ : ℂ → ℝ} (hc : HasCompactSupport ψ) (ε : ℝ) :
    HasCompactSupport (circleMeanFun ψ ε) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + |ε|)) fun x hx => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hx
  exact circleMeanFun_eq_zero hR hx

/-- the circle mean of a test function, as a test function -/
def circleMeanTest (φ : TestC) (ε : ℝ) : TestC :=
  ⟨circleMeanFun φ ε, contDiff_circleMeanFun φ.contDiff φ.hasCompactSupport ε,
    hasCompactSupport_circleMeanFun φ.hasCompactSupport ε, subset_univ _⟩

theorem circleMeanTest_apply (φ : TestC) (ε : ℝ) (x : ℂ) :
    circleMeanTest φ ε x = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, φ (x - circleMap 0 ε θ) :=
  rfl

theorem circleMeanTest_zero (φ : TestC) : circleMeanTest φ 0 = φ := by
  ext x
  show circleMeanFun φ 0 x = φ x
  rw [circleMeanFun_zero]

/-- **Continuity of the circle mean in the radius**: `ε ↦ circleMeanTest φ ε` is continuous at every `ε₀`, for the
topology of `𝓓(ℂ)`. -/
theorem continuousAt_circleMeanTest (φ : TestC) (ε₀ : ℝ) :
    ContinuousAt (fun ε => circleMeanTest φ ε) ε₀ := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set T : ℝ := |ε₀| + 1 with hT
  let p : ℝ → ℝ := fun ε => max (-T) (min ε T)
  have hT0 : 0 ≤ T := by positivity
  have hp : ∀ ε, |p ε| ≤ T := fun ε =>
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hpc : Continuous p := continuous_const.max (continuous_id.min continuous_const)
  let K : Compacts ℂ := ⟨closedBall 0 (R + T), isCompact_closedBall _ _⟩
  let Ψ : ℝ → ℂ → ℝ := fun ε => circleMeanFun φ (p ε)
  have hs : ∀ ε, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ ε) := fun ε =>
    contDiff_circleMeanFun φ.contDiff φ.hasCompactSupport (p ε)
  have hK : ∀ ε, ∀ y ∉ (K : Set ℂ), Ψ ε y = 0 := by
    intro ε y hy
    have h : y ∉ closedBall (0 : ℂ) (R + T) := hy
    rw [mem_closedBall, dist_zero_right, not_le] at h
    exact circleMeanFun_eq_zero hR (by linarith [hp ε])
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (2 * π)⁻¹ * φ z) := contDiff_const.mul φ.contDiff
  have hFc : HasCompactSupport (fun z => (2 * π)⁻¹ * φ z) :=
    φ.hasCompactSupport.mono (Function.support_mul_subset_right _ _)
  have hD : ∀ i : ℕ, Continuous fun q : ℝ × ℂ => iteratedFDeriv ℝ i (Ψ q.1) q.2 := by
    intro i
    have e : (fun q : ℝ × ℂ => iteratedFDeriv ℝ i (Ψ q.1) q.2) =
        fun q => circleSubIntegral (iteratedFDeriv ℝ i (fun z => (2 * π)⁻¹ * φ z)) (p q.1) q.2 := by
      funext q
      show iteratedFDeriv ℝ i (circleMeanFun φ (p q.1)) q.2 = _
      rw [circleMeanFun_eq, iteratedFDeriv_circleSubIntegral hF hFc]
    rw [e]
    exact (continuous_circleSubIntegral_uncurry
      (hF.continuous_iteratedFDeriv (by exact_mod_cast le_top))).comp
      ((hpc.comp continuous_fst).prodMk continuous_snd)
  have hcont : Continuous fun ε => ofSuppC K (testFamK K Ψ hs hK ε) :=
    (ofSuppC K).continuous.comp (continuous_testFamK K Ψ hs hK hD)
  refine hcont.continuousAt.congr ?_
  have hball : ball ε₀ 1 ∈ 𝓝 ε₀ := ball_mem_nhds _ one_pos
  filter_upwards [hball] with ε hε
  have hpe : p ε = ε := by
    rw [mem_ball, Real.dist_eq] at hε
    have h1 := abs_sub_abs_le_abs_sub ε ε₀
    have h2 : |ε| ≤ T := by linarith
    simp only [p]
    rw [min_eq_left ((le_abs_self ε).trans h2), max_eq_right (by linarith [neg_abs_le ε])]
  ext y
  show circleMeanFun φ (p ε) y = circleMeanFun φ ε y
  rw [hpe]

/-- `ε ↦ circleMeanTest φ ε` is continuous into `𝓓(ℂ)` -/
theorem continuous_circleMeanTest (φ : TestC) : Continuous fun ε => circleMeanTest φ ε :=
  continuous_iff_continuousAt.2 (continuousAt_circleMeanTest φ)

/-- **The circle means converge to the test function**: `circleMeanTest φ ε → φ` in `𝓓(ℂ)` as `ε → 0`. -/
theorem tendsto_circleMeanTest_zero (φ : TestC) :
    Tendsto (fun ε => circleMeanTest φ ε) (𝓝 0) (𝓝 φ) := by
  have h := (continuous_circleMeanTest φ).tendsto 0
  rwa [circleMeanTest_zero] at h

end LQGMetric
