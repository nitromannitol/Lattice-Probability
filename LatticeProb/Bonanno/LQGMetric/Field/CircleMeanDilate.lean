import LatticeProb.Bonanno.LQGMetric.Field.CircleMeanTest
import LatticeProb.Bonanno.LQGMetric.Field.AffinePullScale

/-!
# Circle means of affine pullbacks of test functions

For a test function `φ ∈ 𝓓(ℂ)` and `z ∈ ℂ`, the circle mean of radius `ε` of the affine pullback
`testAffinePull r z φ = φ((· - z)/r)` depends jointly continuously on `(r, ε)`, for `r ≠ 0`, in the topology of `𝓓(ℂ)`.

* `continuous_circleSubIntegral_family`: the circle integral `∫₀^{2π} G_x(c_x - ρ_x e^{iθ}) dθ` of a jointly continuous
  family is continuous in the parameter;
* `continuousAt_circleMeanTest_testAffinePull`: `(r, ε) ↦ circleMeanTest (testAffinePull r z φ) ε` is continuous at
  every `(r₀, ε₀)` with `r₀ ≠ 0`;
* `continuousAt_circleMeanTest_dilate`: the same for the dilations `(s, ε) ↦ circleMeanTest (φ(s(· - z))) ε`, `s₀ ≠ 0`.

As for each factor separately, the proof clamps both parameters to a compact neighbourhood, so that all the functions
are supported in one compact set `K`, and applies `continuous_testFamK` in `𝓓_K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions Real

namespace LQGMetric

/-- the circle integral of a jointly continuous family, with continuously varying radius and centre, is continuous -/
theorem continuous_circleSubIntegral_family {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : X → ℂ → E} (hG : Continuous (Function.uncurry G)) {ρ : X → ℝ} (hρ : Continuous ρ)
    {c : X → ℂ} (hc : Continuous c) : Continuous fun x => circleSubIntegral (G x) (ρ x) (c x) := by
  unfold circleSubIntegral
  have h1 : Continuous fun y : X × ℝ => circleMap 0 (ρ y.1) y.2 := by
    simp only [circleMap]
    exact continuous_const.add ((Complex.continuous_ofReal.comp (hρ.comp continuous_fst)).mul
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))
  have h2 : Continuous fun y : X × ℝ => (y.1, c y.1 - circleMap 0 (ρ y.1) y.2) :=
    continuous_fst.prodMk ((hc.comp continuous_fst).sub h1)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : X) (θ : ℝ) => G x (c x - circleMap 0 (ρ x) θ)) (hG.comp h2) _ _

/-- a variant of `circleMeanFun_eq_zero` for a function vanishing outside `closedBall 0 R` -/
theorem circleMeanFun_eq_zero_of_forall {ψ : ℂ → ℝ} {R : ℝ} (hψ : ∀ y, R < ‖y‖ → ψ y = 0) {ε : ℝ} {x : ℂ}
    (hx : R + |ε| < ‖x‖) : circleMeanFun ψ ε x = 0 := by
  have h : ∀ θ, ψ (x - circleMap 0 ε θ) = 0 := fun θ => hψ _ (by
    have h2 : ‖x‖ ≤ ‖x - circleMap 0 ε θ‖ + ‖circleMap 0 ε θ‖ := by
      simpa using norm_add_le (x - circleMap 0 ε θ) (circleMap 0 ε θ)
    rw [norm_circleMap_zero] at h2
    linarith)
  simp [circleMeanFun, h]

/-- **Joint continuity of the circle means of the affine pullbacks.** For `φ ∈ 𝓓(ℂ)`, `z ∈ ℂ` and `r₀ ≠ 0`, the map
`(r, ε) ↦ circleMeanTest (testAffinePull r z φ) ε` into `𝓓(ℂ)` is continuous at `(r₀, ε₀)`. -/
theorem continuousAt_circleMeanTest_testAffinePull (φ : TestC) (z : ℂ) {r₀ : ℝ} (hr₀ : r₀ ≠ 0) (ε₀ : ℝ) :
    ContinuousAt (fun a : ℝ × ℝ => circleMeanTest (testAffinePull a.1 z φ) a.2) (r₀, ε₀) := by
  obtain ⟨ρ, hρ⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set ρ' := max ρ 0 with hρ'
  have hsupp : tsupport φ ⊆ closedBall (0 : ℂ) ρ' :=
    hρ.trans (closedBall_subset_closedBall (le_max_left _ _))
  set p := scaleClamp r₀ with hp
  have hp_lo : ∀ r, |r₀| / 2 ≤ |p r| := half_abs_le_abs_scaleClamp r₀
  have hp_hi : ∀ r, |p r| ≤ 3 * |r₀| / 2 := abs_scaleClamp_le r₀
  have ha : 0 < |r₀| := abs_pos.2 hr₀
  have hp0 : ∀ r, p r ≠ 0 := fun r h => by
    have := hp_lo r
    rw [h, abs_zero] at this
    linarith
  set T : ℝ := |ε₀| + 1 with hT
  have hT0 : 0 ≤ T := by positivity
  let q : ℝ → ℝ := fun ε => max (-T) (min ε T)
  have hq : ∀ ε, |q ε| ≤ T := fun ε =>
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hqc : Continuous q := continuous_const.max (continuous_id.min continuous_const)
  set R' : ℝ := ‖z‖ + 3 * |r₀| / 2 * ρ' with hR'
  -- every pullback vanishes outside `closedBall 0 R'`
  have hvan : ∀ r, ∀ y : ℂ, R' < ‖y‖ → (φ ∘ affMap (p r) z) y = 0 := by
    intro r y hy
    show φ (affMap (p r) z y) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hsupp hmem
    rw [mem_closedBall, dist_zero_right, norm_affMap] at h1
    have hpr : 0 < |p r| := abs_pos.2 (hp0 r)
    have h2 : ‖y - z‖ ≤ |p r| * ρ' := by
      rw [inv_mul_le_iff₀ hpr] at h1
      exact h1
    have h3 : |p r| * ρ' ≤ 3 * |r₀| / 2 * ρ' :=
      mul_le_mul_of_nonneg_right (hp_hi r) (le_max_right _ _)
    have h4 : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := norm_le_insert' y z
    linarith
  let K : Compacts ℂ := ⟨closedBall 0 (R' + T), isCompact_closedBall _ _⟩
  let Ψ : ℝ × ℝ → ℂ → ℝ := fun a => circleMeanFun (φ ∘ affMap (p a.1) z) (q a.2)
  have hs : ∀ a, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ a) := fun a =>
    contDiff_circleMeanFun (contDiff_comp_affMap _ _ φ.contDiff)
      (hasCompactSupport_comp_affMap _ _ (hp0 a.1) φ.hasCompactSupport) (q a.2)
  have hK : ∀ a, ∀ y ∉ (K : Set ℂ), Ψ a y = 0 := by
    intro a y hy
    have h : y ∉ closedBall (0 : ℂ) (R' + T) := hy
    rw [mem_closedBall, dist_zero_right, not_le] at h
    exact circleMeanFun_eq_zero_of_forall (hvan a.1) (by linarith [hq a.2])
  set F : ℂ → ℝ := fun u => (2 * π)⁻¹ * φ u with hFdef
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := contDiff_const.mul φ.contDiff
  have hFc : HasCompactSupport F := φ.hasCompactSupport.mono (Function.support_mul_subset_right _ _)
  have hinv : Continuous fun r : ℝ => (p r)⁻¹ := (continuous_scaleClamp r₀).inv₀ hp0
  have hD : ∀ i : ℕ, Continuous fun b : (ℝ × ℝ) × ℂ => iteratedFDeriv ℝ i (Ψ b.1) b.2 := by
    intro i
    have e : (fun b : (ℝ × ℝ) × ℂ => iteratedFDeriv ℝ i (Ψ b.1) b.2) = fun b =>
        circleSubIntegral (fun w => ((p b.1.1)⁻¹) ^ i • iteratedFDeriv ℝ i F (affMap (p b.1.1) z w))
          (q b.1.2) b.2 := by
      funext b
      show iteratedFDeriv ℝ i (circleMeanFun (φ ∘ affMap (p b.1.1) z) (q b.1.2)) b.2 = _
      have hrw : (fun w => (2 * π)⁻¹ * (φ ∘ affMap (p b.1.1) z) w) = F ∘ affMap (p b.1.1) z := rfl
      rw [circleMeanFun_eq, hrw, iteratedFDeriv_circleSubIntegral (contDiff_comp_affMap _ _ hF)
        (hasCompactSupport_comp_affMap _ _ (hp0 b.1.1) hFc)]
      congr 1
      funext w
      rw [iteratedFDeriv_comp_affMap _ _ hF, compContinuousLinearMap_affLin]
    rw [e]
    have hG : Continuous (Function.uncurry fun (b : (ℝ × ℝ) × ℂ) (w : ℂ) =>
        ((p b.1.1)⁻¹) ^ i • iteratedFDeriv ℝ i F (affMap (p b.1.1) z w)) := by
      have hpc : Continuous fun y : ((ℝ × ℝ) × ℂ) × ℂ => (p y.1.1.1)⁻¹ :=
        hinv.comp (continuous_fst.comp (continuous_fst.comp continuous_fst))
      have haff : Continuous fun y : ((ℝ × ℝ) × ℂ) × ℂ => affMap (p y.1.1.1) z y.2 := by
        show Continuous fun y : ((ℝ × ℝ) × ℂ) × ℂ => (p y.1.1.1)⁻¹ • (y.2 + -z)
        exact hpc.smul (continuous_snd.add continuous_const)
      exact (hpc.pow i).smul
        ((hF.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp haff)
    exact continuous_circleSubIntegral_family hG (hqc.comp (continuous_snd.comp continuous_fst))
      continuous_snd
  have hcont : Continuous fun a => ofSuppC K (testFamK K Ψ hs hK a) :=
    (ofSuppC K).continuous.comp (continuous_testFamK K Ψ hs hK hD)
  refine hcont.continuousAt.congr ?_
  have hnb : ball r₀ (|r₀| / 2) ×ˢ ball ε₀ 1 ∈ 𝓝 (r₀, ε₀) :=
    prod_mem_nhds (ball_mem_nhds _ (by linarith)) (ball_mem_nhds _ one_pos)
  filter_upwards [hnb] with a ha'
  obtain ⟨hr, hε⟩ := ha'
  have hr' : |a.1 - r₀| ≤ |r₀| / 2 := by
    rw [mem_ball, Real.dist_eq] at hr
    exact hr.le
  have hpr : p a.1 = a.1 := scaleClamp_eq r₀ a.1 hr'
  have hr0 : a.1 ≠ 0 := by
    rw [← hpr]
    exact hp0 a.1
  have hqe : q a.2 = a.2 := by
    rw [mem_ball, Real.dist_eq] at hε
    have h1 := abs_sub_abs_le_abs_sub a.2 ε₀
    have h2 : |a.2| ≤ T := by linarith
    simp only [q]
    rw [min_eq_left ((le_abs_self a.2).trans h2), max_eq_right (by linarith [neg_abs_le a.2])]
  have hfun : (⇑(testAffinePull a.1 z φ) : ℂ → ℝ) = φ ∘ affMap a.1 z := by
    funext y
    simp only [testAffinePull, hr0, dite_false]
    rfl
  ext y
  show circleMeanFun (φ ∘ affMap (p a.1) z) (q a.2) y = circleMeanFun (testAffinePull a.1 z φ) a.2 y
  rw [hfun, hpr, hqe]

/-- `(r, ε) ↦ circleMeanTest (testAffinePull r z φ) ε` is continuous on `{r ≠ 0}` -/
theorem continuousOn_circleMeanTest_testAffinePull (φ : TestC) (z : ℂ) :
    ContinuousOn (fun a : ℝ × ℝ => circleMeanTest (testAffinePull a.1 z φ) a.2) {a | a.1 ≠ 0} :=
  fun a ha => (continuousAt_circleMeanTest_testAffinePull φ z ha a.2).continuousWithinAt

/-- **Joint continuity of the circle means of the dilations.** For `φ ∈ 𝓓(ℂ)`, `z ∈ ℂ` and `s₀ ≠ 0`, the map
`(s, ε) ↦ circleMeanTest (φ(s(· - z))) ε = circleMeanTest (testAffinePull s⁻¹ z φ) ε` into `𝓓(ℂ)` is continuous at
`(s₀, ε₀)`. -/
theorem continuousAt_circleMeanTest_dilate (φ : TestC) (z : ℂ) {s₀ : ℝ} (hs₀ : s₀ ≠ 0) (ε₀ : ℝ) :
    ContinuousAt (fun a : ℝ × ℝ => circleMeanTest (testAffinePull a.1⁻¹ z φ) a.2) (s₀, ε₀) := by
  have h1 := continuousAt_circleMeanTest_testAffinePull φ z (inv_ne_zero hs₀) ε₀
  have h2 : ContinuousAt (fun a : ℝ × ℝ => (a.1⁻¹, a.2)) (s₀, ε₀) :=
    ((continuousAt_fst (p := (s₀, ε₀))).inv₀ hs₀).prodMk continuousAt_snd
  simpa only [Function.comp_def] using ContinuousAt.comp_of_eq h1 h2 rfl

/-- for a fixed radius `ε`, the circle means of the dilations `s ↦ circleMeanTest (φ(s(· - z))) ε` are continuous at
every `s₀ ≠ 0` -/
theorem continuousAt_circleMeanTest_dilate_left (φ : TestC) (z : ℂ) {s₀ : ℝ} (hs₀ : s₀ ≠ 0) (ε : ℝ) :
    ContinuousAt (fun s : ℝ => circleMeanTest (testAffinePull s⁻¹ z φ) ε) s₀ := by
  have h2 : ContinuousAt (fun s : ℝ => (s, ε)) s₀ := continuousAt_id.prodMk continuousAt_const
  simpa only [Function.comp_def] using ContinuousAt.comp_of_eq (continuousAt_circleMeanTest_dilate φ z hs₀ ε) h2 rfl

end LQGMetric
