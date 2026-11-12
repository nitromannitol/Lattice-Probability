import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Continuity of affine pullbacks of test functions in the scale

For a test function `φ ∈ 𝓓(ℂ)` and `z ∈ ℂ`, the affine pullback `testAffinePull r z φ = φ((· - z)/r)`
depends continuously on the scale `r ≠ 0`, for the topology of `𝓓(ℂ)`.

* `compContinuousLinearMap_affLin`: `f ∘ (affLin r, …, affLin r) = r^{-i} • f` for an `i`-multilinear map `f`;
* `continuousAt_testAffinePull_scale`: `r ↦ testAffinePull r z φ` is continuous at every `r₀ ≠ 0`;
* `continuousOn_testAffinePull_scale`: it is continuous on `{r ≠ 0}`;
* `continuousAt_testAffinePull_inv_scale`: the dilations `s ↦ φ(s (· - z))` are continuous in `s ≠ 0`.

The proof clamps the scale to the compact neighbourhood `[r₀ - |r₀|/2, r₀ + |r₀|/2]` of `r₀`, so that all the
pullbacks are supported in one compact set `K`, and applies `continuous_testFamK` in `𝓓_K`: the iterated
derivatives `D^i (φ ∘ affMap r z) = r^{-i} • (D^i φ) ∘ affMap r z` are jointly continuous in `(r, x)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions

namespace LQGMetric

/-- Composing an `i`-multilinear map with the dilation `affLin r = r⁻¹ • id` in each variable multiplies it by
`r^{-i}`. -/
theorem compContinuousLinearMap_affLin {i : ℕ} (r : ℝ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin i => ℂ) ℝ) :
    (f.compContinuousLinearMap fun _ => affLin r) = (r⁻¹) ^ i • f := by
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, affLin,
    smul_apply, ContinuousLinearMap.id_apply]
  rw [f.map_smul_univ]
  simp [Finset.prod_const, Finset.card_univ]

theorem norm_affMap (r : ℝ) (z x : ℂ) : ‖affMap r z x‖ = |r|⁻¹ * ‖x - z‖ := by
  unfold affMap
  rw [norm_smul, Real.norm_eq_abs, abs_inv, sub_eq_add_neg]

/-- The scale `r` clamped to the interval `[r₀ - |r₀|/2, r₀ + |r₀|/2]`. -/
def scaleClamp (r₀ r : ℝ) : ℝ := r₀ + max (-(|r₀| / 2)) (min (r - r₀) (|r₀| / 2))

theorem continuous_scaleClamp (r₀ : ℝ) : Continuous (scaleClamp r₀) := by
  unfold scaleClamp
  fun_prop

theorem abs_scaleClamp_sub_le (r₀ r : ℝ) : |scaleClamp r₀ r - r₀| ≤ |r₀| / 2 := by
  unfold scaleClamp
  rw [add_sub_cancel_left, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith [abs_nonneg r₀]) (min_le_right _ _)⟩

theorem scaleClamp_eq (r₀ r : ℝ) (h : |r - r₀| ≤ |r₀| / 2) : scaleClamp r₀ r = r := by
  unfold scaleClamp
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]
  ring

theorem half_abs_le_abs_scaleClamp (r₀ r : ℝ) : |r₀| / 2 ≤ |scaleClamp r₀ r| := by
  have h := abs_scaleClamp_sub_le r₀ r
  have h2 := abs_sub_abs_le_abs_sub r₀ (scaleClamp r₀ r)
  rw [abs_sub_comm] at h2
  linarith

theorem abs_scaleClamp_le (r₀ r : ℝ) : |scaleClamp r₀ r| ≤ 3 * |r₀| / 2 := by
  have h := abs_scaleClamp_sub_le r₀ r
  have h2 := abs_sub_abs_le_abs_sub (scaleClamp r₀ r) r₀
  linarith

/-- **Continuity of the affine pullback in the scale.** For `φ ∈ 𝓓(ℂ)` and `z ∈ ℂ`, the map
`r ↦ φ((· - z)/r)` into `𝓓(ℂ)` is continuous at every `r₀ ≠ 0`. -/
theorem continuousAt_testAffinePull_scale (φ : TestC) (z : ℂ) {r₀ : ℝ} (hr₀ : r₀ ≠ 0) :
    ContinuousAt (fun r => testAffinePull r z φ) r₀ := by
  obtain ⟨ρ, hρ⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set ρ' := max ρ 0 with hρ'
  have hsupp : tsupport φ ⊆ closedBall (0 : ℂ) ρ' :=
    hρ.trans (closedBall_subset_closedBall (le_max_left _ _))
  have ha : 0 < |r₀| := abs_pos.2 hr₀
  set p := scaleClamp r₀ with hp
  have hp_lo : ∀ r, |r₀| / 2 ≤ |p r| := half_abs_le_abs_scaleClamp r₀
  have hp_hi : ∀ r, |p r| ≤ 3 * |r₀| / 2 := abs_scaleClamp_le r₀
  have hp0 : ∀ r, p r ≠ 0 := fun r h => by
    have := hp_lo r
    rw [h, abs_zero] at this
    linarith
  let K : Compacts ℂ := ⟨closedBall z (3 * |r₀| / 2 * ρ'), isCompact_closedBall _ _⟩
  let Ψ : ℝ → ℂ → ℝ := fun r => φ ∘ affMap (p r) z
  have hs : ∀ r, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ r) := fun r =>
    contDiff_comp_affMap (p r) z φ.contDiff
  have hK : ∀ r, ∀ y ∉ (K : Set ℂ), Ψ r y = 0 := by
    intro r y hy
    have hy' : 3 * |r₀| / 2 * ρ' < ‖y - z‖ := by
      have h : y ∉ closedBall z (3 * |r₀| / 2 * ρ') := hy
      rw [mem_closedBall, dist_eq_norm, not_le] at h
      exact h
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
    linarith
  have hD : ∀ i : ℕ, Continuous fun q : ℝ × ℂ => iteratedFDeriv ℝ i (Ψ q.1) q.2 := by
    intro i
    have e : (fun q : ℝ × ℂ => iteratedFDeriv ℝ i (Ψ q.1) q.2) =
        fun q => ((p q.1)⁻¹) ^ i • iteratedFDeriv ℝ i φ (affMap (p q.1) z q.2) := by
      funext q
      show iteratedFDeriv ℝ i (φ ∘ affMap (p q.1) z) q.2 = _
      rw [iteratedFDeriv_comp_affMap _ _ φ.contDiff, compContinuousLinearMap_affLin]
    rw [e]
    have hpc : Continuous fun q : ℝ × ℂ => p q.1 := (continuous_scaleClamp r₀).comp continuous_fst
    have hinv : Continuous fun q : ℝ × ℂ => (p q.1)⁻¹ := hpc.inv₀ fun q => hp0 q.1
    have haff : Continuous fun q : ℝ × ℂ => affMap (p q.1) z q.2 := by
      show Continuous fun q : ℝ × ℂ => (p q.1)⁻¹ • (q.2 + -z)
      exact hinv.smul (continuous_snd.add continuous_const)
    exact (hinv.pow i).smul
      ((φ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp haff)
  have hc := continuous_testFamK K Ψ hs hK hD
  have hcont : Continuous fun r => ofSuppC K (testFamK K Ψ hs hK r) := (ofSuppC K).continuous.comp hc
  refine hcont.continuousAt.congr ?_
  have hball : ball r₀ (|r₀| / 2) ∈ 𝓝 r₀ := ball_mem_nhds _ (by linarith)
  filter_upwards [hball] with r hr
  have hr' : |r - r₀| ≤ |r₀| / 2 := by
    rw [mem_ball, Real.dist_eq] at hr
    exact hr.le
  have hpr : p r = r := scaleClamp_eq r₀ r hr'
  have hr0 : r ≠ 0 := by
    rw [← hpr]
    exact hp0 r
  ext y
  simp only [testAffinePull, hr0, dite_false]
  show φ (affMap (p r) z y) = φ (affMap r z y)
  rw [hpr]

/-- The affine pullback `r ↦ φ((· - z)/r)` is continuous on `{r ≠ 0}` into `𝓓(ℂ)`. -/
theorem continuousOn_testAffinePull_scale (φ : TestC) (z : ℂ) :
    ContinuousOn (fun r => testAffinePull r z φ) {r | r ≠ 0} :=
  fun _ hr => (continuousAt_testAffinePull_scale φ z hr).continuousWithinAt

/-- The dilations `s ↦ φ(s (· - z)) = testAffinePull s⁻¹ z φ` are continuous at every `s₀ ≠ 0` into `𝓓(ℂ)`. -/
theorem continuousAt_testAffinePull_inv_scale (φ : TestC) (z : ℂ) {s₀ : ℝ} (hs₀ : s₀ ≠ 0) :
    ContinuousAt (fun s => testAffinePull s⁻¹ z φ) s₀ :=
  (continuousAt_testAffinePull_scale φ z (inv_ne_zero hs₀)).comp (continuousAt_inv₀ hs₀)

end LQGMetric
