import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea3

/-!
# Weyl scaling of vague limits of exponential-density approximations

Let `A_k = c_k e^{γ a_k(z)} dz` be approximations (for instance of an LQG measure, with `a_k` the
circle averages of a field at scale `2^{-k}` and `c_k = 2^{-kγ²/2}`) converging vaguely on an
open set `U` to a measure `μ`. If, on every compact subset of `U` and at all fine scales, the
exponents of a second family `B_k = c_k e^{γ b_k(z)} dz` satisfy `b_k = a_k + ψ_k` almost
everywhere, with `ψ_k → g` uniformly on compact subsets of `U` and `g` continuous on `U`, then
`B_k → e^{γ g} μ` vaguely on `U`.

This is the deterministic half of the Weyl-scaling rule `dμ_{h + g} = e^{γ g} dμ_h` for Gaussian
multiplicative chaos with a continuous shift `g` (Duplantier–Sheffield; Berestycki–Powell,
*Gaussian free field and Liouville quantum gravity*, Chapter 3). The statement and proof follow
Leonardo Bonanno's lemma `isVagueLimitOn_areaApproxC_of_shift` (lean-formalizations, commit
31e7483), stated there for the circle averages of a fixed field type; here the exponents are
arbitrary measurable functions.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric

/-- **Weyl scaling of vague limits.** If `c_k e^{γ a_k} dz → μ` vaguely on the open set `U`, and
on every compact `K ⊆ U` at fine scales `b_k = a_k + ψ_k` almost everywhere on `K`, with
`ψ_k → g` uniformly on compacts of `U` and `g` continuous on `U`, then
`c_k e^{γ b_k} dz → e^{γ g} μ` vaguely on `U`. -/
theorem _root_.LatticeProb.LQG.isVagueLimitOn_withDensity_exp_of_shift {γ : ℝ} {U : Set ℂ}
    (hU : IsOpen U) {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) {a b : ℕ → ℂ → ℝ}
    (ham : ∀ k, Measurable (a k)) (hbm : ∀ k, Measurable (b k)) {μ : Measure ℂ}
    (hx : QuantumZipper.IsVagueLimitOn U
      (fun k => volume.withDensity fun z => ENNReal.ofReal (c k * Real.exp (γ * a k z))) μ)
    {g : ℂ → ℝ} (hgm : Measurable g) (hg : ContinuousOn g U)
    {ψ : ℕ → ℂ → ℝ} (hψm : ∀ k, Measurable (ψ k))
    (hψ : ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn ψ g atTop K)
    (hab : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ K →
      b k z = a k z + ψ k z) :
    QuantumZipper.IsVagueLimitOn U
      (fun k => volume.withDensity fun z => ENNReal.ofReal (c k * Real.exp (γ * b k z)))
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * g z))) := by
  have hρm : Measurable fun z => Real.exp (γ * g z) :=
    Real.measurable_exp.comp (hgm.const_mul γ)
  refine ⟨withDensity_absolutelyContinuous μ _ hx.1, fun K hK hKU => ?_, fun f hf hfc hfU => ?_⟩
  · -- finiteness on compacts
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hg.mono hKU)
    rw [withDensity_apply _ hK.measurableSet]
    calc ∫⁻ z in K, ENNReal.ofReal (Real.exp (γ * g z)) ∂μ
        ≤ ∫⁻ _ in K, ENNReal.ofReal (Real.exp (|γ| * M)) ∂μ := by
          refine setLIntegral_mono measurable_const fun z hz => ?_
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have h1 := hM z hz
          rw [Real.norm_eq_abs] at h1
          calc γ * g z ≤ |γ * g z| := le_abs_self _
            _ = |γ| * |g z| := abs_mul _ _
            _ ≤ |γ| * M := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = ENNReal.ofReal (Real.exp (|γ| * M)) * μ K := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hx.2.1 K hK hKU)
  -- the test function `F = f e^{γ g}`
  set F : ℂ → ℝ := fun z => f z * Real.exp (γ * g z) with hF
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    by_cases hz : z ∈ U
    · exact hf.continuousAt.mul (Real.continuous_exp.continuousAt.comp
        (continuousAt_const.mul (hg.continuousAt (hU.mem_nhds hz))))
    · have h0 : f =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hz (hfU h)
      have h1 : (fun _ : ℂ => (0 : ℝ)) =ᶠ[𝓝 z] F :=
        Filter.Eventually.mono h0 fun w hw => by
          simp only [Pi.zero_apply] at hw
          simp [hF, hw]
      exact continuousAt_const.congr h1
  have hFs : tsupport F ⊆ tsupport f := tsupport_mul_subset_left
  have hFcs : HasCompactSupport F := hfc.mul_right
  set e : ℕ → ℂ → ℝ := fun k z => Real.exp (γ * (ψ k z - g z)) with he
  have hem : ∀ k, Measurable (e k) := fun k =>
    Real.measurable_exp.comp (((hψm k).sub hgm).const_mul γ)
  have hK : IsCompact (tsupport f) := hfc
  have hunif : ∀ η > 0, ∀ᶠ k in atTop, ∀ z ∈ tsupport F, |e k z - 1| < η := by
    intro η hη
    set η' := min 1 (η / 4) / (|γ| + 1) with hη'
    have hη'0 : 0 < η' := by positivity
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hψ _ hK hfU) η' hη'0] with k hk z hz
    have h1 := hk z (hFs hz)
    rw [Real.dist_eq, abs_sub_comm] at h1
    have h2 : |γ * (ψ k z - g z)| < min 1 (η / 4) := by
      rw [abs_mul]
      calc |γ| * |ψ k z - g z| ≤ (|γ| + 1) * |ψ k z - g z| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < (|γ| + 1) * η' := mul_lt_mul_of_pos_left h1 (by positivity)
        _ = min 1 (η / 4) := by rw [hη']; field_simp
    have h3 := Real.abs_exp_sub_one_le (h2.le.trans (min_le_left _ _))
    have h4 : min 1 (η / 4) ≤ η / 4 := min_le_right _ _
    show |Real.exp (γ * (ψ k z - g z)) - 1| < η
    linarith
  have hlim := DG.tendsto_integral_mul_of_unif hx hem hFc hFcs (hFs.trans hfU) hunif
  have hval : ∫ z, f z ∂(μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * g z))) =
      ∫ z, F z ∂μ := by
    rw [GMCIdent4.integral_withDensity_ofReal hρm (fun z => (Real.exp_pos _).le)]
    simp only [hF, mul_comm]
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [hab _ hK hfU] with k hk
  have hDm : ∀ d : ℂ → ℝ, Measurable d → Measurable fun z => c k * Real.exp (γ * d z) :=
    fun d hd => measurable_const.mul (Real.measurable_exp.comp (hd.const_mul γ))
  have hD0 : ∀ (d : ℂ → ℝ) z, 0 ≤ c k * Real.exp (γ * d z) := fun d z =>
    mul_nonneg (hc k) (Real.exp_pos _).le
  rw [GMCIdent4.integral_withDensity_ofReal (hDm _ (ham k)) (hD0 (a k)),
    GMCIdent4.integral_withDensity_ofReal (hDm _ (hbm k)) (hD0 (b k))]
  refine integral_congr_ae ?_
  filter_upwards [hk] with z hz
  by_cases hzK : z ∈ tsupport f
  · rw [hz hzK]
    have : Real.exp (γ * (a k z + ψ k z)) =
        Real.exp (γ * a k z) * (Real.exp (γ * g z) * Real.exp (γ * (ψ k z - g z))) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    simp only [hF, he, this]
    ring
  · have h0 : f z = 0 := image_eq_zero_of_notMem_tsupport hzK
    simp [hF, h0]

end LQGMetric
