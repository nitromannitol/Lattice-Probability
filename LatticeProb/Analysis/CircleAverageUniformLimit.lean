import Mathlib

/-!
# Uniform limits under density weights and composition

General forms of three facts about weighted integrals and uniform convergence on compact sets, used
for the vague limit of densities `e^{γ f_ε}` with uniformly convergent circle averages:

* the integral against a measure with a nonnegative measurable density is the integral of the
  product of the density and the integrand;
* uniform convergence on a compact set is preserved by composition with a continuous function on
  the left;
* if measures `ν k` converge vaguely to `m` and continuous weights `Fk k` converge to a continuous
  `F` uniformly on compact sets, then `∫ Fk k · g ∂ν k → ∫ F · g ∂m` for continuous compactly
  supported `g`.
-/

namespace LatticeProb.CircleAverageUniformLimit

open MeasureTheory Filter Topology Set Metric

/-- The integral against a measure with a nonnegative measurable density `D`. -/
theorem integral_withDensity_ofReal {X : Type*} [MeasurableSpace X] {ν : Measure X} {D : X → ℝ}
    (hD : Measurable D) (hD0 : ∀ x, 0 ≤ D x) (g : X → ℝ) :
    ∫ x, g x ∂(ν.withDensity fun x => ENNReal.ofReal (D x)) = ∫ x, D x * g x ∂ν := by
  change ∫ x, g x ∂(ν.withDensity fun x => ((D x).toNNReal : ENNReal)) = _
  rw [integral_withDensity_eq_integral_smul hD.real_toNNReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hD0 x)]

/-- Uniform convergence on a compact set is preserved by composition with a continuous function. -/
theorem TendstoUniformlyOn.comp_continuous_left {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ} {K : Set ℂ}
    (hK : IsCompact K) (hv : ContinuousOn v K) (h : TendstoUniformlyOn u v atTop K)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    TendstoUniformlyOn (fun k z => φ (u k z)) (fun z => φ (v z)) atTop K := by
  have hS : IsCompact (cthickening 1 (v '' K)) := (hK.image_of_continuousOn hv).cthickening
  have hφu := hS.uniformContinuousOn_of_continuous hφ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hφu
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδφ⟩ := hφu ε hε
  filter_upwards [h (min δ 1) (lt_min hδ one_pos)] with k hk z hz
  have h1 := hk z hz
  have hvz : v z ∈ cthickening 1 (v '' K) := self_subset_cthickening _ (mem_image_of_mem v hz)
  have huz : u k z ∈ cthickening 1 (v '' K) :=
    mem_cthickening_of_dist_le (u k z) (v z) 1 (v '' K) (mem_image_of_mem v hz)
      (by rw [dist_comm]; exact h1.le.trans (min_le_right _ _))
  exact hδφ (v z) hvz (u k z) huz (h1.trans_le (min_le_left _ _))

/-- **Weights through a vague limit.** If `ν_k → m` vaguely (against continuous compactly supported
functions) and continuous weights `F_k` converge to a continuous `F` uniformly on compact sets, then
`F_k ν_k → F m` vaguely. -/
theorem tendsto_integral_mul_of_tendstoUniformlyOn {ν : ℕ → Measure ℂ} {m : Measure ℂ}
    [∀ k, IsLocallyFiniteMeasure (ν k)]
    (hν : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun k => ∫ z, g z ∂ν k) atTop (𝓝 (∫ z, g z ∂m)))
    {F : ℂ → ℝ} {Fk : ℕ → ℂ → ℝ} (hF : Continuous F) (hFk : ∀ k, Continuous (Fk k))
    (hunif : ∀ K, IsCompact K → TendstoUniformlyOn Fk F atTop K)
    {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun k => ∫ z, Fk k z * g z ∂ν k) atTop (𝓝 (∫ z, F z * g z ∂m)) := by
  have hsplit : ∀ k, ∫ z, Fk k z * g z ∂ν k =
      ∫ z, F z * g z ∂ν k + ∫ z, (Fk k z - F z) * g z ∂ν k := by
    intro k
    rw [← integral_add]
    · exact integral_congr_ae (Eventually.of_forall fun z => by simp only; ring)
    · exact (hF.mul hg).integrable_of_hasCompactSupport hgc.mul_left
    · exact (((hFk k).sub hF).mul hg).integrable_of_hasCompactSupport hgc.mul_left
  simp only [hsplit]
  rw [← add_zero (∫ z, F z * g z ∂m)]
  refine (hν _ (hF.mul hg) hgc.mul_left).add ?_
  have hB := hν _ hg.norm hgc.norm
  set B := ∫ z, ‖g z‖ ∂m + 1 with hBdef
  have hB0 : 0 < B := by
    have : 0 ≤ ∫ z, ‖g z‖ ∂m := integral_nonneg fun _ => norm_nonneg _
    linarith
  have hBev : ∀ᶠ k in atTop, ∫ z, ‖g z‖ ∂ν k < B := hB.eventually (gt_mem_nhds (lt_add_one _))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hη : 0 < ε / (2 * B) := by positivity
  have hU := hunif _ hgc.isCompact
  rw [Metric.tendstoUniformlyOn_iff] at hU
  filter_upwards [hU _ hη, hBev] with k hk hkB
  rw [dist_zero_right]
  calc ‖∫ z, (Fk k z - F z) * g z ∂ν k‖ ≤ ∫ z, ε / (2 * B) * ‖g z‖ ∂ν k := by
        refine norm_integral_le_of_norm_le
          (((hg.norm).integrable_of_hasCompactSupport hgc.norm).const_mul _)
          (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ tsupport g
        · rw [norm_mul]
          have h1 := hk z hz
          rw [dist_comm, dist_eq_norm] at h1
          gcongr
        · rw [image_eq_zero_of_notMem_tsupport hz]
          simp
    _ = ε / (2 * B) * ∫ z, ‖g z‖ ∂ν k := integral_const_mul _ _
    _ ≤ ε / (2 * B) * B := by gcongr
    _ < ε := by
        rw [div_mul_eq_mul_div, mul_div_assoc, div_mul_cancel_right₀ hB0.ne']
        linarith

end LatticeProb.CircleAverageUniformLimit
