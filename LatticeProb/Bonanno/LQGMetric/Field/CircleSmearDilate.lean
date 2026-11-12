import LatticeProb.Bonanno.LQGMetric.Field.CircleMeanDilate

/-!
# Circle smears of a distribution along dilations

Let `H ∈ 𝒟'(ℂ)`, let `φ ∈ 𝓓(ℂ)` and let `h : ℝ → ℂ → ℝ`, `(ε, z) ↦ h ε z`, be jointly continuous on `(0, ∞) × ℂ`
(for instance a continuous version of the circle-average process of a random generalized function). Suppose that the
circle smears of `h` represent `H` on the circle means of the dilations `φ(s ·)` at rational parameters:
`∫ φ(s z) h_ε(z) dz = ⟨H, circleMeanTest (φ(s ·)) ε⟩` for all rational `s > 0` and `ε ∈ (0, 1)`. Then the identity
holds for all real `s > 0` and `ε ∈ (0, 1)`, and `∫ φ(s z) h_ε(z) dz → ⟨H, φ(s ·)⟩` as `ε → 0+`, for every `s > 0`.

* `testAffinePull_inv_zero_apply`: the dilation `φ(s ·)` is `testAffinePull s⁻¹ 0 φ`;
* `continuousAt_integral_smul_mul`: `(s, ε) ↦ ∫ φ(s z) h_ε(z) dz` is continuous on `(0, ∞) × (0, ∞)`;
* `integral_smul_mul_eq_of_rat`: extension of the identity from rational to real parameters;
* `tendsto_integral_smul_mul_of_rat`: the circle smears along every dilation converge to the pairing with `H`.

Both sides of the identity are continuous in `(s, ε)`: the left side by continuity of parametric integrals of a
jointly continuous integrand with a common compact support (after clamping the parameters away from `0`), the right side
by `continuousAt_circleMeanTest_dilate` and continuity of `H` on `𝓓(ℂ)`. The rational points are dense.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions Real

namespace LQGMetric

/-- the dilation `φ(s ·)` of a test function is the affine pullback `testAffinePull s⁻¹ 0 φ` -/
theorem testAffinePull_inv_zero_apply (φ : TestC) {s : ℝ} (hs : s ≠ 0) (x : ℂ) :
    testAffinePull s⁻¹ 0 φ x = φ (s • x) := by
  rw [testAffinePull_apply _ _ (inv_ne_zero hs)]
  congr 1
  simp [Complex.real_smul, mul_comm]

/-- **Continuity of the smears along dilations.** For `φ : ℂ → ℝ` continuous with compact support and `h` jointly
continuous on `(0, ∞) × ℂ`, the map `(s, ε) ↦ ∫ φ(s z) h_ε(z) dz` is continuous at every `(s₀, ε₀)` with `s₀ > 0` and
`ε₀ > 0`. -/
theorem continuousAt_integral_smul_mul {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {h : ℝ → ℂ → ℝ} (hh : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Ioi 0 ×ˢ univ))
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : 0 < ε₀) :
    ContinuousAt (fun a : ℝ × ℝ => ∫ z, φ (a.1 • z) * h a.2 z) (s₀, ε₀) := by
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  have hc : 0 < s₀ / 2 := half_pos hs₀
  have hd : 0 < ε₀ / 2 := half_pos hε₀
  -- the integrand with both parameters clamped away from `0`
  have hFc : Continuous (Function.uncurry fun (a : ℝ × ℝ) (z : ℂ) =>
      φ (max a.1 (s₀ / 2) • z) * h (max a.2 (ε₀ / 2)) z) := by
    change Continuous fun q : (ℝ × ℝ) × ℂ => φ (max q.1.1 (s₀ / 2) • q.2) * h (max q.1.2 (ε₀ / 2)) q.2
    refine (hφ.comp ((continuous_fst.fst.max continuous_const).smul continuous_snd)).mul ?_
    exact hh.comp_continuous ((continuous_fst.snd.max continuous_const).prodMk continuous_snd) fun q =>
      ⟨lt_of_lt_of_le hd (le_max_right _ _), mem_univ _⟩
  have hzero : ∀ (a : ℝ × ℝ) (z : ℂ), z ∉ closedBall (0 : ℂ) (R / (s₀ / 2)) →
      φ (max a.1 (s₀ / 2) • z) * h (max a.2 (ε₀ / 2)) z = 0 := by
    intro a z hz
    have hnot : max a.1 (s₀ / 2) • z ∉ tsupport φ := by
      intro hmem
      have h1 := hR hmem
      have hpos : 0 < max a.1 (s₀ / 2) := lt_of_lt_of_le hc (le_max_right _ _)
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hpos] at h1
      rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hc] at hz
      have h2 : ‖z‖ * (s₀ / 2) ≤ max a.1 (s₀ / 2) * ‖z‖ := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      linarith
    rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]
  have hcont : Continuous fun a : ℝ × ℝ => ∫ z, φ (max a.1 (s₀ / 2) • z) * h (max a.2 (ε₀ / 2)) z := by
    refine (continuous_parametric_integral_of_continuous (μ := (volume : Measure ℂ)) hFc
      (isCompact_closedBall (0 : ℂ) (R / (s₀ / 2)))).congr fun a => ?_
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (hzero a)
  refine hcont.continuousAt.congr ?_
  have h1 : ∀ᶠ a : ℝ × ℝ in 𝓝 (s₀, ε₀), s₀ / 2 < a.1 :=
    (continuous_fst.tendsto (s₀, ε₀)).eventually (lt_mem_nhds (half_lt_self hs₀))
  have h2 : ∀ᶠ a : ℝ × ℝ in 𝓝 (s₀, ε₀), ε₀ / 2 < a.2 :=
    (continuous_snd.tendsto (s₀, ε₀)).eventually (lt_mem_nhds (half_lt_self hε₀))
  filter_upwards [h1, h2] with a ha1 ha2
  rw [max_eq_left ha1.le, max_eq_left ha2.le]

/-- **Extension from rational parameters.** Let `H ∈ 𝒟'(ℂ)`, `φ ∈ 𝓓(ℂ)` and `h` jointly continuous on `(0, ∞) × ℂ`.
If `∫ φ(s z) h_ε(z) dz = ⟨H, circleMeanTest (φ(s ·)) ε⟩` for all rational `s > 0` and `ε ∈ (0, 1)`, then the same
identity holds for all real `s > 0` and `ε ∈ (0, 1)`. -/
theorem integral_smul_mul_eq_of_rat (H : DistC) (φ : TestC) {h : ℝ → ℂ → ℝ}
    (hh : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Ioi 0 ×ˢ univ))
    (hrat : ∀ s ε : ℚ, 0 < s → 0 < ε → ε < 1 →
      ∫ z, φ ((s : ℝ) • z) * h (ε : ℝ) z = H (circleMeanTest (testAffinePull (s : ℝ)⁻¹ 0 φ) (ε : ℝ)))
    {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (hε1 : ε < 1) :
    ∫ z, φ (s • z) * h ε z = H (circleMeanTest (testAffinePull s⁻¹ 0 φ) ε) := by
  have hTo : IsOpen (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) := isOpen_Ioi.prod isOpen_Ioo
  have hQ : Dense (range (Rat.cast : ℚ → ℝ) ×ˢ range (Rat.cast : ℚ → ℝ)) :=
    Rat.denseRange_cast.prod Rat.denseRange_cast
  have heq : EqOn (fun a : ℝ × ℝ => ∫ z, φ (a.1 • z) * h a.2 z)
      (fun a => H (circleMeanTest (testAffinePull a.1⁻¹ 0 φ) a.2))
      ((Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) ∩ (range (Rat.cast : ℚ → ℝ) ×ˢ range (Rat.cast : ℚ → ℝ))) := by
    rintro ⟨a, b⟩ ⟨⟨ha, hb, hb1⟩, ⟨p, rfl⟩, ⟨q, rfl⟩⟩
    exact hrat p q (by exact_mod_cast (show (0 : ℝ) < p from ha)) (by exact_mod_cast (show (0 : ℝ) < q from hb))
      (by exact_mod_cast (show (q : ℝ) < 1 from hb1))
  have hf : ContinuousOn (fun a : ℝ × ℝ => ∫ z, φ (a.1 • z) * h a.2 z) (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) :=
    fun a ha => (continuousAt_integral_smul_mul φ.continuous φ.hasCompactSupport hh ha.1 ha.2.1).continuousWithinAt
  have hg : ContinuousOn (fun a : ℝ × ℝ => H (circleMeanTest (testAffinePull a.1⁻¹ 0 φ) a.2))
      (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) := fun a ha =>
    ((map_continuous H).continuousAt.comp
      (continuousAt_circleMeanTest_dilate φ 0 (ne_of_gt ha.1) a.2)).continuousWithinAt
  exact heq.of_subset_closure hf hg inter_subset_left (hQ.open_subset_closure_inter hTo)
    (show ((s, ε) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1 from ⟨hs, hε, hε1⟩)

/-- **Circle smears along dilations converge to the pairing.** Under the hypotheses of `integral_smul_mul_eq_of_rat`,
for every `s > 0`, `∫ φ(s z) h_ε(z) dz → ⟨H, φ(s ·)⟩` as `ε → 0+`. -/
theorem tendsto_integral_smul_mul_of_rat (H : DistC) (φ : TestC) {h : ℝ → ℂ → ℝ}
    (hh : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Ioi 0 ×ˢ univ))
    (hrat : ∀ s ε : ℚ, 0 < s → 0 < ε → ε < 1 →
      ∫ z, φ ((s : ℝ) • z) * h (ε : ℝ) z = H (circleMeanTest (testAffinePull (s : ℝ)⁻¹ 0 φ) (ε : ℝ)))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ε => ∫ z, φ (s • z) * h ε z) (𝓝[>] 0) (𝓝 (H (testAffinePull s⁻¹ 0 φ))) := by
  have hlim : Tendsto (fun ε => H (circleMeanTest (testAffinePull s⁻¹ 0 φ) ε)) (𝓝[>] 0)
      (𝓝 (H (testAffinePull s⁻¹ 0 φ))) :=
    ((map_continuous H).tendsto _).comp ((tendsto_circleMeanTest_zero _).mono_left nhdsWithin_le_nhds)
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
  exact (integral_smul_mul_eq_of_rat H φ hh hrat hs hε.1 hε.2).symm

end LQGMetric
