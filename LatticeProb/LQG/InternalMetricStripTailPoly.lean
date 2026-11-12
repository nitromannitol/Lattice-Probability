import LatticeProb.LQG.InternalMetricUpperTailPoly
import LatticeProb.LQG.HalfCrossingsOfSetDistance
import LatticeProb.Gauss.GFFAffineInvariance
import LatticeProb.Topology.CornerSquareShells

/-!
# Exponential tail of the internal distance of two sets at unit scale

Let `𝔇` be a γ-LQG metric with Weyl exponent `ξ > 0` and `h` a whole-plane GFF, normalized so that its circle average
over `∂B_1(0)` vanishes. Let `U₀` be a bounded open connected set containing two compact connected non-singletons
`K₁, K₂`. For every `δ` and every `m > 0` there is a constant `K` such that for every `n`,
`P[ e^{δ n} ≤ D_h(K₁, K₂; U₀) ] ≤ K e^{-m δ n}`
(`IsLQGMetric.exists_measure_internalSetDist_ge_exp_le`). This is the polynomial tail
`exists_measure_internalDist_gt_le_poly` at scale `𝕣 = 1`, where `h_1(0) = 0` almost surely, with `c = e^{δ n}/2`.

The strip configurations of the crossing distances `horizontalCrossingDist` and `verticalCrossingDist` satisfy the
hypotheses, which gives the same exponential tail for them.
-/

namespace LatticeProb.LQG

open MeasureTheory Set Metric LatticeProb.Gauss LQGMetric LQGMetric.Blueprint LQGMetric.DFGPS LQGMetric.DFGPS.P31
open scoped ENNReal

theorem scaleSet_one_zero (K : Set ℂ) : scaleSet 1 0 K = K := by
  simp [scaleSet]

/-- **Exponential tail of the internal distance of two sets at unit scale.** See the module docstring. -/
theorem IsLQGMetric.exists_measure_internalSetDist_ge_exp_le {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hξ : 0 < ξ) (hγ : 0 < γ) {U₀ K₁ K₂ : Set ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hU₀b : U₀ ⊆ ball (0 : ℂ) R₀) (hU₀ : IsOpen U₀) (hU₀c : IsConnected U₀) (hK₁ : IsCompact K₁)
    (hK₁c : IsConnected K₁) (hK₁n : K₁.Nontrivial) (hK₂ : IsCompact K₂) (hK₂c : IsConnected K₂)
    (hK₂n : K₂.Nontrivial) (h₁U : K₁ ⊆ U₀) (h₂U : K₂ ⊆ U₀) (δ m : ℝ) (hm : 0 < m)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {H : Ω → DistC}
    (hH : LQGMetric.IsWholePlaneGFF H P) (hHC : ∀ ψ : TestC, (fun ω => H ω ψ) =ᵐ[P] fun ω => hC ω ψ)
    (hHcirc : ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, hcirc ω r z = circleAvg (H ω) r z) :
    ∃ K : ℝ, ∀ n : ℕ,
      P {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ internalSetDist (𝔇 (hC ω)) U₀ K₁ K₂} ≤
        ENNReal.ofReal (K * Real.exp (-(m * δ * n))) := by
  classical
  obtain ⟨C₀, K₀, hC₀, hT⟩ := h𝔇.exists_measure_internalDist_gt_le_poly hξ hγ hR₀ hU₀b hU₀ hU₀c hK₁ hK₁c hK₁n hK₂
    hK₂c hK₂n h₁U h₂U m hm hG hH hHC hHcirc
  refine ⟨max (2 ^ m * K₀) ((2 * C₀) ^ m), fun n => ?_⟩
  have hexp : 0 < Real.exp (δ * n) := Real.exp_pos _
  have hexpm : 0 < Real.exp (-(m * δ * n)) := Real.exp_pos _
  by_cases hc : C₀ ≤ Real.exp (δ * n) / 2
  · -- the polynomial tail applies with `c = e^{δ n} / 2`
    have hnull : ∀ᵐ ω ∂P, hcirc ω 1 0 = 0 := hG.ae_circleAverage_one_zero
    have hsub : {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ internalSetDist (𝔇 (hC ω)) U₀ K₁ K₂} ⊆
        {ω | ENNReal.ofReal (Real.exp (δ * n) / 2 * ((1 : ℝ) ^ (ξ * lqgQ γ) * Real.exp (ξ * hcirc ω 1 0))) <
          ⨅ u ∈ scaleSet 1 0 K₁, ⨅ v ∈ scaleSet 1 0 K₂,
            internalMetric (𝔇 (hC ω)) (scaleSet 1 0 U₀) u v} ∪ {ω | ¬ hcirc ω 1 0 = 0} := by
      intro ω hω
      by_cases h0 : hcirc ω 1 0 = 0
      · left
        simp only [mem_ofPred_eq, scaleSet_one_zero, h0, mul_zero, Real.exp_zero, Real.one_rpow, one_mul, mul_one]
        exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hexp).2 (by linarith)) hω
      · right; exact h0
    calc P {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ internalSetDist (𝔇 (hC ω)) U₀ K₁ K₂}
        ≤ P ({ω | ENNReal.ofReal (Real.exp (δ * n) / 2 * ((1 : ℝ) ^ (ξ * lqgQ γ) * Real.exp (ξ * hcirc ω 1 0))) <
          ⨅ u ∈ scaleSet 1 0 K₁, ⨅ v ∈ scaleSet 1 0 K₂,
            internalMetric (𝔇 (hC ω)) (scaleSet 1 0 U₀) u v} ∪ {ω | ¬ hcirc ω 1 0 = 0}) := measure_mono hsub
      _ ≤ P {ω | ENNReal.ofReal (Real.exp (δ * n) / 2 * ((1 : ℝ) ^ (ξ * lqgQ γ) * Real.exp (ξ * hcirc ω 1 0))) <
          ⨅ u ∈ scaleSet 1 0 K₁, ⨅ v ∈ scaleSet 1 0 K₂,
            internalMetric (𝔇 (hC ω)) (scaleSet 1 0 U₀) u v} + P {ω | ¬ hcirc ω 1 0 = 0} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (K₀ * (Real.exp (δ * n) / 2) ^ (-m)) + 0 := by
          refine add_le_add (hT _ hc 1 one_pos) (le_of_eq ?_)
          exact ae_iff.1 hnull
      _ ≤ ENNReal.ofReal (max (2 ^ m * K₀) ((2 * C₀) ^ m) * Real.exp (-(m * δ * n))) := by
          rw [add_zero]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : (Real.exp (δ * n) / 2) ^ (-m) = Real.exp (-(m * δ * n)) * 2 ^ m := by
            rw [Real.div_rpow hexp.le zero_lt_two.le, ← Real.exp_mul, Real.rpow_neg zero_lt_two.le, div_inv_eq_mul]
            congr 2; ring
          rw [e]
          calc K₀ * (Real.exp (-(m * δ * n)) * 2 ^ m) = (2 ^ m * K₀) * Real.exp (-(m * δ * n)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hexpm.le
  · -- small `n`: the right-hand side is at least one
    have hc : Real.exp (δ * n) / 2 < C₀ := not_le.1 hc
    have h1 : Real.exp (δ * n) ≤ 2 * C₀ := by linarith
    have h2 : Real.exp (m * δ * n) ≤ (2 * C₀) ^ m := by
      rw [show m * δ * n = δ * n * m by ring, Real.exp_mul]
      exact Real.rpow_le_rpow hexp.le h1 hm.le
    have h3 : (1 : ℝ) ≤ max (2 ^ m * K₀) ((2 * C₀) ^ m) * Real.exp (-(m * δ * n)) := by
      have h4 : (2 * C₀) ^ m ≤ max (2 ^ m * K₀) ((2 * C₀) ^ m) := le_max_right _ _
      calc (1 : ℝ) = Real.exp (m * δ * n) * Real.exp (-(m * δ * n)) := by rw [← Real.exp_add]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (h2.trans h4) hexpm.le
    calc P {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ internalSetDist (𝔇 (hC ω)) U₀ K₁ K₂} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h3

/-! ### The strip configurations of the crossing distances -/

theorem isConnected_singleton_reProdIm_Icc (x : ℝ) {a b : ℝ} (hab : a ≤ b) :
    IsConnected (({x} : Set ℝ) ×ℂ Icc a b) :=
  ⟨⟨⟨x, a⟩, Complex.mem_reProdIm.2 ⟨mem_singleton _, le_rfl, hab⟩⟩,
    (LatticeProb.Topology.convex_reProdIm (convex_singleton x) (convex_Icc a b)).isPreconnected⟩

theorem isConnected_Icc_reProdIm_singleton {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    IsConnected (Icc a b ×ℂ ({y} : Set ℝ)) :=
  ⟨⟨⟨a, y⟩, Complex.mem_reProdIm.2 ⟨⟨le_rfl, hab⟩, mem_singleton _⟩⟩,
    (LatticeProb.Topology.convex_reProdIm (convex_Icc a b) (convex_singleton y)).isPreconnected⟩

theorem nontrivial_singleton_reProdIm_Icc (x : ℝ) {a b : ℝ} (hab : a < b) :
    (({x} : Set ℝ) ×ℂ Icc a b).Nontrivial :=
  ⟨⟨x, a⟩, Complex.mem_reProdIm.2 ⟨mem_singleton _, le_rfl, hab.le⟩, ⟨x, b⟩,
    Complex.mem_reProdIm.2 ⟨mem_singleton _, hab.le, le_rfl⟩, fun h => hab.ne (by simpa using congrArg Complex.im h)⟩

theorem nontrivial_Icc_reProdIm_singleton {a b : ℝ} (hab : a < b) (y : ℝ) :
    (Icc a b ×ℂ ({y} : Set ℝ)).Nontrivial :=
  ⟨⟨a, y⟩, Complex.mem_reProdIm.2 ⟨⟨le_rfl, hab.le⟩, mem_singleton _⟩, ⟨b, y⟩,
    Complex.mem_reProdIm.2 ⟨⟨hab.le, le_rfl⟩, mem_singleton _⟩, fun h => hab.ne (by simpa using congrArg Complex.re h)⟩

theorem isConnected_Ioo_reProdIm_Ioo {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    IsConnected (Ioo a b ×ℂ Ioo c d) :=
  ⟨⟨⟨(a + b) / 2, (c + d) / 2⟩, Complex.mem_reProdIm.2 ⟨⟨by show a < (a + b) / 2; linarith, by show (a + b) / 2 < b; linarith⟩,
    ⟨by show c < (c + d) / 2; linarith, by show (c + d) / 2 < d; linarith⟩⟩⟩,
    (LatticeProb.Topology.convex_reProdIm (convex_Ioo a b) (convex_Ioo c d)).isPreconnected⟩

/-- **Exponential tail of the horizontal crossing distance.** For a γ-LQG metric with `ξ > 0`, every `y₀`, `δ`
and `m > 0`, the probability that `D_h(K₋, K₊; U)` for the horizontal strip `U = (-1, 2) × (y₀, y₀ + 1/2)` is at least
`e^{δ n}` is at most `K e^{-m δ n}`. -/
theorem IsLQGMetric.exists_measure_horizontalCrossingDist_ge_exp_le {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) (hξ : 0 < ξ) (hγ : 0 < γ) (y₀ δ m : ℝ)
    (hm : 0 < m) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {H : Ω → DistC}
    (hH : LQGMetric.IsWholePlaneGFF H P) (hHC : ∀ ψ : TestC, (fun ω => H ω ψ) =ᵐ[P] fun ω => hC ω ψ)
    (hHcirc : ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, hcirc ω r z = circleAvg (H ω) r z) :
    ∃ K : ℝ, ∀ n : ℕ,
      P {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ horizontalCrossingDist (𝔇 (hC ω)) y₀} ≤
        ENNReal.ofReal (K * Real.exp (-(m * δ * n))) := by
  have hy : (0 : ℝ) ≤ |y₀| := abs_nonneg y₀
  refine h𝔇.exists_measure_internalSetDist_ge_exp_le hξ hγ (R₀ := 4 + |y₀|) (by positivity) ?_
    (isOpen_Ioo.reProdIm isOpen_Ioo) (isConnected_Ioo_reProdIm_Ioo (by norm_num) (by linarith))
    (isCompact_singleton.reProdIm isCompact_Icc) (isConnected_singleton_reProdIm_Icc _ (by linarith))
    (nontrivial_singleton_reProdIm_Icc _ (by linarith)) (isCompact_singleton.reProdIm isCompact_Icc)
    (isConnected_singleton_reProdIm_Icc _ (by linarith)) (nontrivial_singleton_reProdIm_Icc _ (by linarith))
    ?_ ?_ δ m hm hG hH hHC hHcirc
  · intro z hz
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := Complex.mem_reProdIm.1 hz
    have hre : |z.re| < 2 := abs_lt.2 ⟨by linarith, h2⟩
    have him : |z.im| ≤ |y₀| + 1 / 2 := abs_le.2 ⟨by linarith [neg_abs_le y₀], by linarith [le_abs_self y₀]⟩
    rw [mem_ball_zero_iff]
    linarith [Complex.norm_le_abs_re_add_abs_im z]
  · intro z hz
    obtain ⟨h1, h2, h3⟩ := Complex.mem_reProdIm.1 hz
    rw [mem_singleton_iff] at h1
    exact Complex.mem_reProdIm.2 ⟨⟨by rw [h1]; norm_num, by rw [h1]; norm_num⟩, ⟨by linarith, by linarith⟩⟩
  · intro z hz
    obtain ⟨h1, h2, h3⟩ := Complex.mem_reProdIm.1 hz
    rw [mem_singleton_iff] at h1
    exact Complex.mem_reProdIm.2 ⟨⟨by rw [h1]; norm_num, by rw [h1]; norm_num⟩, ⟨by linarith, by linarith⟩⟩

/-- **Exponential tail of the vertical crossing distance.** For a γ-LQG metric with `ξ > 0`, every `x₀`, `δ`
and `m > 0`, the probability that `D_h(K₋, K₊; U)` for the vertical strip `U = (x₀, x₀ + 1/2) × (-1, 2)` is at least
`e^{δ n}` is at most `K e^{-m δ n}`. -/
theorem IsLQGMetric.exists_measure_verticalCrossingDist_ge_exp_le {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) (hξ : 0 < ξ) (hγ : 0 < γ) (x₀ δ m : ℝ)
    (hm : 0 < m) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {H : Ω → DistC}
    (hH : LQGMetric.IsWholePlaneGFF H P) (hHC : ∀ ψ : TestC, (fun ω => H ω ψ) =ᵐ[P] fun ω => hC ω ψ)
    (hHcirc : ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, hcirc ω r z = circleAvg (H ω) r z) :
    ∃ K : ℝ, ∀ n : ℕ,
      P {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ verticalCrossingDist (𝔇 (hC ω)) x₀} ≤
        ENNReal.ofReal (K * Real.exp (-(m * δ * n))) := by
  have hx : (0 : ℝ) ≤ |x₀| := abs_nonneg x₀
  refine h𝔇.exists_measure_internalSetDist_ge_exp_le hξ hγ (R₀ := 4 + |x₀|) (by positivity) ?_
    (isOpen_Ioo.reProdIm isOpen_Ioo) (isConnected_Ioo_reProdIm_Ioo (by linarith) (by norm_num))
    (isCompact_Icc.reProdIm isCompact_singleton) (isConnected_Icc_reProdIm_singleton (by linarith) _)
    (nontrivial_Icc_reProdIm_singleton (by linarith) _) (isCompact_Icc.reProdIm isCompact_singleton)
    (isConnected_Icc_reProdIm_singleton (by linarith) _) (nontrivial_Icc_reProdIm_singleton (by linarith) _)
    ?_ ?_ δ m hm hG hH hHC hHcirc
  · intro z hz
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := Complex.mem_reProdIm.1 hz
    have him : |z.im| < 2 := abs_lt.2 ⟨by linarith, h4⟩
    have hre : |z.re| ≤ |x₀| + 1 / 2 := abs_le.2 ⟨by linarith [neg_abs_le x₀], by linarith [le_abs_self x₀]⟩
    rw [mem_ball_zero_iff]
    linarith [Complex.norm_le_abs_re_add_abs_im z]
  · intro z hz
    obtain ⟨⟨h1, h2⟩, h3⟩ := Complex.mem_reProdIm.1 hz
    rw [mem_singleton_iff] at h3
    exact Complex.mem_reProdIm.2 ⟨⟨by linarith, by linarith⟩, ⟨by rw [h3]; norm_num, by rw [h3]; norm_num⟩⟩
  · intro z hz
    obtain ⟨⟨h1, h2⟩, h3⟩ := Complex.mem_reProdIm.1 hz
    rw [mem_singleton_iff] at h3
    exact Complex.mem_reProdIm.2 ⟨⟨by linarith, by linarith⟩, ⟨by rw [h3]; norm_num, by rw [h3]; norm_num⟩⟩

end LatticeProb.LQG
