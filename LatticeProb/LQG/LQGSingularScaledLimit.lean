import LatticeProb.LQG.GMCAffineCovariance
import LatticeProb.LQG.GMCDilationField
import LatticeProb.LQG.GMCScaleIncrement
import LatticeProb.LQG.LQGMeasureExistenceProved

/-!
# The LQG measure with a logarithmic singularity along the scales `c 2^{-k}`, and its affine coordinate change

Let `h` be a whole-plane Gaussian free field, `0 < γ < 2`, `α < Q`, and let `μ` be the γ-LQG measure of
`h - α log |·|`, the almost sure vague limit of the circle-average approximations
`ν_ε = ε^{γ²/2} e^{γ (h_ε - α log max(ε, |·|))} d²z` along the dyadic scales `ε = 2^{-k}`. For every fixed `c > 0`,
almost surely `ν_{c 2^{-k}}` also converges vaguely to `μ`. Consequently, for every fixed `a ≠ 0` and `b`, almost
surely the push-forward of `μ` under `x ↦ (x - b)/a` is the vague limit of the approximations of the field
`x ↦ h(a x + b) - α log |a x + b| + Q log |a|` (the LQG coordinate change formula, Duplantier-Sheffield 2011,
Proposition 2.1, for one affine map at a time).

The proof runs the Cauchy argument of the singular field along the interleaved scales
`2^0, c 2^0, 2^{-1}, c 2^{-1}, …`: along them the approximations without the singularity converge (the scale-ratio
increment bound), and the mass near the origin is uniformly small, along the dyadic scales by the moment bound at the
origin and along `c 2^{-k}` by the same bound for the dilated field `h(c ·) - h_c(0)`, again a whole-plane GFF. The
even subsequence identifies the limit with `μ`.

Main results:
* `exists_tendsto_integral_lqgApprox_fieldCircleAverage_seq`: the Cauchy argument along any scales `σ_n → 0`.
* `ae_origin_mul_dyadicScale`: the mass of `ν_{c 2^{-k}}` near the origin is uniformly small, almost surely.
* `ae_isLQGLimitAlong_fieldCircleAverage_mul`: almost surely `ν_{c 2^{-k}} → μ` vaguely.
* `ae_isLQGLimit_affine_fieldCircleAverage`: the coordinate change under one affine map.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

open LatticeProb.Gauss

namespace LatticeProb.LQG

namespace LQGSingularScaledLimit

open LatticeProb.LQG.ProfileDerived (isLocallyFiniteMeasure_lqgApprox)
open LatticeProb.LQG.LQGMeasureExistenceSingular (integral_lqgApprox_fieldCircleAverage continuous_max_norm_rpow
  continuous_fieldCircleAverage_of_continuous fieldCircleAverage_zero)
open LatticeProb.LQG.LQGWeylScalingDerived (ae_continuous_fieldCircleAverage_of_isWholePlaneGFF)

/-- A sequence converges if its even and its odd subsequences converge to the same limit. -/
theorem tendsto_of_tendsto_even_odd {X : Type*} {u : ℕ → X} {l : Filter X}
    (h0 : Tendsto (fun k => u (2 * k)) atTop l) (h1 : Tendsto (fun k => u (2 * k + 1)) atTop l) :
    Tendsto u atTop l := by
  intro s hs
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (h0.eventually_mem hs)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (h1.eventually_mem hs)
  rw [Filter.mem_map, mem_atTop_sets]
  refine ⟨2 * (N0 + N1) + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact hN0 k (by omega)
  · exact hN1 k (by omega)

theorem dyadicScale_pos'' (k : ℕ) : 0 < dyadicScale k := pow_pos (by norm_num) k

theorem tendsto_dyadicScale_zero : Tendsto dyadicScale atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- **The Cauchy argument along arbitrary scales.** Let `σ_n > 0`, `σ_n → 0`. If the approximations of `h` converge
vaguely along `σ_n` and the singular approximations have uniformly small mass near the origin along `σ_n`, then
`∫ f dν_{σ_n}` converges for every continuous compactly supported `f`. -/
theorem exists_tendsto_integral_lqgApprox_fieldCircleAverage_seq {γ α₀ : ℝ} {hcirc : ℝ → ℂ → ℝ} {σ : ℕ → ℝ}
    (hσ : ∀ n, 0 < σ n) (hσ0 : Tendsto σ atTop (𝓝 0))
    (hm : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      ∃ ℓ : ℝ, Tendsto (fun n : ℕ => ∫ z, g z ∂(lqgApprox γ hcirc (σ n))) atTop (𝓝 ℓ))
    (hc : ∀ n : ℕ, Continuous (hcirc (σ n)))
    (horigin : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
      lqgApprox γ (fieldCircleAverage α₀ hcirc) (σ k) (ball 0 δ) ≤ ENNReal.ofReal η)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ ℓ : ℝ, Tendsto (fun k : ℕ =>
      ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α₀ hcirc) (σ k))) atTop (𝓝 ℓ) := by
  set ν : ℕ → Measure ℂ := fun k => lqgApprox γ (fieldCircleAverage α₀ hcirc) (σ k) with hν
  have hνfin : ∀ k, IsLocallyFiniteMeasure (ν k) := fun k =>
    isLocallyFiniteMeasure_lqgApprox γ (continuous_fieldCircleAverage_of_continuous (hσ k) (hc k))
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  set η : ℝ := ε / (4 * (C + 1)) with hηdef
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, K, hK⟩ := horigin η hη
  let b : ContDiffBump (0 : ℂ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  set p : ℝ := -(γ * α₀)
  set g : ℂ → ℝ := fun z => f z * ((1 - b z) * max (δ / 2) ‖z‖ ^ p) with hgdef
  have hgc : Continuous g :=
    hf.mul ((continuous_const.sub b.continuous).mul (continuous_max_norm_rpow (by positivity) p))
  have hgs : HasCompactSupport g := hfc.mul_right
  obtain ⟨ℓg, hℓg⟩ := hm g hgc hgs
  have hG := hℓg.cauchySeq
  rw [Metric.cauchySeq_iff] at hG
  obtain ⟨N1, hN1⟩ := hG (ε / 2) (by positivity)
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp (hσ0.eventually (ge_mem_nhds (half_pos hδ)))
  have hsplit : ∀ k ≥ max N2 K, |∫ z, f z ∂(ν k) - ∫ z, g z ∂(lqgApprox γ hcirc (σ k))| ≤ C * η := by
    intro k hk
    have hk2 : σ k ≤ δ / 2 := hN2 k (le_of_max_le_left hk)
    have hkK : K ≤ k := le_of_max_le_right hk
    have := hνfin k
    have hfb : Integrable (fun z => f z * b z) (ν k) :=
      (hf.mul b.continuous).integrable_of_hasCompactSupport hfc.mul_right
    have hfb' : Integrable (fun z => f z * (1 - b z)) (ν k) :=
      (hf.mul (continuous_const.sub b.continuous)).integrable_of_hasCompactSupport hfc.mul_right
    have hsum : ∫ z, f z ∂(ν k) = ∫ z, f z * b z ∂(ν k) + ∫ z, f z * (1 - b z) ∂(ν k) := by
      rw [← integral_add hfb hfb']
      congr 1
      funext z
      ring
    have hfar : ∫ z, f z * (1 - b z) ∂(ν k) = ∫ z, g z ∂(lqgApprox γ hcirc (σ k)) := by
      rw [hν]
      simp only
      rw [integral_lqgApprox_fieldCircleAverage (hσ k) hcirc (hc k)]
      congr 1
      funext z
      by_cases hz : ‖z‖ ≤ δ / 2
      · have h1 : b z = 1 := b.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
        simp [hgdef, h1]
      · replace hz := not_le.mp hz
        have e1 : max (σ k) ‖z‖ = ‖z‖ := max_eq_right (hk2.trans hz.le)
        have e2 : max (δ / 2) ‖z‖ = ‖z‖ := max_eq_right hz.le
        simp only [hgdef, e1, e2]
        ring
    have hnear : |∫ z, f z * b z ∂(ν k)| ≤ C * η := by
      have hzero : ∀ z, z ∉ ball (0 : ℂ) δ → f z * b z = 0 := by
        intro z hz
        have : b z = 0 := b.zero_of_le_dist (by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hz)
        simp [this]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
      have hfin : ν k (ball 0 δ) < ∞ := (hK k hkK).trans_lt ENNReal.ofReal_lt_top
      have hb := norm_setIntegral_le_of_norm_le_const (μ := ν k) (f := fun z => f z * b z) (C := C) hfin
        (fun z _ => by
          rw [norm_mul, Real.norm_of_nonneg b.nonneg]
          exact (mul_le_of_le_one_right (norm_nonneg _) b.le_one).trans (hC z))
      rw [Real.norm_eq_abs] at hb
      refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      exact ENNReal.toReal_le_of_le_ofReal hη.le (hK k hkK)
    rw [hsum, hfar]
    simpa using hnear
  refine ⟨max N1 (max N2 K), fun k hk l hl => ?_⟩
  have hk' : max N2 K ≤ k := le_of_max_le_right hk
  have hl' : max N2 K ≤ l := le_of_max_le_right hl
  have h1 := hsplit k hk'
  have h2 := hsplit l hl'
  have h3 := hN1 k (le_of_max_le_left hk) l (le_of_max_le_left hl)
  rw [Real.dist_eq] at h3 ⊢
  have hCη : C * η < ε / 4 := by
    rw [hηdef, mul_div_assoc']
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have t1 := abs_sub_le (∫ z, f z ∂(ν k)) (∫ z, g z ∂(lqgApprox γ hcirc (σ k))) (∫ z, f z ∂(ν l))
  have t2 := abs_sub_le (∫ z, g z ∂(lqgApprox γ hcirc (σ k)))
    (∫ z, g z ∂(lqgApprox γ hcirc (σ l))) (∫ z, f z ∂(ν l))
  have t3 := abs_sub_comm (∫ z, g z ∂(lqgApprox γ hcirc (σ l))) (∫ z, f z ∂(ν l))
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Mass near the origin along the dyadic scales.** For a whole-plane GFF, `0 < γ < 2` and `α < Q`, almost surely
the singular approximations at the scales `2^{-k}` have uniformly small mass near the origin. -/
theorem ae_origin_dyadicScale (hG : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hαQ : α < lqgQ γ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball 0 δ) ≤ ENNReal.ofReal η := by
  filter_upwards [hG.ae_eventually_exp_circle_mul_maximal_dilated_le hγ hγ2] with ω hω
  exact LQGMeasureOriginBound.exists_lqgApprox_fieldCircleAverage_ball_le_of_eventually hγ hαQ (hcirc ω) hω

/-- **Mass near the origin along the scales `c 2^{-k}`.** For a whole-plane GFF, `0 < γ < 2`, `α < Q` and `c > 0`,
almost surely the singular approximations at the scales `c 2^{-k}` have uniformly small mass near the origin. They
are a positive multiple of the dyadic approximations of the dilated field `h(c ·) - h_c(0)`, pushed forward under
`w ↦ c w`. -/
theorem ae_origin_mul_dyadicScale (hG : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hαQ : α < lqgQ γ) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) (c * dyadicScale k) (ball 0 δ) ≤ ENNReal.ofReal η := by
  obtain ⟨hC', hG'⟩ := isWholePlaneGFF_dilateRecentre hG hc
  filter_upwards [ae_origin_dyadicScale hG' hγ hγ2 hαQ] with ω hω η hη
  set A : ℝ := c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * hcirc ω c 0) with hA
  have hA0 : 0 < A := mul_pos (Real.rpow_pos_of_pos hc _) (Real.exp_pos _)
  obtain ⟨δ, hδ, K, hK⟩ := hω (η / A) (div_pos hη hA0)
  refine ⟨c * δ, mul_pos hc hδ, K, fun k hk => ?_⟩
  have hmeas : Measurable (fun w : ℂ => (c : ℂ) * w) := measurable_const.mul measurable_id
  rw [lqgApprox_fieldCircleAverage_dilation hγ.ne' α (hcirc ω) hc (dyadicScale_pos'' k), Measure.smul_apply,
    Measure.map_apply hmeas measurableSet_ball, preimage_mul_ofReal_ball hc, smul_eq_mul]
  calc ENNReal.ofReal A *
        lqgApprox γ (fieldCircleAverage α (dilateRecentre c (hcirc ω))) (dyadicScale k) (ball 0 δ)
      ≤ ENNReal.ofReal A * ENNReal.ofReal (η / A) := by gcongr; exact hK k hk
    _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_mul hA0.le, mul_div_cancel₀ η hA0.ne']

/-- **The singular approximations converge along `c 2^{-k}` to the LQG measure.** For a whole-plane GFF,
`0 < γ < 2`, `α < Q`, the γ-LQG measure `μ` of `h - α log |·|` and `c > 0`, almost surely the approximations at the
scales `c 2^{-k}` converge vaguely to `μ`. -/
theorem ae_isLQGLimitAlong_fieldCircleAverage_mul (hG : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hαQ : α < lqgQ γ) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) {c : ℝ}
    (hc : 0 < c) :
    ∀ᵐ ω ∂P, IsLQGLimitAlong γ (fieldCircleAverage α (hcirc ω)) (fun k => c * dyadicScale k) (μ ω) := by
  obtain ⟨μ₀, hμ₀⟩ := hG.exists_isLQGMeasure hγ hγ2
  have hμ₀' : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ₀ ω) := hμ₀
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  have hcont : ∀ᵐ ω ∂P, ∀ n : ℕ, Continuous (hcirc ω (interleavedScale c n)) := by
    refine ae_all_iff.mpr fun n => ?_
    filter_upwards [ae_continuous_fieldCircleAverage_of_isWholePlaneGFF hG 0 (interleavedScale_pos hc n)]
      with ω hω
    simpa [fieldCircleAverage_zero] using hω
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => by omega⟩
  have h2' : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => by omega⟩
  filter_upwards [hμ', hμ₀', hG.ae_tendsto_integral_lqgApprox_mul (hG.scaleIncrementL1Bound hγ hγ2) hμ₀ hc,
    ae_origin_dyadicScale hG hγ hγ2 hαQ, ae_origin_mul_dyadicScale hG hγ hγ2 hαQ hc, hcont]
    with ω h1 h0 hmul hO1 hOc hct
  refine ⟨h1.isLocallyFiniteMeasure, fun f hf hfc => ?_⟩
  have hσ : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → ∃ ℓ : ℝ,
      Tendsto (fun n : ℕ => ∫ z, g z ∂(lqgApprox γ (hcirc ω) (interleavedScale c n))) atTop (𝓝 ℓ) := by
    intro g hg hgs
    refine ⟨∫ z, g z ∂(μ₀ ω), tendsto_of_tendsto_even_odd ?_ ?_⟩
    · simpa only [interleavedScale_two_mul] using h0.tendsto_integral g hg hgs
    · simpa only [interleavedScale_two_mul_add_one] using hmul g hg hgs
  have hσ0 : Tendsto (interleavedScale c) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_even_odd ?_ ?_
    · simpa only [interleavedScale_two_mul] using tendsto_dyadicScale_zero
    · simpa only [interleavedScale_two_mul_add_one, mul_zero] using tendsto_dyadicScale_zero.const_mul c
  have hOσ : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ n ≥ K,
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) (interleavedScale c n) (ball 0 δ) ≤ ENNReal.ofReal η := by
    intro η hη
    obtain ⟨δ1, hδ1, K1, hK1⟩ := hO1 η hη
    obtain ⟨δ2, hδ2, K2, hK2⟩ := hOc η hη
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, 2 * (K1 + K2), fun n hn => ?_⟩
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [interleavedScale_two_mul]
      exact (measure_mono (ball_subset_ball (min_le_left _ _))).trans (hK1 k (by omega))
    · rw [interleavedScale_two_mul_add_one]
      exact (measure_mono (ball_subset_ball (min_le_right _ _))).trans (hK2 k (by omega))
  obtain ⟨ℓ, hℓ⟩ := exists_tendsto_integral_lqgApprox_fieldCircleAverage_seq (interleavedScale_pos hc) hσ0 hσ hct
    hOσ hf hfc
  have heven := hℓ.comp h2
  have hodd := hℓ.comp h2'
  simp only [Function.comp_def, interleavedScale_two_mul, interleavedScale_two_mul_add_one] at heven hodd
  have hl : ℓ = ∫ z, f z ∂(μ ω) := tendsto_nhds_unique heven (h1.tendsto_integral f hf hfc)
  rw [← hl]
  exact hodd

/-- **Coordinate change of the LQG measure with a logarithmic singularity, one affine map at a time.** For a
whole-plane GFF, `0 < γ < 2`, `α < Q`, the γ-LQG measure `μ` of `h - α log |·|`, `a ≠ 0` and `b`, almost surely
`(x ↦ (x - b)/a)_* μ` is the vague limit of the approximations of `x ↦ h(a x + b) - α log |a x + b| + Q log |a|`
(circle averages of radius `|a| ε` about `a x + b`). -/
theorem ae_isLQGLimit_affine_fieldCircleAverage (hG : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hαQ : α < lqgQ γ) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) {a : ℂ}
    (ha : a ≠ 0) (b : ℂ) :
    ∀ᵐ ω ∂P, IsLQGLimit γ (affineField γ a b (fieldCircleAverage α (hcirc ω))) ((μ ω).map (affineChart a b)) := by
  filter_upwards [ae_isLQGLimitAlong_fieldCircleAverage_mul hG hγ hγ2 hαQ hμ (norm_pos_iff.2 ha)] with ω hω
  exact isLQGLimit_affine_map_of_along hγ.ne' _ ha b hω

end LQGSingularScaledLimit

end LatticeProb.LQG
