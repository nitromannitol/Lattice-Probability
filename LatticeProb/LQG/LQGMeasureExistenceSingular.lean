import LatticeProb.LQG.LQGMeasureExistenceNonpos

/-! # The LQG measure with a logarithmic singularity: reduction to the mass near the origin

For the field `h - α₀ log |·|` the circle-average approximations are
`ν_ε(dz) = max(ε, |z|)^{-γα₀} m_ε(dz)`, where `m_ε = ε^{γ²/2} e^{γ h_ε(z)} dz` are the approximations without the
singularity. Away from the origin the weight does not depend on `ε` once `ε` is small, so a vague limit of `m_ε`
gives convergence of `∫ f dν_ε` for every continuous compactly supported `f`, provided the mass of `ν_ε` near the
origin is uniformly small:

  `∀ η > 0, ∃ δ > 0, ∃ K, ∀ k ≥ K, ν_{2^{-k}}(B(0, δ)) ≤ η`.

No sign condition on `α₀` is used. Together with the existence of the vague limit of `m_ε`
(`LatticeProb.Gauss.IsWholePlaneGFF.exists_isLQGMeasure`) this reduces the existence of the LQG measure of
`h^ℂ - α₀ log |·|` to an almost sure bound on the mass near the origin (Duplantier-Sheffield 2011, Section 3; the
bound uses `α₀ < Q`).

Main results:
* `lqgApprox_fieldCircleAverage_eq_withDensity_rpow`: `ν_ε = max(ε, |·|)^{-γα₀} m_ε` for every `α₀`.
* `exists_tendsto_integral_lqgApprox_fieldCircleAverage`: the Cauchy argument for one test function.
* `exists_isLQGLimit_fieldCircleAverage_of_origin`: existence of the vague limit of `ν_{2^{-k}}`.
* `lqgMeasureExistenceLP_of_ae_origin`: `LQGMeasureExistenceLP` from the almost sure bound near the origin.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal
open LatticeProb.Gauss

namespace LatticeProb.LQG

namespace LQGMeasureExistenceSingular

open LatticeProb.LQG.ProfileDerived (dyadicScale_pos isLocallyFiniteMeasure_lqgApprox
  continuous_circleAverage_log_norm)
open LatticeProb.LQG.LQGWeylScalingDerived (ae_continuous_fieldCircleAverage_of_isWholePlaneGFF)
open LatticeProb.LQG.LQGMeasureNonatomicOrigin (fieldCircleAverage_eq_log)
open LatticeProb.LQG.LQGMeasureExistenceNonpos (integral_withDensity_ofReal_eq_integral_mul)

/-- The field circle average without singularity is the circle average itself. -/
theorem fieldCircleAverage_zero (hcirc : ℝ → ℂ → ℝ) : fieldCircleAverage 0 hcirc = hcirc := by
  funext r z
  simp [fieldCircleAverage]

/-- `max(r, |z|)^p` is continuous in `z` for `r > 0` and every exponent `p`. -/
theorem continuous_max_norm_rpow {r : ℝ} (hr : 0 < r) (p : ℝ) :
    Continuous fun z : ℂ => max r ‖z‖ ^ p :=
  (continuous_const.max continuous_norm).rpow_const fun _ => Or.inl (ne_of_gt (lt_max_of_lt_left hr))

/-- The approximation of the field `h - α₀ log |·|` is the approximation of `h` reweighted by `max(r, |z|)^{-γα₀}`. -/
theorem lqgApprox_fieldCircleAverage_eq_withDensity_rpow {γ α₀ r : ℝ} (hr : 0 < r) (hcirc : ℝ → ℂ → ℝ)
    (hc : Continuous (hcirc r)) :
    lqgApprox γ (fieldCircleAverage α₀ hcirc) r =
      (lqgApprox γ hcirc r).withDensity (fun z => ENNReal.ofReal (max r ‖z‖ ^ (-(γ * α₀)))) := by
  have ha : Measurable (fun z => ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc r z))) :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul hc))).measurable
  have hb : Measurable (fun z => ENNReal.ofReal (max r ‖z‖ ^ (-(γ * α₀)))) :=
    ENNReal.measurable_ofReal.comp (continuous_max_norm_rpow hr _).measurable
  simp only [lqgApprox]
  rw [← withDensity_mul volume ha hb]
  apply withDensity_congr_ae
  filter_upwards [] with z
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_nonneg _))]
  congr 1
  rw [Real.rpow_def_of_pos (lt_max_of_lt_left hr)]
  have he : γ * fieldCircleAverage α₀ hcirc r z =
      γ * hcirc r z + Real.log (max r ‖z‖) * (-(γ * α₀)) := by
    rw [fieldCircleAverage_eq_log α₀ hcirc hr]
    ring
  rw [he, Real.exp_add]
  ring

/-- Integrals against the singular approximation are integrals against the approximation without singularity with
the weight `max(r, |z|)^{-γα₀}`. -/
theorem integral_lqgApprox_fieldCircleAverage {γ α₀ r : ℝ} (hr : 0 < r) (hcirc : ℝ → ℂ → ℝ)
    (hc : Continuous (hcirc r)) (φ : ℂ → ℝ) :
    ∫ z, φ z ∂(lqgApprox γ (fieldCircleAverage α₀ hcirc) r) =
      ∫ z, φ z * max r ‖z‖ ^ (-(γ * α₀)) ∂(lqgApprox γ hcirc r) := by
  rw [lqgApprox_fieldCircleAverage_eq_withDensity_rpow hr hcirc hc]
  exact integral_withDensity_ofReal_eq_integral_mul _ _ φ (continuous_max_norm_rpow hr _)
    (fun z => Real.rpow_nonneg (le_max_of_le_left hr.le) _)

/-- Circle averages of `h - α₀ log |·|` are continuous in the centre when those of `h` are. -/
theorem continuous_fieldCircleAverage_of_continuous {α₀ r : ℝ} (hr : 0 < r) {hcirc : ℝ → ℂ → ℝ}
    (hc : Continuous (hcirc r)) : Continuous (fieldCircleAverage α₀ hcirc r) := by
  unfold fieldCircleAverage
  exact hc.sub (continuous_const.mul (continuous_circleAverage_log_norm hr))

/-- **Cauchy argument.** If the approximations `m_k` of `h` converge vaguely and the singular approximations `ν_k`
have uniformly small mass near the origin, then `∫ f dν_k` converges for every continuous compactly supported `f`. -/
theorem exists_tendsto_integral_lqgApprox_fieldCircleAverage {γ α₀ : ℝ} {hcirc : ℝ → ℂ → ℝ}
    {m : Measure ℂ} (hm : IsLQGLimit γ hcirc m) (hc : ∀ k : ℕ, Continuous (hcirc (dyadicScale k)))
    (horigin : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
      lqgApprox γ (fieldCircleAverage α₀ hcirc) (dyadicScale k) (ball 0 δ) ≤ ENNReal.ofReal η)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ ℓ : ℝ, Tendsto (fun k : ℕ =>
      ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α₀ hcirc) (dyadicScale k))) atTop (𝓝 ℓ) := by
  set ν : ℕ → Measure ℂ := fun k => lqgApprox γ (fieldCircleAverage α₀ hcirc) (dyadicScale k) with hν
  have hνfin : ∀ k, IsLocallyFiniteMeasure (ν k) := fun k =>
    isLocallyFiniteMeasure_lqgApprox γ (continuous_fieldCircleAverage_of_continuous (dyadicScale_pos k) (hc k))
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
  have hG := (hm.tendsto_integral g hgc hgs).cauchySeq
  rw [Metric.cauchySeq_iff] at hG
  obtain ⟨N1, hN1⟩ := hG (ε / 2) (by positivity)
  have hscale : Tendsto dyadicScale atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp (hscale.eventually (ge_mem_nhds (half_pos hδ)))
  -- decomposition of `∫ f dν_k` for large `k`
  have hsplit : ∀ k ≥ max N2 K, |∫ z, f z ∂(ν k) - ∫ z, g z ∂(lqgApprox γ hcirc (dyadicScale k))| ≤ C * η := by
    intro k hk
    have hk2 : dyadicScale k ≤ δ / 2 := hN2 k (le_of_max_le_left hk)
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
    have hfar : ∫ z, f z * (1 - b z) ∂(ν k) = ∫ z, g z ∂(lqgApprox γ hcirc (dyadicScale k)) := by
      rw [hν]
      simp only
      rw [integral_lqgApprox_fieldCircleAverage (dyadicScale_pos k) hcirc (hc k)]
      congr 1
      funext z
      by_cases hz : ‖z‖ ≤ δ / 2
      · have h1 : b z = 1 := b.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
        simp [hgdef, h1]
      · replace hz := not_le.mp hz
        have e1 : max (dyadicScale k) ‖z‖ = ‖z‖ := max_eq_right (hk2.trans hz.le)
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
  have t1 := abs_sub_le (∫ z, f z ∂(ν k)) (∫ z, g z ∂(lqgApprox γ hcirc (dyadicScale k)))
    (∫ z, f z ∂(ν l))
  have t2 := abs_sub_le (∫ z, g z ∂(lqgApprox γ hcirc (dyadicScale k)))
    (∫ z, g z ∂(lqgApprox γ hcirc (dyadicScale l))) (∫ z, f z ∂(ν l))
  have t3 := abs_sub_comm (∫ z, g z ∂(lqgApprox γ hcirc (dyadicScale l))) (∫ z, f z ∂(ν l))
  linarith

/-- **Existence of the vague limit with the singularity.** If the approximations of `h` converge vaguely and the
singular approximations have uniformly small mass near the origin, then the singular approximations converge
vaguely along the dyadic scales to a Radon measure. -/
theorem exists_isLQGLimit_fieldCircleAverage_of_origin {γ α₀ : ℝ} {hcirc : ℝ → ℂ → ℝ}
    {m : Measure ℂ} (hm : IsLQGLimit γ hcirc m) (hc : ∀ k : ℕ, Continuous (hcirc (dyadicScale k)))
    (horigin : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
      lqgApprox γ (fieldCircleAverage α₀ hcirc) (dyadicScale k) (ball 0 δ) ≤ ENNReal.ofReal η) :
    ∃ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α₀ hcirc) μ := by
  obtain ⟨D, -, hDcc, hD⟩ := exists_countable_determining_isLQGLimit
  exact hD γ _ (fun k => continuous_fieldCircleAverage_of_continuous (dyadicScale_pos k) (hc k))
    (fun g hg => exists_tendsto_integral_lqgApprox_fieldCircleAverage hm hc horigin (hDcc g hg).1 (hDcc g hg).2)

/-- **Reduction of the existence to the mass near the origin.** For a whole-plane GFF, `0 < γ < 2` and `α₀ < Q`,
an almost sure uniform bound on the mass of the singular approximations near the origin gives the existence of the
LQG measure of `h^ℂ - α₀ log |·|`. -/
theorem lqgMeasureExistenceLP_of_ae_origin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ α₀ : ℝ}
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (horigin : IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
        lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale k) (ball 0 δ) ≤ ENNReal.ofReal η) :
    LQGMeasureExistenceLP P γ α₀ hC hcirc := by
  intro hG hγ hγ2 hQ
  obtain ⟨μ₀, hμ₀⟩ := hG.exists_isLQGMeasure hγ hγ2
  have hc : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (hcirc ω (dyadicScale k)) := by
    refine ae_all_iff.mpr fun k => ?_
    filter_upwards [ae_continuous_fieldCircleAverage_of_isWholePlaneGFF hG 0 (dyadicScale_pos k)] with ω hω
    simpa [fieldCircleAverage_zero] using hω
  have hex : ∀ᵐ ω ∂P, ∃ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) μ := by
    filter_upwards [hμ₀, hc, horigin hG hγ hγ2 hQ] with ω h1 h2 h3
    exact exists_isLQGLimit_fieldCircleAverage_of_origin h1 h2 h3
  classical
  refine ⟨fun ω => if h : ∃ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) μ then h.choose
    else 0, ?_⟩
  unfold IsLQGMeasureOfField IsLQGMeasure
  filter_upwards [hex] with ω hω
  split_ifs
  exact hω.choose_spec

end LQGMeasureExistenceSingular

end LatticeProb.LQG
