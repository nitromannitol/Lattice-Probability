import Mathlib

/-!
# A Hölder bound for the Riesz kernel on balls

Let `E` be a finite-dimensional real inner product space of dimension `d ≥ 1` with an additive Haar
measure `μ`, and let `p > d`. For every ball `B(a, r)`, every `z ∈ B(a, r)` and every measurable
`g : E → ℝ≥0∞`,
`∫_{B(a, r)} ‖w - z‖^{1-d} g(w) dμ(w) ≤ C r^{1 - d/p} (∫_{B(a, r)} g^p dμ)^{1/p}`,
with a constant `C` that depends only on `E`, `μ` and `p`.

The proof is Hölder's inequality with the conjugate exponent `q = p / (p - 1)`. The function
`‖w‖^{(1-d) q}` is integrable on the unit ball since `(1 - d) q > -d`, which is equivalent to
`p > d`, and the Haar measure scales its integral over `B(0, R)` by `R^{d + (1-d) q}`.

## Main results

* `LatticeProb.PegdenSmart.lintegral_ball_enorm_sub_rpow`: the integral of `‖w - z‖^t` over
  `B(z, R)` is `R^{d + t}` times the integral of `‖v‖^t` over the unit ball centred at `0`.
* `LatticeProb.PegdenSmart.lintegral_ball_enorm_rpow_lt_top`: the latter integral is finite for
  `t > -d`.
* `LatticeProb.PegdenSmart.rieszKernel_holder`: the Hölder bound.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace LatticeProb.PegdenSmart

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The integral of `‖w - z‖^t` over the ball `B(z, R)` is `R^{d + t}` times the integral of `‖v‖^t`
over the unit ball centred at `0`. -/
theorem lintegral_ball_enorm_sub_rpow (z : E) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    ∫⁻ w in ball z R, ‖w - z‖ₑ ^ t ∂μ =
      ENNReal.ofReal R ^ ((Module.finrank ℝ E : ℝ) + t) *
        ∫⁻ v in ball (0 : E) 1, ‖v‖ₑ ^ t ∂μ := by
  set F : E → ℝ≥0∞ := (ball (0 : E) R).indicator fun v => ‖v‖ₑ ^ t with hF
  have hFm : Measurable F := (measurable_enorm.pow_const t).indicator measurableSet_ball
  have h1 : ∫⁻ w in ball z R, ‖w - z‖ₑ ^ t ∂μ = ∫⁻ w, F w ∂μ := by
    rw [← lintegral_indicator measurableSet_ball, ← lintegral_sub_right_eq_self F z]
    congr 1
    ext w
    simp only [F, indicator, mem_ball_iff_norm, sub_zero]
  have h2 : ∫⁻ x, F (R • x) ∂μ =
      ENNReal.ofReal R ^ t * ∫⁻ v in ball (0 : E) 1, ‖v‖ₑ ^ t ∂μ := by
    rw [← lintegral_indicator measurableSet_ball,
      ← lintegral_const_mul _ ((measurable_enorm.pow_const t).indicator measurableSet_ball)]
    congr 1
    ext x
    simp only [F, indicator, mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hR.le,
      mul_lt_iff_lt_one_right hR]
    split_ifs
    · rw [enorm_smul, Real.enorm_eq_ofReal hR.le,
        ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top enorm_ne_top]
    · rw [mul_zero]
  have h3 : ∫⁻ x, F (R • x) ∂μ =
      ENNReal.ofReal |(R ^ Module.finrank ℝ E)⁻¹| * ∫⁻ w, F w ∂μ := by
    rw [← lintegral_map hFm (measurable_const_smul R), Measure.map_addHaar_smul μ hR.ne',
      lintegral_smul_measure, smul_eq_mul]
  have h4 : ENNReal.ofReal (R ^ Module.finrank ℝ E) *
      ENNReal.ofReal |(R ^ Module.finrank ℝ E)⁻¹| = 1 := by
    rw [abs_of_pos (inv_pos.2 (pow_pos hR _)), ← ENNReal.ofReal_mul (pow_nonneg hR.le _),
      mul_inv_cancel₀ (pow_pos hR _).ne', ENNReal.ofReal_one]
  rw [h1, ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 hR).ne' ENNReal.ofReal_ne_top,
    ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hR.le, mul_assoc, ← h2, h3, ← mul_assoc, h4,
    one_mul]

/-- The integral of `‖v‖^t` over the unit ball is finite for `t > -d`. -/
theorem lintegral_ball_enorm_rpow_lt_top [Nontrivial E] {t : ℝ}
    (ht : -(Module.finrank ℝ E : ℝ) < t) :
    ∫⁻ v in ball (0 : E) 1, ‖v‖ₑ ^ t ∂μ < ⊤ := by
  have hint : IntegrableOn (fun v : E => ‖v‖ ^ t) (ball 0 1) μ :=
    integrableOn_ball_of_norm_le_rpow Module.finrank_pos (C := 1) (α := -t) (by linarith)
      (Filter.Eventually.of_forall fun v => by
        rw [one_mul, neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg v) t)])
      (measurable_norm.pow_const t).aestronglyMeasurable
  refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hint.2
  filter_upwards [ae_restrict_of_ae (μ.ae_ne 0)] with v hv
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg v) t), ← ofReal_norm,
    ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 hv)]

end Scaling

/-- Hölder bound for the Riesz kernel `‖w - z‖^{1-d}` on a ball, for `p > d`: the constant depends
on `E`, `μ` and `p` only. -/
theorem rieszKernel_holder (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (p : ℝ) (hp : (Module.finrank ℝ E : ℝ) < p) :
    ∃ C : ℝ≥0, ∀ (a z : E) (r : ℝ), 0 < r → z ∈ ball a r → ∀ g : E → ℝ≥0∞, Measurable g →
      ∫⁻ w in ball a r, ‖w - z‖ₑ ^ (1 - (Module.finrank ℝ E : ℝ)) * g w ∂μ ≤
        (C : ℝ≥0∞) * ENNReal.ofReal r ^ (1 - (Module.finrank ℝ E : ℝ) / p) *
          (∫⁻ w in ball a r, g w ^ p ∂μ) ^ (1 / p) := by
  set d : ℝ := (Module.finrank ℝ E : ℝ) with hd_def
  have hd : 1 ≤ d := by rw [hd_def]; exact_mod_cast Module.finrank_pos
  have hp1 : 1 < p := hd.trans_lt hp
  set q : ℝ := p / (p - 1) with hq_def
  have hpq : p.HolderConjugate q := .conjExponent hp1
  have hq : 0 < q := hpq.symm.pos
  set t : ℝ := (1 - d) * q with ht_def
  have ht : -d < t := by
    rw [ht_def, hq_def, mul_div_assoc', lt_div_iff₀ (by linarith)]
    nlinarith
  have hexp : (d + t) * (1 / q) = 1 - d / p := by
    have hp0 : p ≠ 0 := by linarith
    have hp1' : p - 1 ≠ 0 := by linarith
    rw [ht_def, hq_def]
    field_simp
    ring
  have he : 0 ≤ 1 - d / p := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact hp.le
  set K := ∫⁻ v in ball (0 : E) 1, ‖v‖ₑ ^ t ∂μ with hK_def
  have hK : K ≠ ⊤ := (lintegral_ball_enorm_rpow_lt_top μ ht).ne
  set C' : ℝ≥0∞ := 2 ^ (1 - d / p) * K ^ (1 / q) with hC'_def
  have hC' : C' ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg he ENNReal.ofNat_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hK)
  refine ⟨C'.toNNReal, fun a z r hr hz g hg => ?_⟩
  rw [ENNReal.coe_toNNReal hC']
  have hk : Measurable fun w : E => ‖w - z‖ₑ ^ (1 - d) :=
    ((measurable_id.sub_const z).enorm).pow_const _
  have hsub : ball a r ⊆ ball z (2 * r) := by
    refine ball_subset_ball' ?_
    rw [dist_comm]
    linarith [mem_ball.1 hz]
  have hker : ∫⁻ w in ball a r, (‖w - z‖ₑ ^ (1 - d)) ^ q ∂μ ≤
      ENNReal.ofReal (2 * r) ^ (d + t) * K := by
    simp_rw [← ENNReal.rpow_mul]
    calc ∫⁻ w in ball a r, ‖w - z‖ₑ ^ t ∂μ ≤ ∫⁻ w in ball z (2 * r), ‖w - z‖ₑ ^ t ∂μ :=
          lintegral_mono_set hsub
      _ = _ := lintegral_ball_enorm_sub_rpow μ z (by positivity) t
  calc ∫⁻ w in ball a r, ‖w - z‖ₑ ^ (1 - d) * g w ∂μ
      ≤ (∫⁻ w in ball a r, (‖w - z‖ₑ ^ (1 - d)) ^ q ∂μ) ^ (1 / q) *
          (∫⁻ w in ball a r, g w ^ p ∂μ) ^ (1 / p) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq.symm hk.aemeasurable hg.aemeasurable
    _ ≤ (ENNReal.ofReal (2 * r) ^ (d + t) * K) ^ (1 / q) *
          (∫⁻ w in ball a r, g w ^ p ∂μ) ^ (1 / p) :=
        by gcongr
    _ = C' * ENNReal.ofReal r ^ (1 - d / p) * (∫⁻ w in ball a r, g w ^ p ∂μ) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, hexp,
          ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ENNReal.mul_rpow_of_nonneg _ _ he,
          hC'_def]
        ring

end LatticeProb.PegdenSmart
