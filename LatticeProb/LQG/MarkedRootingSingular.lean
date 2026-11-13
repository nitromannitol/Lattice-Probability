import Mathlib
import LatticeProb.LQG.MarkedRootingBall
import LatticeProb.LQG.WeylOffOrigin
import LatticeProb.LQG.GMCDyadicLimit

/-!
# The marked rooting identity for the field with a logarithmic singularity

Let `h = h^ℂ - α₀ log |·|` be the whole-plane Gaussian free field with a logarithmic singularity at the origin
and `μ` its `γ`-Liouville measure (`IsLQGMeasureOfField P γ α₀ hcirc μ`).  Off the origin `μ` has the density
`|z|^{-γ α₀}` with respect to the Liouville measure of the field `h^ℂ` (Weyl relation), and the pairings of `h` against
a mean-zero test function `φ` are `(h^ℂ, φ) - α₀ ∫ φ log |·|`.  Combined with the marked rooting identity for `h^ℂ`
on a ball (`lintegral_lqgMeasure_marked_ball`) this gives, for a measurable `U` in the ball of radius `2^j` avoiding
the origin,
`E [∫_U f (z, Y) dμ (z)] = ∫_U |z|^{-γ α₀} max(1, |z|)^{γ²} E [f (z, Y + γ s(z))] dz`
with `Y_i = (h^ℂ, φ_i) - α₀ ∫ φ_i log |·|` and `s_i(z) = ∫ φ_i(x) Cov (h^ℂ(x), h^ℂ(z)) dx`.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Gauss

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Change of density off the origin.** If `lam s = ∫⁻_s |z|^β dμ` for measurable `s` avoiding `0`, then
`∫⁻_U F dμ = ∫⁻_U |z|^{-β} F dlam` for measurable `U` avoiding `0`. -/
theorem lintegral_restrict_eq_of_offOrigin {μ lam : Measure ℂ} {β : ℝ}
    (hlam : ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s →
      lam s = ∫⁻ z in s, ENNReal.ofReal (‖z‖ ^ β) ∂μ)
    {U : Set ℂ} (hU : MeasurableSet U) (hU0 : (0 : ℂ) ∉ U) {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in U, F z ∂μ = ∫⁻ z in U, ENNReal.ofReal (‖z‖ ^ (-β)) * F z ∂lam := by
  have hρ : Measurable fun z : ℂ => ENNReal.ofReal (‖z‖ ^ β) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const β)
  have hg : Measurable fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (-β)) * F z :=
    (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const (-β))).mul hF
  have hrestr : lam.restrict U = (μ.restrict U).withDensity fun z => ENNReal.ofReal (‖z‖ ^ β) := by
    ext s hs
    rw [Measure.restrict_apply hs, withDensity_apply _ hs, Measure.restrict_restrict hs]
    exact hlam (s ∩ U) (hs.inter hU) fun h => hU0 h.2
  rw [hrestr, lintegral_withDensity_eq_lintegral_mul _ hρ hg]
  refine setLIntegral_congr_fun hU fun z hz => ?_
  have hz0 : z ≠ 0 := fun h => hU0 (h ▸ hz)
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  show F z = ENNReal.ofReal (‖z‖ ^ β) * (ENNReal.ofReal (‖z‖ ^ (-β)) * F z)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _), ← Real.rpow_add hpos,
    add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]

/-- **Marked rooting identity for the field with a logarithmic singularity.** -/
theorem lintegral_lqgMeasureOfField_marked_ball (hh : IsWholePlaneGFF P hC hcirc) {γ α₀ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < LatticeProb.LQG.lqgQ γ) {μ : Ω → Measure ℂ}
    (hμ : LatticeProb.LQG.IsLQGMeasureOfField P γ α₀ hcirc μ) (j : ℕ) {m : ℕ} {φ : Fin m → ℂ → ℝ}
    (hφ : ∀ i, IsTestFunction Set.univ (φ i)) (hφ0 : ∀ i, ∫ x, φ i x = 0)
    (hφs : ∀ i y, φ i y ≠ 0 → ‖y‖ < (2 : ℝ) ^ j) {U : Set ℂ} (hU : MeasurableSet U)
    (hUc : U ⊆ Metric.ball (0 : ℂ) ((2 : ℝ) ^ j)) (hU0 : (0 : ℂ) ∉ U)
    {f : ℂ × (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    AEMeasurable (fun ω => ∫⁻ z in U,
      f (z, fun i => hC ω (φ i) - α₀ * ∫ x, φ i x * Real.log ‖x‖) ∂μ ω) P ∧
    ∫⁻ ω, ∫⁻ z in U, f (z, fun i => hC ω (φ i) - α₀ * ∫ x, φ i x * Real.log ‖x‖) ∂μ ω ∂P =
      ∫⁻ z in U, ENNReal.ofReal (Real.exp (-γ * α₀ * Real.log ‖z‖ +
          γ ^ 2 * Real.log (max ‖z‖ 1))) *
        ∫⁻ ω, f (z, fun i => hC ω (φ i) - α₀ * (∫ x, φ i x * Real.log ‖x‖) +
          γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
  have := hh.isProbabilityMeasure
  obtain ⟨lam, hlam⟩ := hh.exists_isLQGMeasure hγ0 hγ2
  have hlam0 : LatticeProb.LQG.IsLQGMeasureOfField P γ 0 hcirc lam := by
    simpa only [LatticeProb.LQG.IsLQGMeasureOfField,
      LatticeProb.LQG.LQGMeasureNonatomicMass.fieldCircleAverage_zero_lp] using hlam
  have hweyl := LatticeProb.LQG.WeylOffOriginDerived.localLQGInsertionWeylOffOrigin_lp
    Ω P γ α₀ hC hcirc μ lam hh hγ0 hγ2 hα hμ hlam0
  -- the marks and the modified integrand
  set a : Fin m → ℝ := fun i => ∫ x, φ i x * Real.log ‖x‖ with hadef
  set f' : ℂ × (Fin m → ℝ) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (‖q.1‖ ^ (-(γ * α₀))) * f (q.1, fun i => q.2 i - α₀ * a i) with hf'def
  have hf' : Measurable f' := by
    have h1 : Measurable fun q : ℂ × (Fin m → ℝ) => ENNReal.ofReal (‖q.1‖ ^ (-(γ * α₀))) :=
      ENNReal.measurable_ofReal.comp ((measurable_norm.comp measurable_fst).pow_const _)
    have h2 : Measurable fun q : ℂ × (Fin m → ℝ) => (q.1, fun i => q.2 i - α₀ * a i) :=
      measurable_fst.prodMk (measurable_pi_iff.2 fun i =>
        ((measurable_pi_apply i).comp measurable_snd).sub_const _)
    exact h1.mul (hf.comp h2)
  have hpath : ∀ᵐ ω ∂P, ∫⁻ z in U, f (z, fun i => hC ω (φ i) - α₀ * a i) ∂μ ω =
      ∫⁻ z in U, f' (z, fun i => hC ω (φ i)) ∂lam ω := by
    filter_upwards [hweyl] with ω hω
    have hmeasF : Measurable fun z : ℂ => f (z, fun i => hC ω (φ i) - α₀ * a i) :=
      hf.comp (measurable_id.prodMk measurable_const)
    have := lintegral_restrict_eq_of_offOrigin (β := γ * α₀) (fun s hs h0 => hω s hs h0) hU hU0 hmeasF
    rw [this]
  obtain ⟨hae, hid⟩ := hh.lintegral_lqgMeasure_marked_ball hγ0 hγ2 hlam j hφ hφ0 hφs hU hUc hf'
  refine ⟨hae.congr (hpath.mono fun ω h => h.symm), ?_⟩
  rw [lintegral_congr_ae hpath, hid]
  refine setLIntegral_congr_fun hU fun z hz => ?_
  have hz0 : z ≠ 0 := fun h => hU0 (h ▸ hz)
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hw : ENNReal.ofReal (Real.exp (-γ * α₀ * Real.log ‖z‖ + γ ^ 2 * Real.log (max ‖z‖ 1))) =
      ENNReal.ofReal (max 1 ‖z‖ ^ γ ^ 2) * ENNReal.ofReal (‖z‖ ^ (-(γ * α₀))) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_max_of_le_left zero_le_one) _),
      Real.exp_add, Real.rpow_def_of_pos hpos, max_comm ‖z‖ 1,
      Real.rpow_def_of_pos (lt_max_of_lt_left one_pos)]
    congr 1
    rw [mul_comm]
    congr 1 <;> congr 1 <;> ring
  rw [hw, mul_assoc]
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω => ?_
  simp only [hf'def, hadef]
  congr 3
  funext i
  ring

end IsWholePlaneGFF

end LatticeProb.Gauss
