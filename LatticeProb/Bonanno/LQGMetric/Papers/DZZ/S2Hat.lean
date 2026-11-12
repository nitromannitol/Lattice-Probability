/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2Hat at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw

/-!
# DZZ §2.2: the stationary white-noise field `ĥ` (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang, *Heat kernel for Liouville Brownian motion and Liouville graph distance*
(arXiv:1807.00422, `LBM_LGDarXiv.tex`), define (l. 600–604, eq. `eq:WND_decomposition-stationary`)
`ĥ_δ^{δ̃}(v) = √π ∫_{ℝ² × (δ², δ̃²)} p(s/2; v, w) W(dw, ds)`, which is the field
`WhiteNoise.phi W δ δ̃ v` of the white-noise layer (decision D35).

* `dzz_variance_hat_sub_le` — DZZ (`eq-hat-h-continuity`, l. 608–613):
  `Var(ĥ_δ^{δ̃}(v) − ĥ_δ^{δ̃}(w)) ≤ |v − w|² / δ²` (DZZ's own computation:
  `1 − e^{−x} ≤ x` and `∫_{δ²}^∞ s^{-2} ds = δ^{-2}`).
* `cov_phi_nested` — covariance of two bands with a common top `b`:
  `E ĥ_α^b(x) ĥ_{α'}^b(x') = ∫_{max(α,α')²}^{b²} (2t)⁻¹ e^{−|x−x'|²/(2t)} dt` (the kernels add
  up and bands over disjoint time intervals are orthogonal, as in DZZ l. 452–458).
* `map_phi_family_eq_of_cov` — two families of white-noise fields over arbitrary bands with the
  same covariances have the same law (centered Gaussian processes).
* `dzz_hat_scaling_law` — DZZ (l. 635–637, proof of Lemma 2.9 `lem-scaling-coupling`):
  "by the translation invariance and scaling invariance of the `ĥ`-process",
  `{ĥ_{2^{-j}}^1(v)}_{v, j ≥ 0} =ᵈ {ĥ_{a2^{-j}}^a(a v + b)}_{v, j ≥ 0}` for `a ∈ (0,1]`, `b ∈ ℂ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `∫_{a}^{b} t⁻² dt = a⁻¹ − b⁻¹` for `0 < a ≤ b`. -/
lemma integral_Icc_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in Icc a b, (t ^ 2)⁻¹ = a⁻¹ - b⁻¹ := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hpos : ∀ t ∈ uIcc a b, 0 < t := fun t ht => by
    rw [uIcc_of_le hab] at ht; exact ha.trans_le ht.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -t⁻¹)
    (fun t ht => by simpa using (hasDerivAt_inv (hpos t ht).ne').fun_neg)]
  · ring
  · refine ContinuousOn.intervalIntegrable fun t ht => ?_
    have := (hpos t ht).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))

/-- **DZZ (`eq-hat-h-continuity`, l. 608–613)**: for `0 < δ ≤ δ̃`,
`Var(ĥ_δ^{δ̃}(v) − ĥ_δ^{δ̃}(w)) ≤ |v − w|² / δ²`. -/
theorem dzz_variance_hat_sub_le (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (x x' : ℂ) :
    Var[fun ω => phi W a b x ω - phi W a b x' ω; P] ≤ ‖x - x'‖ ^ 2 / a ^ 2 := by
  rw [(hasLaw_phi_sub hW ha b x x').variance_eq, variance_id_gaussianReal, Real.coe_toNNReal']
  refine max_le ?_ (by positivity)
  set r := ‖x - x'‖
  have ha2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have ha2p : 0 < a ^ 2 := by positivity
  have hpos : ∀ t ∈ Icc (a ^ 2) (b ^ 2), 0 < t := fun t ht => ha2p.trans_le ht.1
  have hc1 : ContinuousOn (fun t : ℝ => t⁻¹ * (1 - Real.exp (-r ^ 2 / (2 * t))))
      (Icc (a ^ 2) (b ^ 2)) := fun t ht => by
    have := (hpos t ht).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have hc2 : ContinuousOn (fun t : ℝ => r ^ 2 / 2 * (t ^ 2)⁻¹) (Icc (a ^ 2) (b ^ 2)) :=
    fun t ht => by
      have := (hpos t ht).ne'
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  calc ∫ t in Icc (a ^ 2) (b ^ 2), t⁻¹ * (1 - Real.exp (-r ^ 2 / (2 * t)))
      ≤ ∫ t in Icc (a ^ 2) (b ^ 2), r ^ 2 / 2 * (t ^ 2)⁻¹ := by
        refine setIntegral_mono_on (hc1.integrableOn_compact isCompact_Icc)
          (hc2.integrableOn_compact isCompact_Icc) measurableSet_Icc fun t ht => ?_
        have ht := hpos t ht
        have h1 : 1 - Real.exp (-r ^ 2 / (2 * t)) ≤ r ^ 2 / (2 * t) := by
          have := Real.add_one_le_exp (-r ^ 2 / (2 * t))
          rw [neg_div] at this ⊢
          linarith
        calc t⁻¹ * (1 - Real.exp (-r ^ 2 / (2 * t))) ≤ t⁻¹ * (r ^ 2 / (2 * t)) :=
              mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ht.le)
          _ = r ^ 2 / 2 * (t ^ 2)⁻¹ := by field_simp
    _ = r ^ 2 / 2 * ((a ^ 2)⁻¹ - (b ^ 2)⁻¹) := by
        rw [integral_const_mul, integral_Icc_inv_sq ha2p ha2]
    _ ≤ r ^ 2 / a ^ 2 := by
        have hb : 0 ≤ (b ^ 2)⁻¹ := by positivity
        have : r ^ 2 / 2 * ((a ^ 2)⁻¹ - (b ^ 2)⁻¹) ≤ r ^ 2 / 2 * (a ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        refine this.trans ?_
        rw [div_eq_mul_inv (r ^ 2) (a ^ 2)]
        have : 0 ≤ r ^ 2 * (a ^ 2)⁻¹ := by positivity
        nlinarith

end DZZ
end LQGMetric
