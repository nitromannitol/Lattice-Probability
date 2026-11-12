/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L8Var
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7

/-!
# DZZ Lemma 2.8: `ĥ` versus `η` on `𝕍^ξ`, the sum over scales (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`), Lemma 2.8 (`lem-hat-h-eta`),
l. 594–609: `Δ_i = ĥ_{2^{-i}}^{2^{-i+1}} − η_{2^{-i}}^{2^{-i+1}}` (`i ≥ 1`), `Δ_0 = η_1` (we use
`−η_1`, the sign is immaterial), `Var Δ_i ≤ O(1) e^{−Ω(i²)}` and `Var(Δ_i(v) − Δ_i(u)) ≤ O(1) 2^i|u − v|`
on `𝕍^ξ`, "then conclude as in Lemma 2.7". Here `ĥ_a^b = phi W a b` (DEC-WN).

* `variance_phi_band_sub_le`: `Var(ĥ_a^b(x) − ĥ_a^b(x')) ≤ √2|x − x'|/a` (as DDDF L4 /
  `variance_phi_sub_le`, any `b`);
* `hatDeltaKernel`, `sq_norm_hatDeltaKernel_le` (`π‖Δ_i‖² ≤ Kρ^i` when `B(x, ξ) ⊆ 𝕍`),
  `sq_norm_hatDeltaKernel_sub_le` (increments; uses `BridgeShellBound` for the `η` part);
* `dzz_lemma28_sum`: `P(∃ v ∈ 𝕍^ξ, ∃ n, λ ≤ Σ_{i<n}|Y_i(v)|) ≤ C e^{−λ²/C}` for continuous versions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail

lemma integrand_phi_sub_le {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) :
    t⁻¹ * (1 - Real.exp (-r ^ 2 / (2 * t))) ≤ r / Real.sqrt 2 * t ^ (-(3 / 2 : ℝ)) := by
  have hz : 0 ≤ r ^ 2 / (2 * t) := by positivity
  have h1 := one_sub_exp_neg_le_sqrt hz
  rw [neg_div]
  have hsq : Real.sqrt (r ^ 2 / (2 * t)) = r / Real.sqrt 2 * (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr, Real.sqrt_mul (by norm_num)]
    field_simp
  have hpow : t ^ (-(3 / 2 : ℝ)) = t⁻¹ * (Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg ht.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht,
      Real.rpow_one, ← Real.sqrt_eq_rpow, mul_inv]
  calc t⁻¹ * (1 - Real.exp (-(r ^ 2 / (2 * t))))
      ≤ t⁻¹ * Real.sqrt (r ^ 2 / (2 * t)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr ht.le)
    _ = r / Real.sqrt 2 * t ^ (-(3 / 2 : ℝ)) := by rw [hsq, hpow]; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `Var(ĥ_a^b(x) − ĥ_a^b(x')) ≤ √2 |x − x'|/a` (DZZ eq-hat-h-continuity in the `|u − v|/δ`
form; own variant of `variance_phi_sub_le` for all `b`). -/
theorem variance_phi_band_sub_le (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (x x' : ℂ) :
    Var[fun ω => phi W a b x ω - phi W a b x' ω; P] ≤ Real.sqrt 2 * ‖x - x'‖ / a := by
  rw [(hasLaw_phi_sub hW ha b x x').variance_eq, variance_id_gaussianReal, Real.coe_toNNReal']
  refine max_le ?_ (by positivity)
  set r := ‖x - x'‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have ha2 : 0 < a ^ 2 := by positivity
  have hpow : IntegrableOn (fun t : ℝ => r / Real.sqrt 2 * t ^ (-(3 / 2 : ℝ))) (Ioi (a ^ 2)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ha2).const_mul _
  rw [integral_Icc_eq_integral_Ioc]
  have hsub : Ioc (a ^ 2) (b ^ 2) ⊆ Ioi (a ^ 2) := Ioc_subset_Ioi_self
  calc ∫ t in Ioc (a ^ 2) (b ^ 2), t⁻¹ * (1 - Real.exp (-r ^ 2 / (2 * t)))
      ≤ ∫ t in Ioc (a ^ 2) (b ^ 2), r / Real.sqrt 2 * t ^ (-(3 / 2 : ℝ)) := by
        refine setIntegral_mono_on ?_ (hpow.mono_set hsub) measurableSet_Ioc
          fun t ht => integrand_phi_sub_le hr0 (ha2.trans ht.1)
        refine Integrable.mono' (hpow.mono_set hsub) ?_ ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall fun t ht => ?_))
        · exact (Measurable.mul measurable_inv (measurable_const.sub
            (Real.measurable_exp.comp (measurable_const.div
              (measurable_const.mul measurable_id))))).aestronglyMeasurable
        · have ht0 : 0 < t := ha2.trans ht.1
          have h0 : 0 ≤ t⁻¹ * (1 - Real.exp (-r ^ 2 / (2 * t))) := by
            refine mul_nonneg (inv_nonneg.mpr ht0.le) (sub_nonneg.mpr (Real.exp_le_one_iff.mpr ?_))
            have : 0 ≤ r ^ 2 / (2 * t) := by positivity
            rw [neg_div]; linarith
          rw [Real.norm_eq_abs, abs_of_nonneg h0]
          exact integrand_phi_sub_le hr0 ht0
    _ ≤ ∫ t in Ioi (a ^ 2), r / Real.sqrt 2 * t ^ (-(3 / 2 : ℝ)) := by
        refine setIntegral_mono_set hpow ((ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall fun t ht => ?_)) (Eventually.of_forall hsub)
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (ha2.trans ht).le _)
    _ = Real.sqrt 2 * r / a := by
        rw [integral_const_mul, integral_Ioi_rpow_three_halves ha]
        have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        have hs2p : 0 < Real.sqrt 2 := by positivity
        field_simp
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]


/-- DZZ's `Δ_i` of Lemma 2.8 as a kernel: `Δ_i(x) = √π W(hatDeltaKernel i x)`. -/
def hatDeltaKernel (i : ℕ) (x : ℂ) : WNSpace :=
  if i = 0 then -etaKernelL2 (bandSet 0) x
  else phiKernelL2 ((1 / 2 : ℝ) ^ i) ((1 / 2 : ℝ) ^ (i - 1)) x - etaKernelL2 (bandSet i) x

/-- `ρ_ξ = e^{−(2/9) min(ξ², κ)}`. -/
def rhoXi (ξ : ℝ) : ℝ := Real.exp (-(2 / 9 * min (ξ ^ 2) kappaBand))

lemma rhoXi_pos (ξ : ℝ) : 0 < rhoXi ξ := Real.exp_pos _

lemma rhoXi_lt_one {ξ : ℝ} (hξ : 0 < ξ) : rhoXi ξ < 1 := by
  have : 0 < min (ξ ^ 2) kappaBand := lt_min (by positivity) kappaBand_pos
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-- **(eq-variance-truncation) for Lemma 2.8**: if `B(x, ξ) ⊆ 𝕍` then
`π‖Δ_i(x)‖² ≤ K_ξ ρ_ξ^i`, `K_ξ = max 4 (2 log 4/ρ_ξ)`. -/
theorem sq_norm_hatDeltaKernel_le (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) {x : ℂ}
    (hB : Metric.ball x ξ ⊆ openSquare) (i : ℕ) :
    Real.pi * ‖hatDeltaKernel i x‖ ^ 2 ≤ max 4 (2 * Real.log 4 / rhoXi ξ) * rhoXi ξ ^ i := by
  have hρ := rhoXi_pos ξ
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rcases i with _ | j
  · simp only [hatDeltaKernel, if_true, norm_neg, pow_zero, mul_one]
    refine le_trans ?_ (le_max_left _ _)
    have hI0 : bandSet 0 ⊆ Ioi (1 : ℝ) := by simp [bandSet]
    have hI0' : bandSet 0 ⊆ Ioi 0 := hI0.trans (Ioi_subset_Ioi zero_le_one)
    have nu : ∫ p, etaKernel (bandSet 0) x p * etaKernel (bandSet 0) x p =
        ∫ s in bandSet 0, killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x := by
      simpa [sq] using integral_sq_eq_of_lintegral (measurable_etaKernel (measurableSet_bandSet 0) x)
        (etaKernel_nonneg _ _) (measurable_killedHeat_eta_time x)
        (fun s => killedHeat_nonneg _ _ _ _) (lintegral_etaKernel_sq (measurableSet_bandSet 0) hI0' x)
    rw [← real_inner_self_eq_norm_sq, inner_etaKernelL2 (measurableSet_bandSet 0) one_pos hI0, nu]
    have hiu := integrableOn_killedHeat_of_subset LQGMetric.isOpen_openSquare
      (by norm_num : (0 : ℝ) ≤ 2) openSquare_subset_ball one_pos subset_rfl x x
    have hpow : IntegrableOn (fun s : ℝ => 2 ^ 2 / Real.pi * s ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    have h1 : ∫ s in bandSet 0, killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x
        ≤ 4 / Real.pi := by
      have e0 : bandSet 0 = Ioi (1 : ℝ) := by simp [bandSet]
      rw [e0]
      calc ∫ s in Ioi (1 : ℝ), killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x
          ≤ ∫ s in Ioi (1 : ℝ), 2 ^ 2 / Real.pi * s ^ (-2 : ℝ) :=
            setIntegral_mono_on (integrableOn_killedHeat_eta one_pos subset_rfl x) hpow
              measurableSet_Ioi fun s hs => (killedHeat_mono inter_subset_left _ _ _).trans
                (killedHeat_le_rpow (by norm_num) openSquare_subset_ball (one_pos.trans hs) x x)
        _ = 4 / Real.pi := by
            rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]; norm_num
    have := Real.pi_pos
    calc Real.pi * ∫ s in bandSet 0,
          killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x
        ≤ Real.pi * (4 / Real.pi) := mul_le_mul_of_nonneg_left h1 this.le
      _ = 4 := by field_simp
  · have h := variance_hat_sub_eta_band_le hW hξ hB j
    rw [show (fun ω => phi W ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x ω -
        etaField W (Ioo (((1 / 2 : ℝ) ^ (j + 1)) ^ 2) (((1 / 2 : ℝ) ^ j) ^ 2)) x ω) =
        fun ω => Real.sqrt Real.pi * W (phiKernelL2 ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x) ω
          - Real.sqrt Real.pi * W (etaKernelL2 (Ioo (((1 / 2 : ℝ) ^ (j + 1)) ^ 2)
            (((1 / 2 : ℝ) ^ j) ^ 2)) x) ω from rfl, variance_sqrtPi_sub hW] at h
    have hk : hatDeltaKernel (j + 1) x = phiKernelL2 ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x -
        etaKernelL2 (Ioo (((1 / 2 : ℝ) ^ (j + 1)) ^ 2) (((1 / 2 : ℝ) ^ j) ^ 2)) x := by
      simp [hatDeltaKernel, bandSet]
    rw [hk]
    refine h.trans ?_
    have e : Real.exp (-(2 / 9 * min (ξ ^ 2) kappaBand * j)) = rhoXi ξ ^ j := by
      rw [rhoXi, ← Real.exp_nat_mul]; ring_nf
    rw [e]
    calc 2 * rhoXi ξ ^ j * Real.log 4 = 2 * Real.log 4 / rhoXi ξ * rhoXi ξ ^ (j + 1) := by
          field_simp; ring
      _ ≤ max 4 (2 * Real.log 4 / rhoXi ξ) * rhoXi ξ ^ (j + 1) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Increments of `Δ_i` (Lemma 2.8's eq-feb25 analogue), assuming `BridgeShellBound`:
`π‖Δ_i(x) − Δ_i(x')‖² ≤ 2(√2 + 4(13 + C)) 2^i |x − x'|`. -/
theorem sq_norm_hatDeltaKernel_sub_le {C : ℝ} (hC0 : 0 ≤ C) (hC : BridgeShellBound C)
    (hW : IsWhiteNoise P W) (i : ℕ) (x x' : ℂ) :
    Real.pi * ‖hatDeltaKernel i x - hatDeltaKernel i x'‖ ^ 2 ≤
      2 * (Real.sqrt 2 + 4 * (13 + C)) * 2 ^ i * ‖x - x'‖ := by
  have hδ : (0 : ℝ) < (1 / 2) ^ i := by positivity
  have hδinv : ((1 / 2 : ℝ) ^ i)⁻¹ = 2 ^ i := by rw [one_div, inv_pow, inv_inv]
  have h2 := dzz_lemma25_etaField hC0 hC hW hδ (measurableSet_bandSet i) (bandSet_subset i) x x'
  simp only [etaField] at h2
  rw [variance_sqrtPi_sub hW, div_eq_mul_inv, hδinv] at h2
  have hpi := Real.pi_pos
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hD : 0 ≤ ‖x - x'‖ := norm_nonneg _
  rcases i with _ | j
  · simp only [hatDeltaKernel, if_true, neg_sub_neg, norm_sub_rev (etaKernelL2 _ x')]
    simp only [pow_zero, mul_one] at h2 ⊢
    nlinarith
  · have h1 := variance_phi_band_sub_le hW (b := (1 / 2 : ℝ) ^ j) hδ x x'
    rw [show (fun ω => phi W ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x ω -
        phi W ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x' ω) = fun ω =>
        Real.sqrt Real.pi * W (phiKernelL2 ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x) ω -
        Real.sqrt Real.pi * W (phiKernelL2 ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x') ω
        from rfl, variance_sqrtPi_sub hW] at h1
    have hdiv : Real.sqrt 2 * ‖x - x'‖ / (1 / 2 : ℝ) ^ (j + 1) =
        Real.sqrt 2 * ‖x - x'‖ * 2 ^ (j + 1) := by rw [div_eq_mul_inv _ ((1 / 2 : ℝ) ^ (j + 1)), hδinv]
    rw [hdiv] at h1
    have hk : ∀ y, hatDeltaKernel (j + 1) y =
        phiKernelL2 ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) y - etaKernelL2 (bandSet (j + 1)) y :=
      fun y => by simp [hatDeltaKernel]
    rw [hk, hk]
    have h3 := sq_norm_sub_sub_le (phiKernelL2 ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x)
      (etaKernelL2 (bandSet (j + 1)) x) (phiKernelL2 ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x')
      (etaKernelL2 (bandSet (j + 1)) x')
    have h2pos : (0 : ℝ) ≤ 2 ^ (j + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hpi.le]

end DZZ
end LQGMetric
