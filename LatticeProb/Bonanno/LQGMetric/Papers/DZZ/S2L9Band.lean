/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L9Band at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L8Var
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L8
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Bridge

/-!
# DZZ Lemma 2.8 at non-dyadic scales: sub-band variance bound (task P2-DZZPRE3)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 628–641 (proof of Lemma 2.9):
(eq-coupling-hat-h-eta-2) needs Lemma 2.8 (`lem-hat-h-eta`, l. 594–609) along the scales `a 2^{-j}`
instead of `2^{-j}`. Writing `a 2^{-j}` between consecutive dyadic scales, the extra term is a
band `[a', b']` inside one dyadic band `[2^{-j-1}, 2^{-j}]`. Its variance obeys the same bound as
DZZ's (eq-variance-truncation) analogue for that band, by the same proof (the integrand
`p_s(x,x) − p_{𝕍 ∩ B(x, r(s))}(s; x, x)` is bounded pointwise on the dyadic band, and
`log(b'²/a'²) ≤ log 4`). This file adapts `variance_hat_sub_eta_band_le` (S2L8Var) verbatim.

* `pi_sq_norm_phi_sub_eta_subband_le`;
* `pi_sq_norm_subband_sub_le`: increments `≤ 2(√2 + 4·269)|x − x'|/a` (Lemma 2.5 for both parts,
  as `sq_norm_hatDeltaKernel_sub_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise

/-- **(eq-variance-truncation) for sub-bands**: for `B(x, ξ) ⊆ 𝕍` and
`2^{-j-1} ≤ a ≤ b ≤ 2^{-j}`, `π‖k^ĥ_{a,b,x} − K^η_{(a²,b²),x}‖² ≤ 2 e^{−(2/9) min(ξ², κ) j} log 4`. -/
theorem pi_sq_norm_phi_sub_eta_subband_le {ξ : ℝ} (hξ : 0 < ξ) {x : ℂ}
    (hB : Metric.ball x ξ ⊆ openSquare) (j : ℕ) {a b : ℝ} (ha1 : (1 / 2 : ℝ) ^ (j + 1) ≤ a)
    (hab : a ≤ b) (hb1 : b ≤ (1 / 2 : ℝ) ^ j) :
    Real.pi * ‖phiKernelL2 a b x - etaKernelL2 (Ioo (a ^ 2) (b ^ 2)) x‖ ^ 2 ≤
      2 * Real.exp (-(2 / 9 * min (ξ ^ 2) kappaBand * j)) * Real.log 4 := by
  have ha : 0 < a := lt_of_lt_of_le (by positivity) ha1
  have hA2 : ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 = (1 / 4 : ℝ) ^ (j + 1) := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hB2 : ((1 / 2 : ℝ) ^ j) ^ 2 = (1 / 4 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have ha2 : (1 / 4 : ℝ) ^ (j + 1) ≤ a ^ 2 := by
    rw [← hA2]; exact pow_le_pow_left₀ (by positivity) ha1 2
  have hb2 : b ^ 2 ≤ (1 / 4 : ℝ) ^ j := by
    rw [← hB2]; exact pow_le_pow_left₀ (ha.le.trans hab) hb1 2
  have hab2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have hc₀ : 0 < a ^ 2 := by positivity
  set m : ℝ := 2 / 9 * min (ξ ^ 2) kappaBand * j
  have hN := sq_norm_phi_sub_eta_le (b := b) ha x
  have hI0 : Ioo (a ^ 2) (b ^ 2) ⊆ Ioi (a ^ 2) := Ioo_subset_Ioi_self
  have hie := integrableOn_killedHeat_eta hc₀ hI0 x
  have hinv : IntegrableOn (fun s : ℝ => s⁻¹) (Ioo (a ^ 2) (b ^ 2)) :=
    ((continuousOn_inv₀.mono fun y hy => mem_compl_singleton_iff.mpr
      (ne_of_gt (hc₀.trans_le hy.1))).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hheat : IntegrableOn (fun s : ℝ => heatKernel s x x) (Ioo (a ^ 2) (b ^ 2)) := by
    have e : (fun s : ℝ => heatKernel s x x) = fun s => (2 * Real.pi)⁻¹ * s⁻¹ := by
      funext s
      rw [heatKernel, sub_self, norm_zero, show (0 : ℝ) ^ 2 = 0 by norm_num, neg_zero, zero_div,
        Real.exp_zero, mul_one, mul_inv]
    rw [e]; exact hinv.const_mul _
  rw [← integral_sub hheat hie] at hN
  have hpt : ∀ s ∈ Ioo (a ^ 2) (b ^ 2), Real.pi * (heatKernel s x x -
      killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x) ≤
      2 * Real.exp (-m) * s⁻¹ := by
    intro s hs
    have hs' : s ∈ Ioo ((1 / 4 : ℝ) ^ (j + 1)) ((1 / 4 : ℝ) ^ j) :=
      ⟨ha2.trans_lt hs.1, hs.2.trans_le hb2⟩
    obtain ⟨hr, hκ⟩ := etaRad_band j hs'
    have hs0 : 0 < s := hc₀.trans hs.1
    have h := heatKernel_sub_killedHeat_eta_le hξ hB hs0 hr
    have hs1 : s < 1 := hs.2.trans_le (hb2.trans (pow_le_one₀ (by norm_num) (by norm_num)))
    -- `min(ξ, r)²/s ≥ min(ξ², κ) j`
    have hmin : min (ξ ^ 2) kappaBand * j ≤ min ξ (etaRad s) ^ 2 / s := by
      have hj : (j : ℝ) ≤ s⁻¹ := by
        have h4 : (j : ℝ) ≤ 4 ^ j := by
          have h1 : (j : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
          have h2 : (2 : ℝ) ^ j ≤ 4 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
          linarith
        refine h4.trans ?_
        have : (4 : ℝ) ^ j = ((1 / 4 : ℝ) ^ j)⁻¹ := by rw [one_div, inv_pow, inv_inv]
        rw [this]; exact inv_anti₀ hs0 (hs.2.le.trans hb2)
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      rcases le_total ξ (etaRad s) with hle | hle
      · rw [min_eq_left hle]
        calc min (ξ ^ 2) kappaBand * j ≤ ξ ^ 2 * j := mul_le_mul_of_nonneg_right (min_le_left _ _) hj0
          _ ≤ ξ ^ 2 * s⁻¹ := mul_le_mul_of_nonneg_left hj (sq_nonneg ξ)
          _ = ξ ^ 2 / s := by rw [div_eq_mul_inv]
      · rw [min_eq_right hle]
        calc min (ξ ^ 2) kappaBand * j ≤ kappaBand * j :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hj0
          _ ≤ etaRad s ^ 2 / s := hκ
    have hm : m ≤ 2 * (min ξ (etaRad s) / 3) ^ 2 / s := by
      have e : 2 * (min ξ (etaRad s) / 3) ^ 2 / s = 2 / 9 * (min ξ (etaRad s) ^ 2 / s) := by ring
      rw [e]; simp only [m]; nlinarith
    have he : Real.exp (-(2 * (min ξ (etaRad s) / 3) ^ 2 / s)) ≤ Real.exp (-m) :=
      Real.exp_le_exp.mpr (neg_le_neg hm)
    have hpi := Real.pi_pos
    calc Real.pi * (heatKernel s x x -
          killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x)
        ≤ Real.pi * ((2 * Real.pi * s)⁻¹ * (4 * Real.exp (-m))) := by
          refine mul_le_mul_of_nonneg_left (h.trans ?_) hpi.le
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * Real.exp (-m) * s⁻¹ := by field_simp; ring
  have hlog : Real.log (b ^ 2 / a ^ 2) ≤ Real.log 4 := by
    refine Real.log_le_log (div_pos (pow_pos (ha.trans_le hab) 2) hc₀) ?_
    rw [div_le_iff₀ hc₀]
    have : (1 / 4 : ℝ) ^ j = 4 * (1 / 4 : ℝ) ^ (j + 1) := by rw [pow_succ]; ring
    nlinarith
  calc Real.pi * ‖phiKernelL2 a b x - etaKernelL2 (Ioo (a ^ 2) (b ^ 2)) x‖ ^ 2
      ≤ Real.pi * ∫ s in Ioo (a ^ 2) (b ^ 2), (heatKernel s x x -
          killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x) :=
        mul_le_mul_of_nonneg_left hN Real.pi_pos.le
    _ = ∫ s in Ioo (a ^ 2) (b ^ 2), Real.pi * (heatKernel s x x -
          killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ s in Ioo (a ^ 2) (b ^ 2), 2 * Real.exp (-m) * s⁻¹ :=
        setIntegral_mono_on ((hheat.sub hie).const_mul _) (hinv.const_mul _) measurableSet_Ioo hpt
    _ = 2 * Real.exp (-m) * Real.log (b ^ 2 / a ^ 2) := by
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hab2, integral_inv_of_pos hc₀ (hc₀.trans_le hab2)]
    _ ≤ 2 * Real.exp (-m) * Real.log 4 :=
        mul_le_mul_of_nonneg_left hlog (by positivity)



variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- Increments of the sub-band difference `ĥ_a^b − η_a^b` (Lemma 2.5 for `ĥ` and `η`, as in
`sq_norm_hatDeltaKernel_sub_le`): `π‖Δ(x) − Δ(x')‖² ≤ 2(√2 + 4(13 + 256))|x − x'|/a`. -/
theorem pi_sq_norm_subband_sub_le (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (x x' : ℂ) :
    Real.pi * ‖(phiKernelL2 a b x - etaKernelL2 (Ioo (a ^ 2) (b ^ 2)) x) -
        (phiKernelL2 a b x' - etaKernelL2 (Ioo (a ^ 2) (b ^ 2)) x')‖ ^ 2 ≤
      2 * (Real.sqrt 2 + 4 * (13 + 256)) * ‖x - x'‖ / a := by
  have h2 := dzz_lemma25_etaField (by norm_num) bridgeShellBound_256 hW ha measurableSet_Ioo
    (Ioo_subset_Ioi_self : Ioo (a ^ 2) (b ^ 2) ⊆ Ioi (a ^ 2)) x x'
  simp only [etaField] at h2
  rw [variance_sqrtPi_sub hW] at h2
  have h1 := variance_phi_band_sub_le hW (b := b) ha x x'
  rw [show (fun ω => phi W a b x ω - phi W a b x' ω) = fun ω =>
      Real.sqrt Real.pi * W (phiKernelL2 a b x) ω - Real.sqrt Real.pi * W (phiKernelL2 a b x') ω
      from rfl, variance_sqrtPi_sub hW] at h1
  have h3 := sq_norm_sub_sub_le (phiKernelL2 a b x) (etaKernelL2 (Ioo (a ^ 2) (b ^ 2)) x)
    (phiKernelL2 a b x') (etaKernelL2 (Ioo (a ^ 2) (b ^ 2)) x')
  have hpi := Real.pi_pos
  have e : 2 * (Real.sqrt 2 + 4 * (13 + 256)) * ‖x - x'‖ / a =
      2 * (Real.sqrt 2 * ‖x - x'‖ / a) + 2 * (4 * (13 + 256) * ‖x - x'‖ / a) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h3 hpi.le]

end DZZ
end LQGMetric
