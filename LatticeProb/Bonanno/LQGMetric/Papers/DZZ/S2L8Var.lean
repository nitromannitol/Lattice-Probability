/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L8Var at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6EtaVar
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePhi
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Var

/-!
# DZZ Lemma 2.8, first step: `ĥ`-band versus `η`-band (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Lemma 2.8 (`lem-hat-h-eta`,
l. 603–609): `Δ_i = ĥ_{2^{-i}}^{2^{-i+1}} − η_{2^{-i}}^{2^{-i+1}}`, "similarly to (eq-feb25)",
`Var Δ_i(v) ≤ O(1) e^{−Ω(i²)}` on `𝕍^ξ`. Here, for `ĥ_a^b = phi W a b` (DEC-WN) and the `η` band
on the same time interval:

* `integral_le_inner_phi_eta`: `⟪k^ĥ_x, K^η_x⟫ ≥ ∫_{(a²,b²)} p_{𝕍∩B(x,r(s))}(s; x, x) ds`
  (`p_t ≥ p_D ≥ 0` and Chapman–Kolmogorov for `D`);
* `sq_norm_phi_sub_eta_le`: `‖k^ĥ_x − K^η_x‖² ≤ ∫_{(a²,b²)} (p_s(x,x) − p_{𝕍∩B(x,r(s))}(s; x, x)) ds`;
* `heatKernel_sub_killedHeat_eta_le`: for `B(x, ξ) ⊆ 𝕍`,
  `p_s(x,x) − p_{𝕍∩B(x,r(s))}(s;x,x) ≤ (2πs)⁻¹ 4 e^{−2(min(ξ, r(s))/3)²/s}` (bridge exit,
  reflection principle).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise

/-- The cross term of `ĥ` and `η` on the band `(a², b²)`. -/
theorem integral_le_inner_phi_eta {a b : ℝ} (ha : 0 < a) (x : ℂ) :
    ∫ s in Ioo (a ^ 2) (b ^ 2),
        killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x ≤
      ⟪phiKernelL2 a b x, etaKernelL2 (Ioo (a ^ 2) (b ^ 2)) x⟫ := by
  have hc₀ : 0 < a ^ 2 := by positivity
  have hI0 : Ioo (a ^ 2) (b ^ 2) ⊆ Ioi (a ^ 2) := Ioo_subset_Ioi_self
  have hφ := memLp_phiKernel a b ha x
  have hη := memLp_etaKernel measurableSet_Ioo hc₀ hI0 x
  have hinner : ⟪phiKernelL2 a b x, etaKernelL2 (Ioo (a ^ 2) (b ^ 2)) x⟫ =
      ∫ p, phiKernel a b x p * etaKernel (Ioo (a ^ 2) (b ^ 2)) x p := by
    rw [etaKernelL2, dite_eq_left_of_eq_true (eq_true hη), L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_phiKernelL2 a b ha x, hη.coeFn_toLp] with p h1 h2
    rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply]
    simp [mul_comm]
  rw [hinner]
  have hint : Integrable (fun p => phiKernel a b x p * etaKernel (Ioo (a ^ 2) (b ^ 2)) x p) :=
    hφ.integrable_mul hη
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, integral_prod _ hint,
    ← integral_indicator measurableSet_Ioo]
  refine integral_mono ((integrableOn_killedHeat_eta hc₀ hI0 x).integrable_indicator
    measurableSet_Ioo) hint.integral_prod_left fun s => ?_
  by_cases hs : s ∈ Ioo (a ^ 2) (b ^ 2)
  · rw [indicator_of_mem hs]
    have hs0 : (0 : ℝ) < s := hc₀.trans hs.1
    set r := etaRad s
    set t := (s / 2).toNNReal
    have ht : t ≠ 0 := by simp only [t, ne_eq, Real.toNNReal_eq_zero, not_le]; linarith
    have htc : ((t : ℝ≥0) : ℝ) = s / 2 := Real.coe_toNNReal _ (by linarith)
    have hsum : t + t = s.toNNReal := by
      simp only [t]; rw [← Real.toNNReal_add (by linarith) (by linarith)]; ring_nf
    have hD : IsOpen (openSquare ∩ Metric.ball x r) :=
      LQGMetric.isOpen_openSquare.inter Metric.isOpen_ball
    have hH := integrable_heatKernel_mul_heatKernel (s / 2) (by linarith) x x
    have e : ∀ w, phiKernel a b x (s, w) * etaKernel (Ioo (a ^ 2) (b ^ 2)) x (s, w) =
        heatKernel (s / 2) x w * killedHeat (openSquare ∩ Metric.ball x r) t x w := by
      intro w
      simp only [phiKernel, etaKernel]
      rw [indicator_of_mem (mk_mem_prod (Ioo_subset_Icc_self hs) (mem_univ w)),
        indicator_of_mem hs]
    simp_rw [e]
    rw [← hsum, ← integral_killedHeat_mul_killedHeat hD ht x x]
    have hpk : ∀ w, killedHeat (openSquare ∩ Metric.ball x r) t x w ≤ heatKernel (s / 2) x w :=
      fun w => htc ▸ killedHeat_le_heatKernel _ _ _ _
    have hp0 : ∀ w, 0 ≤ killedHeat (openSquare ∩ Metric.ball x r) t x w :=
      fun w => killedHeat_nonneg _ _ _ _
    have hh0 : ∀ w, 0 ≤ heatKernel (s / 2) x w := fun w => by
      have := heatKernel_nonneg' t x w; rwa [htc] at this
    have hm := measurable_killedHeat_right hD ht x
    have hmh := measurable_heatKernel_right (s / 2) x
    refine integral_mono (Integrable.mono' hH (hm.mul hm).aestronglyMeasurable
      (ae_of_all _ fun w => ?_)) (Integrable.mono' hH (hmh.mul hm).aestronglyMeasurable
      (ae_of_all _ fun w => ?_)) fun w => mul_le_mul_of_nonneg_right (hpk w) (hp0 w)
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp0 w) (hp0 w))]
      exact mul_le_mul (hpk w) (hpk w) (hp0 w) (hh0 w)
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hh0 w) (hp0 w))]
      exact mul_le_mul_of_nonneg_left (hpk w) (hh0 w)
  · simp [hs, etaKernel]

/-- `‖k^ĥ_x − K^η_x‖² ≤ ∫_{(a²,b²)} (p_s(x,x) − p_{𝕍∩B(x,r(s))}(s; x, x)) ds`. -/
theorem sq_norm_phi_sub_eta_le {a b : ℝ} (ha : 0 < a) (x : ℂ) :
    ‖phiKernelL2 a b x - etaKernelL2 (Ioo (a ^ 2) (b ^ 2)) x‖ ^ 2 ≤
      (∫ s in Ioo (a ^ 2) (b ^ 2), heatKernel s x x) -
        ∫ s in Ioo (a ^ 2) (b ^ 2),
          killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x := by
  have hc₀ : 0 < a ^ 2 := by positivity
  have hI0 : Ioo (a ^ 2) (b ^ 2) ⊆ Ioi (a ^ 2) := Ioo_subset_Ioi_self
  have hI0' : Ioo (a ^ 2) (b ^ 2) ⊆ Ioi 0 := hI0.trans (Ioi_subset_Ioi hc₀.le)
  have hc := integral_le_inner_phi_eta (b := b) ha x
  have nu : ∫ p, etaKernel (Ioo (a ^ 2) (b ^ 2)) x p * etaKernel (Ioo (a ^ 2) (b ^ 2)) x p =
      ∫ s in Ioo (a ^ 2) (b ^ 2),
        killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x := by
    simpa [sq] using integral_sq_eq_of_lintegral (measurable_etaKernel measurableSet_Ioo x)
      (etaKernel_nonneg _ _) (measurable_killedHeat_eta_time x)
      (fun s => killedHeat_nonneg _ _ _ _) (lintegral_etaKernel_sq measurableSet_Ioo hI0' x)
  rw [@norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_phiKernelL2 a b ha x x, integral_Icc_eq_integral_Ioo,
    inner_etaKernelL2 measurableSet_Ioo hc₀ hI0 x x, nu]
  linarith

/-- For `B(x, ξ) ⊆ 𝕍`: `p_s(x,x) − p_{𝕍∩B(x,r(s))}(s; x, x) ≤ (2πs)⁻¹ 4 e^{−2(min(ξ, r(s))/3)²/s}`. -/
theorem heatKernel_sub_killedHeat_eta_le {x : ℂ} {ξ : ℝ} (hξ : 0 < ξ)
    (hB : Metric.ball x ξ ⊆ openSquare) {s : ℝ} (hs : 0 < s) (hr : 0 < etaRad s) :
    heatKernel s x x - killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x ≤
      (2 * Real.pi * s)⁻¹ * (4 * Real.exp (-(2 * (min ξ (etaRad s) / 3) ^ 2 / s))) := by
  have htn : s.toNNReal ≠ 0 := by simpa using hs
  have hc : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.le
  have hρ : 0 < min ξ (etaRad s) := lt_min hξ hr
  have h := killedHeat_sub_inter_ball_le htn univ x hρ
  rw [killedHeat_univ, hc] at h
  have hsub : univ ∩ Metric.ball x (min ξ (etaRad s)) ⊆
      openSquare ∩ Metric.ball x (etaRad s) := by
    rintro y ⟨-, hy⟩
    exact ⟨hB (Metric.ball_subset_ball (min_le_left _ _) hy),
      Metric.ball_subset_ball (min_le_right _ _) hy⟩
  have hm := killedHeat_mono hsub s.toNNReal x x
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ L2.8 analogue of (eq-variance-truncation)** (l. 604–607), band `i = j + 1`: for
`B(x, ξ) ⊆ 𝕍`, `Var(ĥ_{2^{-j-1}}^{2^{-j}}(x) − η_{2^{-j-1}}^{2^{-j}}(x)) ≤
2 e^{−(2/9) min(ξ², κ) j} log 4`. -/
theorem variance_hat_sub_eta_band_le (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) {x : ℂ}
    (hB : Metric.ball x ξ ⊆ openSquare) (j : ℕ) :
    Var[fun ω => phi W ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x ω -
        etaField W (Ioo (((1 / 2 : ℝ) ^ (j + 1)) ^ 2) (((1 / 2 : ℝ) ^ j) ^ 2)) x ω; P] ≤
      2 * Real.exp (-(2 / 9 * min (ξ ^ 2) kappaBand * j)) * Real.log 4 := by
  set a : ℝ := (1 / 2 : ℝ) ^ (j + 1)
  set b : ℝ := (1 / 2 : ℝ) ^ j
  have ha : 0 < a := by positivity
  have ha2 : a ^ 2 = (1 / 4 : ℝ) ^ (j + 1) := by
    simp only [a]; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hb2 : b ^ 2 = (1 / 4 : ℝ) ^ j := by
    simp only [b]; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hab2 : a ^ 2 ≤ b ^ 2 := by
    rw [ha2, hb2]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ j)
  have hc₀ : 0 < a ^ 2 := by positivity
  set m : ℝ := 2 / 9 * min (ξ ^ 2) kappaBand * j
  -- the variance as a squared norm
  have hV : Var[fun ω => phi W a b x ω - etaField W (Ioo (a ^ 2) (b ^ 2)) x ω; P] =
      Real.pi * ‖phiKernelL2 a b x - etaKernelL2 (Ioo (a ^ 2) (b ^ 2)) x‖ ^ 2 :=
    variance_sqrtPi_sub hW _ _
  rw [hV]
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
    have hs' : s ∈ Ioo ((1 / 4 : ℝ) ^ (j + 1)) ((1 / 4 : ℝ) ^ j) := by rwa [← ha2, ← hb2]
    obtain ⟨hr, hκ⟩ := etaRad_band j hs'
    have hs0 : 0 < s := hc₀.trans hs.1
    have h := heatKernel_sub_killedHeat_eta_le hξ hB hs0 hr
    have hs1 : s < 1 := hs.2.trans_le (by rw [hb2]; exact pow_le_one₀ (by norm_num) (by norm_num))
    -- `min(ξ, r)²/s ≥ min(ξ², κ) j`
    have hmin : min (ξ ^ 2) kappaBand * j ≤ min ξ (etaRad s) ^ 2 / s := by
      have hj : (j : ℝ) ≤ s⁻¹ := by
        have h4 : (j : ℝ) ≤ 4 ^ j := by
          have h1 : (j : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
          have h2 : (2 : ℝ) ^ j ≤ 4 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
          linarith
        refine h4.trans ?_
        have : (4 : ℝ) ^ j = ((1 / 4 : ℝ) ^ j)⁻¹ := by rw [one_div, inv_pow, inv_inv]
        rw [this, ← hb2]; exact inv_anti₀ hs0 hs.2.le
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
  have hlog : Real.log (b ^ 2 / a ^ 2) = Real.log 4 := by
    rw [ha2, hb2, pow_succ, div_mul_cancel_left₀ (by positivity)]; norm_num
  calc Real.pi * ‖phiKernelL2 a b x - etaKernelL2 (Ioo (a ^ 2) (b ^ 2)) x‖ ^ 2
      ≤ Real.pi * ∫ s in Ioo (a ^ 2) (b ^ 2), (heatKernel s x x -
          killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x) :=
        mul_le_mul_of_nonneg_left hN Real.pi_pos.le
    _ = ∫ s in Ioo (a ^ 2) (b ^ 2), Real.pi * (heatKernel s x x -
          killedHeat (openSquare ∩ Metric.ball x (etaRad s)) s.toNNReal x x) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ s in Ioo (a ^ 2) (b ^ 2), 2 * Real.exp (-m) * s⁻¹ :=
        setIntegral_mono_on ((hheat.sub hie).const_mul _) (hinv.const_mul _) measurableSet_Ioo hpt
    _ = 2 * Real.exp (-m) * Real.log 4 := by
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hab2, integral_inv_of_pos hc₀ (hc₀.trans_le hab2),
          hlog]

end DZZ
end LQGMetric
