/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L6EtaVar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Eta

/-!
# DZZ Lemma 2.5, `η` part: the variance bound (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 455:
`Var(η_δ(u) − η_δ(v)) = O(|u − v|/δ)` uniformly in `δ > 0`, `u, v`, proved as for `h̃`
(l. 466–514), modulo `BridgeShellBound C` (see `S2L6Eta`):

`‖K_u − K_v‖² = ‖K_u‖² + ‖K_v‖² − 2⟪K_u, K_v⟫`, `‖K_u‖² = ∫_I p_{D_u(s)}(s; u, u) ds`
(`D_u(s) = 𝕍 ∩ B(u, r(s))`), and `⟪K_u, K_v⟫ ≥ ∫_I p_{E(s)}(s; u, v) ds ≥ ∫_I (p_{D_u(s)}(s; u, u) −
b(s)) ds` with `πb(s) = (13 + C)|u − v| s^{−3/2}` (and the same with `u ↔ v`), so
`Var = π‖K_u − K_v‖² ≤ 2π ∫_{δ²}^∞ b = 4(13 + C)|u − v|/δ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise

theorem inner_etaKernelL2 {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hI0 : I ⊆ Ioi c₀) (u v : ℂ) :
    ⟪etaKernelL2 I u, etaKernelL2 I v⟫ = ∫ p, etaKernel I u p * etaKernel I v p := by
  have hu := memLp_etaKernel hI hc₀ hI0 u
  have hv := memLp_etaKernel hI hc₀ hI0 v
  rw [etaKernelL2, etaKernelL2, dite_eq_left_of_eq_true (eq_true hu),
    dite_eq_left_of_eq_true (eq_true hv), L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with p h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

/-- The cross term: if `g ≤ p_{E(s)}(s; u, v)` on `I` then `∫_I g ≤ ∫ K^η_u K^η_v`. -/
theorem integral_le_integral_etaKernel_mul {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hI0 : I ⊆ Ioi c₀) (u v : ℂ) {g : ℝ → ℝ} (hg : IntegrableOn g I)
    (hpt : ∀ s ∈ I, g s ≤ killedHeat (openSquare ∩ Metric.ball u (etaRad s) ∩
      Metric.ball v (etaRad s)) s.toNNReal u v) :
    ∫ s in I, g s ≤ ∫ p, etaKernel I u p * etaKernel I v p := by
  have hint : Integrable (fun p => etaKernel I u p * etaKernel I v p) :=
    (memLp_etaKernel hI hc₀ hI0 u).integrable_mul (memLp_etaKernel hI hc₀ hI0 v)
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, integral_prod _ hint,
    ← integral_indicator hI]
  refine integral_mono (hg.integrable_indicator hI) hint.integral_prod_left fun s => ?_
  by_cases hs : s ∈ I
  · simp only [indicator_of_mem hs, etaKernel]
    have hs0 : (0 : ℝ) < s := hc₀.trans (hI0 hs)
    set r := etaRad s
    set t := (s / 2).toNNReal
    have ht : t ≠ 0 := by simp only [t, ne_eq, Real.toNNReal_eq_zero, not_le]; linarith
    have ht' : (0 : ℝ) < t := by
      simp only [t, Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ s / 2)]; linarith
    have hsum : t + t = s.toNNReal := by
      simp only [t]; rw [← Real.toNNReal_add (by linarith) (by linarith)]; ring_nf
    set E := openSquare ∩ Metric.ball u r ∩ Metric.ball v r
    have hE : IsOpen E :=
      (LQGMetric.isOpen_openSquare.inter Metric.isOpen_ball).inter Metric.isOpen_ball
    have hDu : IsOpen (openSquare ∩ Metric.ball u r) :=
      LQGMetric.isOpen_openSquare.inter Metric.isOpen_ball
    have hDv : IsOpen (openSquare ∩ Metric.ball v r) :=
      LQGMetric.isOpen_openSquare.inter Metric.isOpen_ball
    have hEu : E ⊆ openSquare ∩ Metric.ball u r := inter_subset_left
    have hEv : E ⊆ openSquare ∩ Metric.ball v r := fun x hx => ⟨hx.1.1, hx.2⟩
    have hH := integrable_heatKernel_mul_heatKernel (t : ℝ) ht' u v
    have dom : ∀ (A B : Set ℂ), IsOpen A → IsOpen B → Integrable fun w =>
        killedHeat A t u w * killedHeat B t v w := fun A B hA hB =>
      Integrable.mono' hH ((measurable_killedHeat_right hA ht u).mul
        (measurable_killedHeat_right hB ht v)).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (killedHeat_nonneg _ _ _ _)
            (killedHeat_nonneg _ _ _ _))]
          exact mul_le_mul (killedHeat_le_heatKernel _ _ _ _) (killedHeat_le_heatKernel _ _ _ _)
            (killedHeat_nonneg _ _ _ _) (heatKernel_nonneg' _ _ _))
    refine (hpt s hs).trans ?_
    rw [← hsum, ← integral_killedHeat_mul_killedHeat hE ht u v]
    refine integral_mono (dom E E hE hE) (dom _ _ hDu hDv) fun w => ?_
    exact mul_le_mul (killedHeat_mono hEu _ _ _) (killedHeat_mono hEv _ _ _)
      (killedHeat_nonneg _ _ _ _) (killedHeat_nonneg _ _ _ _)
  · simp [hs, etaKernel]

/-- Pointwise: `p_{D_u}(s; u, u) − b(s) ≤ p_{E(s)}(s; u, v)`, `π b(s) = (13 + C)|u − v| s^{−3/2}`. -/
lemma killedHeat_eta_cross_ge {C : ℝ} (hC0 : 0 ≤ C) (hC : BridgeShellBound C) {s : ℝ}
    (hs : 0 < s) (u v : ℂ) :
    killedHeat (openSquare ∩ Metric.ball u (etaRad s)) s.toNNReal u u -
        (13 + C) / Real.pi * ‖u - v‖ * s ^ (-(3 / 2 : ℝ)) ≤
      killedHeat (openSquare ∩ Metric.ball u (etaRad s) ∩ Metric.ball v (etaRad s))
        s.toNNReal u v := by
  have htn : s.toNNReal ≠ 0 := by simpa using hs
  have hq := bridgeStay_eta_sub_le hC0 hC htn u v (etaRad s)
  rw [Real.coe_toNNReal _ hs.le] at hq
  have h := pi_killedHeat_sub_le_of_bridge hs (by linarith : (0 : ℝ) ≤ 12 + C) u v hq
  have hpi := Real.pi_pos
  have e : Real.pi * ((13 + C) / Real.pi * ‖u - v‖ * s ^ (-(3 / 2 : ℝ))) =
      (12 + C + 1) * ‖u - v‖ * s ^ (-(3 / 2 : ℝ)) := by field_simp; ring
  have h2 := (mul_le_mul_iff_of_pos_left hpi).mp (h.trans e.symm.le)
  linarith

lemma integrableOn_killedHeat_eta {I : Set ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hI0 : I ⊆ Ioi c₀)
    (u : ℂ) : IntegrableOn (fun s : ℝ =>
      killedHeat (openSquare ∩ Metric.ball u (etaRad s)) s.toNNReal u u) I :=
  Integrable.mono' (integrableOn_killedHeat_of_subset LQGMetric.isOpen_openSquare
    (by norm_num : (0 : ℝ) ≤ 2) openSquare_subset_ball hc₀ hI0 u u)
    (measurable_killedHeat_eta_time u).aestronglyMeasurable
    (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
      exact killedHeat_mono inter_subset_left _ _ _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ Lemma 2.5, `η` part** (l. 455), for every time set `I ⊆ (δ², ∞)` (so for `η_δ` and the
bands `η_δ^{δ'}`), assuming the bridge shell bound:
`Var(η_I(u) − η_I(v)) ≤ 4(13 + C)|u − v|/δ`. -/
theorem dzz_lemma25_etaField {C : ℝ} (hC0 : 0 ≤ C) (hC : BridgeShellBound C)
    (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) {I : Set ℝ} (hI : MeasurableSet I)
    (hI0 : I ⊆ Ioi (δ ^ 2)) (u v : ℂ) :
    Var[fun ω => etaField W I u ω - etaField W I v ω; P] ≤ 4 * (13 + C) * ‖u - v‖ / δ := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hI0' : I ⊆ Ioi 0 := hI0.trans (Ioi_subset_Ioi hδ2.le)
  set D := ‖u - v‖ with hD
  set b : ℝ → ℝ := fun s => (13 + C) / Real.pi * D * s ^ (-(3 / 2 : ℝ)) with hb
  have hpow : IntegrableOn (fun s : ℝ => s ^ (-(3 / 2 : ℝ))) (Ioi (δ ^ 2)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hδ2
  have hbi : IntegrableOn b I := (hpow.mono_set hI0).const_mul _
  have hau := integrableOn_killedHeat_eta hδ2 hI0 u
  have hav := integrableOn_killedHeat_eta hδ2 hI0 v
  -- the two lower bounds for the cross term
  have l1 := integral_le_integral_etaKernel_mul hI hδ2 hI0 u v
    (g := fun s => killedHeat (openSquare ∩ Metric.ball u (etaRad s)) s.toNNReal u u - b s)
    (hau.sub hbi) fun s hs =>
    killedHeat_eta_cross_ge hC0 hC (hδ2.trans (hI0 hs)) u v
  have l2 := integral_le_integral_etaKernel_mul hI hδ2 hI0 u v
    (g := fun s => killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v - b s)
    (hav.sub hbi) fun s hs => by
    have h := killedHeat_eta_cross_ge hC0 hC (hδ2.trans (hI0 hs)) v u
    rw [norm_sub_rev, Set.inter_right_comm, killedHeat_symm
      ((LQGMetric.isOpen_openSquare.inter Metric.isOpen_ball).inter Metric.isOpen_ball)] at h
    exact h
  -- the diagonal terms
  have nu : ∫ p, etaKernel I u p * etaKernel I u p =
      ∫ s in I, killedHeat (openSquare ∩ Metric.ball u (etaRad s)) s.toNNReal u u := by
    simpa [sq] using integral_sq_eq_of_lintegral (measurable_etaKernel hI u)
      (etaKernel_nonneg _ _) (measurable_killedHeat_eta_time u)
      (fun s => killedHeat_nonneg _ _ _ _) (lintegral_etaKernel_sq hI hI0' u)
  have nv : ∫ p, etaKernel I v p * etaKernel I v p =
      ∫ s in I, killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v := by
    simpa [sq] using integral_sq_eq_of_lintegral (measurable_etaKernel hI v)
      (etaKernel_nonneg _ _) (measurable_killedHeat_eta_time v)
      (fun s => killedHeat_nonneg _ _ _ _) (lintegral_etaKernel_sq hI hI0' v)
  -- `∫_I b ≤ (13 + C)/π · D · 2/δ`
  have hbint : ∫ s in I, b s ≤ (13 + C) / Real.pi * D * (2 / δ) := by
    rw [hb, integral_const_mul, ← integral_Ioi_rpow_three_halves hδ]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine setIntegral_mono_set hpow ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun s hs => ?_)) (Eventually.of_forall hI0)
    exact Real.rpow_nonneg (hδ2.trans hs).le _
  unfold etaField
  rw [variance_sqrtPi_sub hW, @norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_etaKernelL2 hI hδ2 hI0, inner_etaKernelL2 hI hδ2 hI0,
    inner_etaKernelL2 hI hδ2 hI0, nu, nv]
  rw [integral_sub hau hbi] at l1
  rw [integral_sub hav hbi] at l2
  have hpi := Real.pi_pos
  have key : (∫ s in I, killedHeat (openSquare ∩ Metric.ball u (etaRad s)) s.toNNReal u u) -
      2 * (∫ p, etaKernel I u p * etaKernel I v p) +
      ∫ s in I, killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v ≤
      2 * ((13 + C) / Real.pi * D * (2 / δ)) := by linarith
  calc Real.pi * ((∫ s in I, killedHeat (openSquare ∩ Metric.ball u (etaRad s)) s.toNNReal u u) -
        2 * (∫ p, etaKernel I u p * etaKernel I v p) +
        ∫ s in I, killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v)
      ≤ Real.pi * (2 * ((13 + C) / Real.pi * D * (2 / δ))) :=
        mul_le_mul_of_nonneg_left key hpi.le
    _ = 4 * (13 + C) * D / δ := by field_simp; ring

end DZZ
end LQGMetric
