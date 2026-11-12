/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppAVar at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppASP2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L1Tr

/-!
# Ding–Gwynne Lemma A.2: the variance bound for `ĥ − ĥ^tr`, per time slice (task P2-DG3B)

DG (`metric-comparison-final.tex`, DG:2236–2240, "the same argument as Lemma A.1", i.e. the
proof of (A.3) at DG:2156–2232 with `U = ℂ`): the kernel of `(ĥ_t − ĥ^tr_t)(z)` at white-noise time
`s` is `w ↦ p(s/2; z, w) − p_{B_{1/10}(z)}(s/2; z, w)`. For `|z₁ − z₂| = δ ≤ 1/40`:

* `lintegral_kerDiff_le` — the `L²(dw)` norm² of the difference of the two kernels is at most
  `2 C₀ δ + 2 (p_{B(z₂,1/10+δ)}(s; z₂, z₂) − p_{B(z₂,1/10−δ)}(s; z₂, z₂))`:
  write the difference as a start-point change in the fixed ball `B(z₁, 1/10)`
  (`lintegral_sq_compK_sub_le_unif`, `ρ = 3/40`) minus a recentring of the ball at the fixed start
  `z₂` (`integral_sq_recentre_le`);
* `lintegral_Icc_diag_sub_le` — the time integral of the second term is `≤ π⁻¹ log((r+δ)/(r−δ))`
  (`integral_killedHeat_ball_diag_sub_le`).

Own route replacing DG's bridge coupling (DEVIATIONS DG3B-1, DG3B-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat

/-- DG's constant for the start-point term with `ρ = 3/40`. -/
def dgC0 : ℝ := 1 / (4 * Real.pi) + 34992 / (Real.pi * (3 / 40 : ℝ) ^ 6)

lemma dgC0_nonneg : 0 ≤ dgC0 := by unfold dgC0; have := Real.pi_pos; positivity

/-- The kernel of `ĥ − ĥ^tr` at `(s, w)` for `s ∈ [t², 1]`. -/
def kerDiff (z : ℂ) (s : ℝ) (w : ℂ) : ℝ :=
  heatKernel (s / 2) z w - killedHeat (Metric.ball z (1 / 10)) (s / 2).toNNReal z w

lemma kerDiff_eq_compK {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    kerDiff z s w = compK (Metric.ball z (1 / 10)) (s / 2).toNNReal z w := by
  unfold kerDiff compK
  rw [Real.coe_toNNReal _ (by positivity)]

/-- **Per-slice bound** for `δ = |z₁ − z₂| ≤ 1/40`. -/
theorem lintegral_kerDiff_le {s : ℝ} (hs : 0 < s) {z₁ z₂ : ℂ} (hδ : ‖z₁ - z₂‖ ≤ 1 / 40) :
    ∫⁻ w, ENNReal.ofReal ((kerDiff z₁ s w - kerDiff z₂ s w) ^ 2) ≤
      2 * ENNReal.ofReal (dgC0 * ‖z₁ - z₂‖) +
        2 * ENNReal.ofReal (killedHeat (Metric.ball z₂ (1 / 10 + ‖z₁ - z₂‖)) s.toNNReal z₂ z₂ -
          killedHeat (Metric.ball z₂ (1 / 10 - ‖z₁ - z₂‖)) s.toNNReal z₂ z₂) := by
  set τ : ℝ≥0 := (s / 2).toNNReal with hτdef
  have hτ : τ ≠ 0 := by simpa [hτdef] using hs
  have hττ : τ + τ = s.toNNReal := by
    rw [hτdef, ← Real.toNNReal_add (by positivity) (by positivity)]; ring_nf
  set B₁ := Metric.ball z₁ (1 / 10 : ℝ)
  set B₂ := Metric.ball z₂ (1 / 10 : ℝ)
  set SP : ℂ → ℝ := fun w => compK B₁ τ z₁ w - compK B₁ τ z₂ w
  set RC : ℂ → ℝ := fun w => killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w
  have hpt : ∀ w, kerDiff z₁ s w - kerDiff z₂ s w = SP w - RC w := by
    intro w
    rw [kerDiff_eq_compK hs, kerDiff_eq_compK hs]
    simp only [SP, RC, compK]
    ring
  have hSPm : Measurable SP :=
    (measurable_compK_right Metric.isOpen_ball hτ z₁).sub
      (measurable_compK_right Metric.isOpen_ball hτ z₂)
  -- the start-point term
  have hd : dist z₁ z₂ ≤ 1 / 40 := by rwa [dist_eq_norm]
  have hb1 : Metric.ball z₁ (3 / 40) ⊆ B₁ := Metric.ball_subset_ball (by norm_num)
  have hb2 : Metric.ball z₂ (3 / 40) ⊆ B₁ := fun w hw => by
    rw [Metric.mem_ball] at hw ⊢
    linarith [dist_triangle w z₂ z₁, dist_comm z₁ z₂]
  have hSP := lintegral_sq_compK_sub_le_unif Metric.isOpen_ball (by norm_num : (0 : ℝ) < 3 / 40)
    hb1 hb2 hτ
  -- the recentring term
  have hRC : ∫⁻ w, ENNReal.ofReal (RC w ^ 2) ≤
      ENNReal.ofReal (killedHeat (Metric.ball z₂ (1 / 10 + ‖z₁ - z₂‖)) s.toNNReal z₂ z₂ -
          killedHeat (Metric.ball z₂ (1 / 10 - ‖z₁ - z₂‖)) s.toNNReal z₂ z₂) := by
    have hint : Integrable fun w => RC w ^ 2 := by
      refine (WhiteNoise.integrable_heatKernel_mul_heatKernel _ (pos_of_ne hτ) z₂ z₂).mono'
        (((measurable_killedHeat_right Metric.isOpen_ball hτ z₂).sub
          (measurable_killedHeat_right Metric.isOpen_ball hτ z₂)).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun w => ?_)
      have a1 := killedHeat_nonneg B₁ τ z₂ w
      have a2 := killedHeat_nonneg B₂ τ z₂ w
      have a3 := killedHeat_le_heatKernel B₁ τ z₂ w
      have a4 := killedHeat_le_heatKernel B₂ τ z₂ w
      rw [Real.norm_of_nonneg (sq_nonneg _), sq]
      simp only [RC]
      have : |killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w| ≤ heatKernel τ z₂ w := by
        rw [abs_le]; constructor <;> linarith
      calc (killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w) *
            (killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w)
          = |killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w| *
            |killedHeat B₁ τ z₂ w - killedHeat B₂ τ z₂ w| := (abs_mul_abs_self _).symm
        _ ≤ heatKernel τ z₂ w * heatKernel τ z₂ w :=
            mul_le_mul this this (abs_nonneg _) (heatKernel_nonneg' _ _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := integral_sq_recentre_le (r := 1 / 10) (δ := ‖z₁ - z₂‖) (z₁ := z₁) (z₂ := z₂)
      le_rfl hτ
    rw [hττ] at h
    exact h
  calc ∫⁻ w, ENNReal.ofReal ((kerDiff z₁ s w - kerDiff z₂ s w) ^ 2)
      ≤ ∫⁻ w, (2 * ENNReal.ofReal (SP w ^ 2) + 2 * ENNReal.ofReal (RC w ^ 2)) :=
        lintegral_mono fun w => by rw [hpt w]; exact ofReal_sq_sub_le _ _
    _ = 2 * (∫⁻ w, ENNReal.ofReal (SP w ^ 2)) + 2 * ∫⁻ w, ENNReal.ofReal (RC w ^ 2) := by
        rw [lintegral_add_left' (((hSPm.pow_const 2).ennreal_ofReal).const_mul 2).aemeasurable,
          lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
    _ ≤ _ := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le)
          (mul_le_mul_of_nonneg_left hRC zero_le)
        exact hSP.trans (le_of_eq (by rfl))

/-- The time integral of the recentring term. -/
theorem lintegral_Icc_diag_sub_le (c : ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 10) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ∫⁻ s in Icc a 1, ENNReal.ofReal (killedHeat (Metric.ball c (1 / 10 + δ)) s.toNNReal c c -
        killedHeat (Metric.ball c (1 / 10 - δ)) s.toNNReal c c) ≤
      ENNReal.ofReal (Real.log ((1 / 10 + δ) / (1 / 10 - δ)) / Real.pi) := by
  set F : ℝ → ℝ := fun s => killedHeat (Metric.ball c (1 / 10 + δ)) s.toNNReal c c -
    killedHeat (Metric.ball c (1 / 10 - δ)) s.toNNReal c c
  have hF0 : ∀ s, 0 ≤ F s := fun s =>
    sub_nonneg.2 (killedHeat_mono (Metric.ball_subset_ball (by linarith)) _ _ _)
  have hmeas : ∀ ρ : ℝ, Measurable fun s : ℝ =>
      killedHeat (Metric.ball c ρ) s.toNNReal c c := fun ρ =>
    (measurable_killedHeat Metric.isOpen_ball).comp
      (measurable_real_toNNReal.prodMk (measurable_const.prodMk measurable_const))
  have hFm : Measurable F := (hmeas _).sub (hmeas _)
  have hint : IntegrableOn F (Icc a 1) := by
    refine IntegrableOn.of_bound measure_Icc_lt_top hFm.aestronglyMeasurable
      (2 * Real.pi * a)⁻¹ ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs => ?_))
    have hs0 : 0 < s := ha.trans_le hs.1
    rw [Real.norm_of_nonneg (hF0 s)]
    have h1 := killedHeat_le_heatKernel (Metric.ball c (1 / 10 + δ)) s.toNNReal c c
    have h2 := heatKernel_le_inv _ (NNReal.coe_nonneg s.toNNReal) c c
    have h3 := killedHeat_nonneg (Metric.ball c (1 / 10 - δ)) s.toNNReal c c
    rw [Real.coe_toNNReal _ hs0.le] at h1 h2
    have := Real.pi_pos
    have h4 : (2 * Real.pi * s)⁻¹ ≤ (2 * Real.pi * a)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [hs.1])
    simp only [F]
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hF0)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha1]
  exact integral_killedHeat_ball_diag_sub_le c (by linarith) (by linarith) ha ha1

end DG
end LQGMetric
