/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel

/-!
# DZZ Lemma 2.5 for `h̃` (`lem-variance-continuity`; task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 452–515:
`Var(h̃_δ(u) − h̃_δ(v)) = O(|u − v|/δ)` uniformly in `δ > 0`, `u, v`.

Proof as in DZZ (after RV14, App. A): by l. 512 (`variance_wnField_sub`) the variance is
`π∫_{δ²}^∞ (p(t;u,u) − p(t;u,v)) dt + π∫_{δ²}^∞ (p(t;v,v) − p(t;u,v)) dt`, and each term is
`≤ ∫_{δ²}^∞ 7|u − v| t^{−3/2} dt = 14|u − v|/δ` (eq-feb23, from `pi_killedHeat_sub_le`).
We prove it for every time set `I ⊆ (δ², ∞)` (so also for the bands `h̃_δ^{δ'}` used in the proof
of Lemma 2.7, eq-feb25), with the explicit constant `28`.

The `η` half of Lemma 2.5 ("follows from a similar argument", l. 460–461) is not done here: the
domain `𝕍 ∩ B(v, r(s))` of `η`'s kernel varies with `s` and `v` (see handoff/P2-DZZPRE.md).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise

/-- `s ↦ p_A(s; u, v)` is integrable on `I ⊆ (c₀, ∞)` (bounded open `A`, all `u, v`). -/
theorem integrableOn_killedHeat_of_subset {A : Set ℂ} (hA : IsOpen A) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hAR : A ⊆ Metric.ball c R) {I : Set ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hI0 : I ⊆ Ioi c₀) (u v : ℂ) :
    IntegrableOn (fun s : ℝ => killedHeat A s.toNNReal u v) I := by
  refine ⟨(measurable_killedHeat_time hA u v).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun s => killedHeat_nonneg _ _ _ _)]
  exact lintegral_killedHeat_lt_top hR hAR hc₀ hI0 u v

lemma integral_Ioi_rpow_three_halves {δ : ℝ} (hδ : 0 < δ) :
    ∫ s in Ioi (δ ^ 2), s ^ (-(3 / 2 : ℝ)) = 2 / δ := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) (by positivity),
    show -(3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num, Real.rpow_neg (by positivity),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hδ.le]
  field_simp

/-- **DZZ (eq-feb23)**, for any time set `I ⊆ (δ², ∞)`:
`π ∫_I (p_𝕍(t; u, u) − p_𝕍(t; u, v)) dt ≤ 14 |u − v|/δ`. -/
theorem pi_integral_killedHeat_sub_le {δ : ℝ} (hδ : 0 < δ) {I : Set ℝ} (hI : MeasurableSet I)
    (hI0 : I ⊆ Ioi (δ ^ 2)) (u v : ℂ) :
    Real.pi * ((∫ s in I, killedHeat openSquare s.toNNReal u u) -
      ∫ s in I, killedHeat openSquare s.toNNReal u v) ≤ 14 * ‖u - v‖ / δ := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hiu := integrableOn_killedHeat_of_subset LQGMetric.isOpen_openSquare
    (by norm_num : (0 : ℝ) ≤ 2) openSquare_subset_ball hδ2 hI0 u u
  have hiv := integrableOn_killedHeat_of_subset LQGMetric.isOpen_openSquare
    (by norm_num : (0 : ℝ) ≤ 2) openSquare_subset_ball hδ2 hI0 u v
  have hpow : IntegrableOn (fun s : ℝ => 7 * ‖u - v‖ * s ^ (-(3 / 2 : ℝ))) (Ioi (δ ^ 2)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hδ2).const_mul _
  rw [← integral_sub hiu hiv, ← integral_const_mul]
  calc ∫ s in I, Real.pi * (killedHeat openSquare s.toNNReal u u -
        killedHeat openSquare s.toNNReal u v)
      ≤ ∫ s in I, 7 * ‖u - v‖ * s ^ (-(3 / 2 : ℝ)) := by
        refine setIntegral_mono_on ((hiu.sub hiv).const_mul _) (hpow.mono_set hI0) hI
          fun s hs => pi_killedHeat_sub_le (hδ2.trans (hI0 hs)) u v
    _ ≤ ∫ s in Ioi (δ ^ 2), 7 * ‖u - v‖ * s ^ (-(3 / 2 : ℝ)) := by
        refine setIntegral_mono_set hpow ((ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall fun s hs => ?_)) (Eventually.of_forall hI0)
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (hδ2.trans hs).le _)
    _ = 14 * ‖u - v‖ / δ := by
        rw [integral_const_mul, integral_Ioi_rpow_three_halves hδ]; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ Lemma 2.5, `h̃` part** (l. 452–515), for every time set `I ⊆ (δ², ∞)` (in particular
`h̃_δ = wnField W openSquare (Ioi (δ²))` and the bands `h̃_δ^{δ'}`):
`Var(F(u) − F(v)) ≤ 28 |u − v|/δ`, for all `u, v` and `δ > 0`. -/
theorem dzz_lemma25_wnField (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) {I : Set ℝ}
    (hI : MeasurableSet I) (hI0 : I ⊆ Ioi (δ ^ 2)) (u v : ℂ) :
    Var[fun ω => wnField W openSquare I u ω - wnField W openSquare I v ω; P] ≤
      28 * ‖u - v‖ / δ := by
  rw [variance_wnField_sub hW LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball hI (by positivity : (0 : ℝ) < δ ^ 2) hI0]
  have h1 := pi_integral_killedHeat_sub_le hδ hI hI0 u v
  have h2 := pi_integral_killedHeat_sub_le hδ hI hI0 v u
  have hs : (fun s : ℝ => killedHeat openSquare s.toNNReal v u) =
      fun s => killedHeat openSquare s.toNNReal u v :=
    funext fun s => killedHeat_symm LQGMetric.isOpen_openSquare _ _ _
  rw [hs, norm_sub_rev] at h2
  have e : 28 * ‖u - v‖ / δ = 14 * ‖u - v‖ / δ + 14 * ‖u - v‖ / δ := by ring
  rw [e]
  refine le_of_eq_of_le ?_ (add_le_add h1 h2)
  ring

/-- **DZZ Lemma 2.5, `h̃` part** (l. 455): `Var(h̃_δ(u) − h̃_δ(v)) ≤ 28|u − v|/δ`. -/
theorem dzz_lemma25_tildeH (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (u v : ℂ) :
    Var[fun ω => tildeHInf W δ u ω - tildeHInf W δ v ω; P] ≤ 28 * ‖u - v‖ / δ :=
  dzz_lemma25_wnField hW hδ measurableSet_Ioi subset_rfl u v

end DZZ
end LQGMetric
