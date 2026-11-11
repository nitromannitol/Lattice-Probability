import Mathlib
import LatticeProb.Gauss.GFFCovSymm
import LatticeProb.Gauss.GFFCovPSD1

/-!
# Positive semidefiniteness of the whole-plane covariance, 2: the pairing and circle representations

Constructors of `SmearRep` for the two kinds of admissible observables (`LatticeProb.Gauss.GFFCovPSD1`):

* `pairingRep φ` (`φ` a test function): `α = ℂ`, `lam = volume`, `w = φ`, `p = id`; the estimate `logU` follows from
  `integrable_logAbsBall` (Lebesgue integrability of `log |·|` on balls, `GFFCovSymm`) by translation;
* `circleRep hr` (`r > 0`): `α = ℝ`, `lam = volume` on `(0, 2π]`, `w = (2π)⁻¹`, `p θ = circleMap z r θ`; the estimate
  `logU` uses `|log t| = 2 log⁺ t - log t` and Jensen's lower bound `2π log r ≤ ∫ log ‖circleMap - y‖`
  (`two_pi_mul_log_le_integral_log_circle`), which gives a constant independent of `y` on bounded sets.
-/

open MeasureTheory Metric Set Filter Topology
open scoped Real

namespace LatticeProb.Gauss

namespace GFFCovPSD

open GFFCovSymm

/-- `|log t| = 2 log⁺ t - log t` for `t ≥ 0`. -/
lemma abs_log_eq_two_posLog_sub {t : ℝ} (_ht : 0 ≤ t) :
    |Real.log t| = 2 * Real.posLog t - Real.log t := by
  unfold Real.posLog
  rcases le_total 0 (Real.log t) with h | h
  · rw [abs_of_nonneg h, max_eq_right h]
    ring
  · rw [abs_of_nonpos h, max_eq_left h]
    ring

/-- Uniform logarithmic estimate for a test function: `∫ |φ a| |log ‖a - y‖| ≤ C` for `‖y‖ ≤ R`. -/
lemma pairing_logU {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    ∀ R : ℝ, ∃ C : ℝ, ∀ y : ℂ, ‖y‖ ≤ R →
      Integrable (fun a => |φ a| * |Real.log ‖a - y‖|) volume ∧
        ∫ a, |φ a| * |Real.log ‖a - y‖| ∂volume ≤ C := by
  intro R
  obtain ⟨R0, hR0⟩ := exists_radius hφ.2.1
  obtain ⟨Cφ, hCφ⟩ := exists_bound hφ
  have hC0 : 0 ≤ Cφ := (norm_nonneg _).trans (hCφ 0)
  have hφm : Measurable φ := hφ.1.continuous.measurable
  refine ⟨Cφ * ∫ u, logAbsBall (R0 + |R| + 1) u, fun y hy => ?_⟩
  have hpt : ∀ a : ℂ, |φ a| * |Real.log ‖a - y‖| ≤ Cφ * logAbsBall (R0 + |R| + 1) (a - y) := by
    intro a
    by_cases h : φ a = 0
    · rw [h, abs_zero, zero_mul]
      exact mul_nonneg hC0 (logAbsBall_nonneg _ _)
    · have ha : ‖a‖ ≤ R0 := hR0 a h
      have hay : ‖a - y‖ < R0 + |R| + 1 := by
        have h1 : ‖a - y‖ ≤ ‖a‖ + ‖y‖ := norm_sub_le _ _
        have h2 : ‖y‖ ≤ |R| := hy.trans (le_abs_self R)
        linarith
      rw [logAbsBall_eq_abs hay]
      have hφa : |φ a| ≤ Cφ := by simpa [Real.norm_eq_abs] using hCφ a
      exact mul_le_mul_of_nonneg_right hφa (abs_nonneg _)
  have hint : Integrable (fun a => Cφ * logAbsBall (R0 + |R| + 1) (a - y)) volume :=
    ((integrable_logAbsBall (R0 + |R| + 1)).comp_sub_right y).const_mul Cφ
  have hmeas : Measurable (fun a : ℂ => |φ a| * |Real.log ‖a - y‖|) :=
    (continuous_abs.measurable.comp hφm).mul
      (continuous_abs.measurable.comp (Real.measurable_log.comp ((measurable_id.sub_const y).norm)))
  refine ⟨Integrable.mono' hint hmeas.aestronglyMeasurable (ae_of_all _ fun a => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact hpt a
  · calc ∫ a, |φ a| * |Real.log ‖a - y‖|
        ≤ ∫ a, Cφ * logAbsBall (R0 + |R| + 1) (a - y) :=
          integral_mono_of_nonneg (ae_of_all _ fun a => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hint
            (ae_of_all _ hpt)
      _ = Cφ * ∫ u, logAbsBall (R0 + |R| + 1) u := by
          rw [integral_const_mul, integral_sub_right_eq_self (fun u => logAbsBall (R0 + |R| + 1) u) y]

/-- The pairing observable `(h, φ)` as a smearing representation on `ℂ`. -/
noncomputable def pairingRep {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    SmearRep (GFFObservable.pairing φ) where
  α := ℂ
  lam := volume
  sfin := inferInstance
  w := φ
  p := id
  w_meas := hφ.1.continuous.measurable
  w_int := integrable_of_test hφ
  w_supp := by
    obtain ⟨R, hR⟩ := exists_radius hφ.2.1
    exact ⟨R, fun a ha => hR a ha⟩
  p_meas := measurable_id
  atom := fun y => by
    simp
  smear_eq := fun _ => rfl
  logU := pairing_logU hφ

/-- The circle parametrisation hits each point at most once on `(0, 2π]`; its preimages are null. -/
lemma circle_atom {r : ℝ} {z : ℂ} (hr : 0 < r) (y : ℂ) :
    volume.restrict (Ioc 0 (2 * π)) {θ : ℝ | circleMap z r θ = y} = 0 := by
  rw [Measure.restrict_apply' measurableSet_Ioc]
  refine Set.Subsingleton.measure_zero ?_ _
  have hinj : InjOn (circleMap z r) (Ioc 0 (2 * π)) := by
    have h := injOn_circleMap_of_abs_sub_le (c := z) (R := r) (a := 0) (b := 2 * π) hr.ne'
      (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)])
    rwa [Set.uIoc_of_le (by positivity)] at h
  rintro θ1 ⟨h1, h2⟩ θ2 ⟨h3, h4⟩
  have e1 : circleMap z r θ1 = y := h1
  have e2 : circleMap z r θ2 = y := h3
  exact hinj h2 h4 (e1.trans e2.symm)

/-- Uniform logarithmic estimate for the circle representation: for `‖y‖ ≤ R`,
`∫_{(0,2π]} (2π)⁻¹ |log ‖circleMap z r θ - y‖| dθ ≤ 2 log⁺(‖z‖ + |r| + R) - log r`. -/
lemma circle_logU {r : ℝ} {z : ℂ} (hr : 0 < r) :
    ∀ R : ℝ, ∃ C : ℝ, ∀ y : ℂ, ‖y‖ ≤ R →
      Integrable (fun θ : ℝ => |(2 * π)⁻¹| * |Real.log ‖circleMap z r θ - y‖|)
        (volume.restrict (Ioc 0 (2 * π))) ∧
        ∫ θ, |(2 * π)⁻¹| * |Real.log ‖circleMap z r θ - y‖| ∂(volume.restrict (Ioc 0 (2 * π))) ≤ C := by
  intro R
  refine ⟨2 * Real.posLog (‖z‖ + |r| + R) - Real.log r, fun y hy => ?_⟩
  have hpi : (0:ℝ) < 2 * π := by positivity
  have habs : |(2 * π)⁻¹| = (2 * π)⁻¹ := abs_of_pos (inv_pos.2 hpi)
  rw [habs]
  have hL : Integrable (fun θ : ℝ => Real.log ‖circleMap z r θ - y‖) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_log_circle z y r
  have hPm : Measurable (fun θ : ℝ => Real.posLog ‖circleMap z r θ - y‖) := by
    have hn : Measurable (fun θ : ℝ => ‖circleMap z r θ - y‖) :=
      ((continuous_circleMap z r).sub continuous_const).norm.measurable
    have hmax : (fun θ : ℝ => Real.posLog ‖circleMap z r θ - y‖) =
        fun θ => max 0 (Real.log ‖circleMap z r θ - y‖) := rfl
    rw [hmax]
    exact Measurable.max measurable_const (Real.measurable_log.comp hn)
  have hLp : Integrable (fun θ : ℝ => Real.posLog ‖circleMap z r θ - y‖)
      (volume.restrict (Ioc 0 (2 * π))) := by
    refine Integrable.mono' (integrable_const (Real.posLog (‖z‖ + |r| + R))) hPm.aestronglyMeasurable
      (ae_of_all _ fun θ => ?_)
    rw [Real.norm_of_nonneg Real.posLog_nonneg]
    refine Real.posLog_le_posLog (by linarith [norm_nonneg (circleMap z r θ - y)]) ?_
    have h1 : ‖circleMap z r θ - y‖ ≤ ‖circleMap z r θ‖ + ‖y‖ := norm_sub_le _ _
    have h2 : ‖circleMap z r θ‖ ≤ ‖z‖ + |r| := norm_circleMap_le' z r θ
    linarith
  have e : (fun θ : ℝ => |Real.log ‖circleMap z r θ - y‖|) =
      fun θ => 2 * Real.posLog ‖circleMap z r θ - y‖ - Real.log ‖circleMap z r θ - y‖ :=
    funext fun θ => abs_log_eq_two_posLog_sub (norm_nonneg _)
  have hA : Integrable (fun θ : ℝ => |Real.log ‖circleMap z r θ - y‖|)
      (volume.restrict (Ioc 0 (2 * π))) := by
    rw [e]
    exact (hLp.const_mul 2).sub hL
  refine ⟨hA.const_mul _, ?_⟩
  rw [integral_const_mul, e, integral_sub (hLp.const_mul 2) hL, integral_const_mul]
  have hP : ∫ θ, Real.posLog ‖circleMap z r θ - y‖ ∂(volume.restrict (Ioc 0 (2 * π)))
      ≤ 2 * π * Real.posLog (‖z‖ + |r| + R) := by
    have h := integral_mono hLp (integrable_const (Real.posLog (‖z‖ + |r| + R)))
      (fun θ => by
        have h1 : ‖circleMap z r θ - y‖ ≤ ‖circleMap z r θ‖ + ‖y‖ := norm_sub_le _ _
        have h2 : ‖circleMap z r θ‖ ≤ ‖z‖ + |r| := norm_circleMap_le' z r θ
        exact Real.posLog_le_posLog (norm_nonneg _ |>.trans' (by linarith)) (by linarith))
    rw [integral_const, volume_restrict_Ioc_univ_real, smul_eq_mul] at h
    exact h
  have hJ : 2 * π * Real.log r ≤ ∫ θ, Real.log ‖circleMap z r θ - y‖ ∂(volume.restrict (Ioc 0 (2 * π))) :=
    two_pi_mul_log_le_integral_log_circle z y hr
  calc (2 * π)⁻¹ * (2 * ∫ θ, Real.posLog ‖circleMap z r θ - y‖ ∂(volume.restrict (Ioc 0 (2 * π)))
          - ∫ θ, Real.log ‖circleMap z r θ - y‖ ∂(volume.restrict (Ioc 0 (2 * π))))
      ≤ (2 * π)⁻¹ * (2 * (2 * π * Real.posLog (‖z‖ + |r| + R)) - 2 * π * Real.log r) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hpi.le)
    _ = 2 * Real.posLog (‖z‖ + |r| + R) - Real.log r := by
        field_simp

/-- The circle average `h_r(z)` as a smearing representation on `ℝ`: `lam` is Lebesgue measure on `(0, 2π]`. -/
noncomputable def circleRep {r : ℝ} {z : ℂ} (hr : 0 < r) : SmearRep (GFFObservable.circle r z) where
  α := ℝ
  lam := volume.restrict (Ioc 0 (2 * π))
  sfin := inferInstance
  w := fun _ => (2 * π)⁻¹
  p := fun θ => circleMap z r θ
  w_meas := measurable_const
  w_int := integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  w_supp := ⟨‖z‖ + |r|, fun a _ => norm_circleMap_le' z r a⟩
  p_meas := (continuous_circleMap z r).measurable
  atom := fun y => circle_atom hr y
  smear_eq := fun f => by
    rw [GFFObservable.smear, Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity), smul_eq_mul,
      integral_const_mul]
  logU := circle_logU hr

end GFFCovPSD

end LatticeProb.Gauss
