import LatticeProb.Prob.BrownianExitDynkin
import LatticeProb.Prob.BrownianExitKelvin
import LatticeProb.Prob.BrownianOccupationTrunc
import LatticeProb.Analysis.BrownianHeatTime

/-!
# Occupation of a ball by Brownian motion

The Green kernel for the occupation measure of Brownian motion stopped on leaving a ball.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- The Green kernel of a ball with centre `x`. -/
def ballGreen (d : ℕ) (s : ℝ) (x z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if ‖x - z‖ < s then
    (if d = 2 then (1 / (2 * Real.pi)) * Real.log (s / ‖x - z‖)
     else (1 / (4 * Real.pi)) * (1 / ‖x - z‖ - 1 / s))
  else 0

/-- The exit time from a ball has finite expectation in positive dimension. -/
theorem IsBrownianSpace.integrable_exitTime {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (s : ℝ) : Integrable (fun ω => (exitTime B x s ω).toReal) P := by
  have := hB.isProbabilityMeasure
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hsd : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hdpos).ne'
  have hc : (Real.sqrt d)⁻¹ ≠ 0 := inv_ne_zero hsd
  obtain ⟨C, hCm, hC, -, hCW, hcoord, hindep⟩ := hB.exists_continuousVersion
  have hμ : IsStandardBrownianLaw (P.map (pathMap C hC)) :=
    isStandardBrownianLaw_map_pathMap hCm hC hcoord hindep
  let V := (fun w : EuclideanSpace ℝ (Fin d) => x + (Real.sqrt d)⁻¹ • w) ⁻¹' Metric.ball x s
  have hVo : IsOpen V := Metric.isOpen_ball.preimage (by fun_prop)
  have hVb : Bornology.IsBounded V := isBounded_preimage_affine Metric.isBounded_ball x hc
  have hτm : Measurable (continuousExitTime V 0) := measurable_continuousExitTime hVo 0
  have hmap : Measurable (pathMap C hC) := measurable_pathMap C hCm hC
  have hτ : ∀ᵐ ω ∂P, exitTime B x s ω = continuousExitTime V 0 (pathMap C hC ω) := by
    simpa only [exitTime_eq_openExitTime_ball] using
      (ae_openExitTime_eq_continuousExitTime hd hC hCW (U := Metric.ball x s))
  apply integrable_toReal_of_lintegral_ne_top (measurable_exitTime hm hcont x s).aemeasurable
  have hfin := standardBrownianLaw_lintegral_continuousExitTime_lt_top hd hμ hVo hVb 0
  rw [lintegral_map hτm hmap] at hfin
  have heq : (∫⁻ ω, exitTime B x s ω ∂P) =
      ∫⁻ ω, continuousExitTime V 0 (pathMap C hC ω) ∂P := lintegral_congr_ae hτ
  rw [heq]
  exact hfin.ne

/-- The accumulated reward of a bounded measurable function up to the exit time is integrable. -/
theorem IsBrownianSpace.integrable_occupation_exitTime {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (s : ℝ) {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Measurable φ)
    (hb : ∃ M, ∀ z, |φ z| ≤ M) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..(exitTime B x s ω).toReal,
      φ (B r.toNNReal ω)) P := by
  have := hB.isProbabilityMeasure
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  let τ : Ω → ℝ := fun ω => (exitTime B x s ω).toReal
  have hτ : Measurable τ := ENNReal.measurable_toReal.comp (measurable_exitTime hm hcont x s)
  have hτint : Integrable τ P := hB.integrable_exitTime hd hm hcont s
  have hBjoint := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
  have hF : Measurable (fun p : Ω × ℝ => φ (B p.2.toNNReal p.1)) :=
    hφ.comp (hBjoint.measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
  let A : Set (Ω × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ τ p.1}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hτ.comp measurable_fst))
  have hI : StronglyMeasurable (fun ω => ∫ r in (0 : ℝ)..τ ω, φ (B r.toNNReal ω)) := by
    have h := (hF.indicator hA).stronglyMeasurable.integral_prod_right' (ν := volume)
    convert h using 1
    funext ω
    rw [intervalIntegral.integral_of_le ENNReal.toReal_nonneg]
    change (∫ r in Set.Ioc 0 (τ ω), φ (B r.toNNReal ω)) = _
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  refine (hτint.const_mul M).mono' hI.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro ω
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := τ ω)
    (fun r _ => show ‖φ (B r.toNNReal ω)‖ ≤ M by simpa only [Real.norm_eq_abs] using hM _)
  simpa [τ, abs_of_nonneg ENNReal.toReal_nonneg, hM0] using hbound

/-- A logarithmic potential with its pole outside the closed ball satisfies the exit identity. -/
theorem IsBrownianSpace.integral_log_norm_exit_ball_of_outside {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (x : EuclideanSpace ℝ (Fin 2))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)) (hB : IsBrownianSpace 2 x B P)
    {s : ℝ} {y : EuclideanSpace ℝ (Fin 2)} (hy : s < ‖y - x‖) :
    ∫ ω, Real.log ‖B (exitTime B x s ω).toNNReal ω - y‖ ∂P = Real.log ‖x - y‖ := by
  have hsub : closure (Metric.ball x s) ⊆ {y}ᶜ := by
    intro z hz hzy
    have hz' : ‖z - x‖ ≤ s := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using
        (Metric.closure_ball_subset_closedBall hz)
    have : z = y := hzy
    subst z
    linarith
  have hh : HarmonicNearClosure (fun z => Real.log ‖z - y‖) (Metric.ball x s) :=
    harmonicNearClosure_iff.2 ((harmonicOnNhd_log_norm_sub y).mono hsub)
  simpa only [exitTime_eq_openExitTime_ball] using
    (integral_openExit_harmonicNearClosure (by norm_num) hB Metric.isOpen_ball
      Metric.isBounded_ball hh)

/-- An inverse-distance potential with its pole outside the closed ball satisfies the exit identity. -/
theorem IsBrownianSpace.integral_inv_norm_exit_ball_of_outside {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (x : EuclideanSpace ℝ (Fin 3))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : IsBrownianSpace 3 x B P)
    {s : ℝ} {y : EuclideanSpace ℝ (Fin 3)} (hy : s < ‖y - x‖) :
    ∫ ω, ‖B (exitTime B x s ω).toNNReal ω - y‖⁻¹ ∂P = ‖x - y‖⁻¹ := by
  have hsub : closure (Metric.ball x s) ⊆ {y}ᶜ := by
    intro z hz hzy
    have hz' : ‖z - x‖ ≤ s := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using
        (Metric.closure_ball_subset_closedBall hz)
    have : z = y := hzy
    subst z
    linarith
  have hh : HarmonicNearClosure (fun z => ‖z - y‖⁻¹) (Metric.ball x s) :=
    harmonicNearClosure_iff.2 ((harmonicOnNhd_inv_norm_sub y).mono hsub)
  simpa only [exitTime_eq_openExitTime_ball] using
    (integral_openExit_harmonicNearClosure (by norm_num) hB Metric.isOpen_ball
      Metric.isBounded_ball hh)

end LatticeProb
