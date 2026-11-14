import LatticeProb.Prob.BrownianRestartCanonical
import LatticeProb.Prob.BrownianPathCoords
import LatticeProb.Prob.BrownianWeakMarkovPath

/-!
# The law of the centred path of Brownian motion

The motion of `LatticeProb.IsBrownianSpace` has generator `Δ / (2 d)`: each coordinate of
`B t - x`, scaled by `√d`, is a standard real Brownian motion. Its centred path `t ↦ B t - B 0` is
therefore the image of a standard Brownian law on the space of continuous paths under the map
`centredRescale d : γ ↦ (√d)⁻¹ • (γ - γ 0)`. By uniqueness of the standard Brownian law, the law
of the centred path is the same for every motion of `IsBrownianSpace` in a given dimension,
whatever its probability space and its starting point. Consequently the restarted path in the
Fubini form of the strong Markov property can be integrated out against any standard Brownian
law, through `centredRescale d`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- The path `t ↦ (√d)⁻¹ • (γ t - γ 0)`. It carries a path of a standard Brownian law to a path
of the motion of `IsBrownianSpace` started at the origin, whose generator is `Δ / (2 d)`. -/
noncomputable def centredRescale (d : ℕ) (γ : BrownianPath d) : BrownianPath d :=
  ⟨fun t => (Real.sqrt d)⁻¹ • (γ t - γ 0), by fun_prop⟩

section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

theorem measurable_centredRescale : Measurable (centredRescale d) :=
  (ContinuousMapBorel.ContinuousMap.measurable_iff_eval (X := ℝ≥0)
    (Y := EuclideanSpace ℝ (Fin d))).2 fun t => by
    change Measurable fun γ : BrownianPath d => (Real.sqrt d)⁻¹ • (γ t - γ 0)
    have h := fun s : ℝ≥0 => ContinuousMapBorel.ContinuousMap.measurable_eval (X := ℝ≥0)
      (Y := EuclideanSpace ℝ (Fin d)) s
    exact ((h t).sub (h 0)).const_smul (Real.sqrt d)⁻¹

/-- **The law of the centred path.** For a motion of `IsBrownianSpace` with continuous paths and
a standard Brownian law `μ`, the law of the centred path `t ↦ B t - B 0` is the image of `μ`
under `centredRescale d`. -/
theorem IsBrownianSpace.map_restartPath_zero_eq_map {x : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianSpace d x B P)
    (hcont : ∀ ω, Continuous fun t => B t ω) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) :
    P.map (restartPath B hcont fun _ => 0) = μ.map (centredRescale d) := by
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure
  obtain ⟨C, hCm, hC, -, hCB, hcoord, hindep⟩ := hB.exists_continuousVersion
  rw [standardBrownianLaw_unique hμ (isStandardBrownianLaw_map_pathMap hCm hC hcoord hindep),
    Measure.map_map measurable_centredRescale (measurable_pathMap C hCm hC)]
  refine Measure.map_congr ?_
  filter_upwards [hCB] with ω hω
  ext t : 1
  change B (0 + t) ω - B 0 ω = (Real.sqrt d)⁻¹ • (C t ω - C 0 ω)
  rw [zero_add, hω t, hω 0]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · ext i
    exact i.elim0
  · rw [← smul_sub (Real.sqrt d) (B t ω - x) (B 0 ω - x), sub_sub_sub_cancel_right,
      inv_smul_smul₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hd)).ne']

/-- **The strong Markov property in Fubini form against a standard Brownian law.** Under the
hypotheses of `IsBrownianSpace.setIntegral_restart_canonical`, the restarted path is integrated
out against any standard Brownian law `μ`, through the map `centredRescale d`. -/
theorem IsBrownianSpace.setIntegral_restart_standard (P : Measure Ω) [IsProbabilityMeasure P]
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration B hm) fun ω => (τ ω : ℝ≥0∞))
    {α : Type*} [MeasurableSpace α] (Y : Ω → α) (hY : Measurable[hτ.measurableSpace] Y)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (F : α × BrownianPath d → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun ω => F (Y ω, restartPath B hcont τ ω)) (P.restrict E))
    (μ : Measure (BrownianPath d)) (hμ : IsStandardBrownianLaw μ) :
    ∫ ω in E, F (Y ω, restartPath B hcont τ ω) ∂P
      = ∫ ω in E, (∫ w, F (Y ω, centredRescale d w) ∂μ) ∂P := by
  rw [IsBrownianSpace.setIntegral_restart_canonical P x B hB hm hcont τ hτ Y hY E hE F hF hFi,
    hB.map_restartPath_zero_eq_map hcont hμ]
  congr 1
  funext ω
  exact integral_map measurable_centredRescale.aemeasurable
    (hF.comp measurable_prodMk_left).aestronglyMeasurable

end

/-- **The law of the centred path does not depend on the motion.** Two motions of
`IsBrownianSpace` in the same dimension with continuous paths, on any probability spaces and from
any starting points, have the same law of the centred path. -/
theorem IsBrownianSpace.map_restartPath_zero_eq {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {d : ℕ} {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {x x' : EuclideanSpace ℝ (Fin d)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {B' : ℝ≥0 → Ω' → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hB' : IsBrownianSpace d x' B' P')
    (hcont : ∀ ω, Continuous fun t => B t ω) (hcont' : ∀ ω, Continuous fun t => B' t ω) :
    P.map (restartPath B hcont fun _ => 0) = P'.map (restartPath B' hcont' fun _ => 0) := by
  obtain ⟨C, hCm, hC, -, -, hcoord, hindep⟩ := hB.exists_continuousVersion
  have hμ := isStandardBrownianLaw_map_pathMap hCm hC hcoord hindep
  rw [hB.map_restartPath_zero_eq_map hcont hμ, hB'.map_restartPath_zero_eq_map hcont' hμ]

end LatticeProb
