import LatticeProb.Prob.FirstHitSpacedExitTrial
import LatticeProb.Prob.BrownianOpenExitStopping

/-! # Finite exits for first-hit rooted curves -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- The centered first-hit restriction of a proper curve exits any ball. -/
theorem firstHitNonnegativeCurve_openExitTime_ne_top
    (c : C(ℝ, ℂ)) (z : ℂ)
    (hproper : Tendsto c (cocompact ℝ) (cocompact ℂ)) (R : ℝ) :
    openExitTime (fun t (_ : Unit) => firstHitNonnegativeCurve c z t)
      (ball (0 : EuclideanSpace ℝ (Fin 2)) R) () ≠ ⊤ := by
  let t₀ := MatedCRTHarmonic.GMS4b.hitTime c z
  have htrans : Tendsto (fun w : ℂ => w - z) (cocompact ℂ) (cocompact ℂ) := by
    simpa [sub_eq_add_neg] using (Homeomorph.addRight (-z)).isClosedEmbedding.tendsto_cocompact
  have hcenter : Tendsto (firstHitCenteredCurve c z) (cocompact ℝ) (cocompact _) := by
    change Tendsto (fun s => Complex.orthonormalBasisOneI.repr (c (t₀ + s) - z)) _ _
    exact Complex.orthonormalBasisOneI.repr.toHomeomorph.isClosedEmbedding.tendsto_cocompact.comp
      (htrans.comp (hproper.comp (Homeomorph.addLeft t₀).isClosedEmbedding.tendsto_cocompact))
  have hfin := (openExitTime_ball_ne_top_of_tendsto_cocompact
    (firstHitCenteredCurve c z) hcenter 0 0 R).1
  change openExitTime (fun t (_ : Unit) => firstHitCenteredCurve c z (t : ℝ)) (ball 0 R) () ≠ ⊤
  simpa only [zero_add] using hfin

/-- Finite exits pass from a random continuous path to its path law. -/
theorem ae_openExitTime_ne_top_map_continuousPath
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (Φ : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (hΦ : Measurable Φ) (R : ℝ)
    (hfin : ∀ᵐ ω ∂P, openExitTime (fun t (_ : Unit) => Φ ω t) (ball 0 R) () ≠ ⊤) :
    ∀ᵐ w ∂(P.map Φ), openExitTime (fun t w => w t) (ball 0 R) w ≠ ⊤ := by
  let X : ℝ≥0 → C(ℝ≥0, EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
    fun t w => w t
  have hX : Measurable (openExitTime X (ball 0 R)) :=
    measurable_openExitTime
      (fun t => ((continuous_eval : Continuous (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0 => p.1 p.2)).comp
        (continuous_id.prodMk continuous_const)).measurable.stronglyMeasurable)
      (fun w => w.continuous) isOpen_ball
  change ∀ᵐ w ∂(P.map Φ), openExitTime X (ball 0 R) w ≠ ⊤
  apply (ae_map_iff hΦ.aemeasurable ((measurableSet_singleton ⊤).compl.preimage hX)).2
  exact hfin

/-- An almost surely proper curve has finite ball exit under its first-hit path law. -/
theorem ae_firstHitNonnegativeCurve_openExitTime_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c : Ω → C(ℝ, ℂ)) (hc : Measurable c) (z : ℂ)
    (hproper : ∀ᵐ ω ∂P, Tendsto (c ω) (cocompact ℝ) (cocompact ℂ))
    (R : ℝ) :
    ∀ᵐ w ∂(P.map (fun ω => firstHitNonnegativeCurve (c ω) z)),
      openExitTime (fun t w => w t) (ball (0 : EuclideanSpace ℝ (Fin 2)) R) w ≠ ⊤ := by
  apply ae_openExitTime_ne_top_map_continuousPath P _
    (measurable_firstHitNonnegativeCurve.comp (hc.prodMk measurable_const)) R
  filter_upwards [hproper] with ω hω
  exact firstHitNonnegativeCurve_openExitTime_ne_top (c ω) z hω R

end LatticeProb
