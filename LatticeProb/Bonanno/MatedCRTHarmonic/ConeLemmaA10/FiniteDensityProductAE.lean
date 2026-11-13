/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.FiniteDensityProductAE at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FiniteDensityLimit
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FiniteDensityMeasurable

/-!
# Product-space almost-sure convergence of the finite rooting densities

The fixed-root density limit can be lifted over any finite root measure whose almost-everywhere
support lies strictly inside the unit disk. The event is measurable because both the finite
density and the circle-average version of the limiting density are jointly measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric

/-- The fixed-root density limit, with the measurable circle-average version in its limit. -/
private theorem ae_tendsto_finiteCircleDensity_circleAvg
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ}
    (hh : IsNormalizedWPGFF h P)
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hagree : ∀ r, 0 < r → ∀ w,
      (fun ω => H r w ω) =ᵐ[P] fun ω => circleAvg (h ω) r w)
    (γ : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (z : ℂ)
    (hz : ‖z‖ + ε < 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n => finiteCircleDensity (h := h) γ n z ε ω) atTop
      (𝓝 (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) *
        Real.exp (γ * circleAvg (h ω) ε z)))) := by
  filter_upwards [ae_tendsto_finiteCircleDensity hh hH hagree γ hε hε1 z hz,
    hagree ε hε z] with ω hlim heq
  simpa only [heq] using hlim

/-- If a finite root law is supported almost everywhere on the strict interior
`‖z‖ + ε < 1`, then the finite Wick densities converge almost surely on the field-root product
to the density written using the jointly measurable circle-average version. -/
theorem ae_tendsto_finiteCircleDensity_prod
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ}
    (hh : IsNormalizedWPGFF h P)
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hagree : ∀ r, 0 < r → ∀ w,
      (fun ω => H r w ω) =ᵐ[P] fun ω => circleAvg (h ω) r w)
    (γ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, ‖z‖ + ε < 1) :
    ∀ᵐ p ∂(P.prod ν),
      Tendsto (fun n => finiteCircleDensity (h := h) γ n p.2 ε p.1) atTop
        (𝓝 (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) *
          Real.exp (γ * circleAvg (h p.1) ε p.2)))) := by
  let target : Ω × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg (h p.1) ε p.2))
  let pred : Ω → ℂ → Prop := fun ω z =>
    Tendsto (fun n => finiteCircleDensity (h := h) γ n z ε ω) atTop
      (𝓝 (target (ω, z)))
  letI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have htarget : Measurable target := by
    dsimp [target]
    have hcir : Measurable fun p : Ω × ℂ => circleAvg (h p.1) ε p.2 :=
      measurable_circleAvg.comp (f := fun p : Ω × ℂ => (h p.1, ε, p.2))
        ((hh.1.measurable.comp measurable_fst).prodMk
          (measurable_const.prodMk measurable_snd))
    have hinner : Measurable fun p : Ω × ℂ => γ * circleAvg (h p.1) ε p.2 :=
      measurable_const.mul hcir
    have hexp : Measurable fun p : Ω × ℂ =>
        Real.exp (γ * circleAvg (h p.1) ε p.2) := Real.measurable_exp.comp hinner
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul hexp)
  have hseq : ∀ n, Measurable fun p : Ω × ℂ =>
      finiteCircleDensity (h := h) γ n p.2 ε p.1 := by
    intro n
    exact measurable_finiteCircleDensity hh γ n ε
  have hmeas : MeasurableSet {p : Ω × ℂ |
      Tendsto (fun n => finiteCircleDensity (h := h) γ n p.2 ε p.1) atTop
        (𝓝 (target p))} := by
    exact MeasureTheory.measurableSet_tendsto_fun hseq htarget
  have hroot : ∀ᵐ z ∂ν, ∀ᵐ ω ∂P, pred ω z := by
    filter_upwards [hν] with z hz
    have hεz : ε < 1 := by
      have := norm_nonneg z
      linarith
    filter_upwards [ae_tendsto_finiteCircleDensity_circleAvg hh hH hagree γ hε hεz z hz]
      with ω hlim
    exact hlim
  have hfieldRoot : ∀ᵐ ω ∂P, ∀ᵐ z ∂ν, pred ω z :=
    (Measure.ae_ae_comm (μ := P) (ν := ν) (p := pred) (by
      simpa [pred, target] using hmeas)).2 hroot
  have hprod := (Measure.ae_prod_iff_ae_ae
    (p := fun p : Ω × ℂ => pred p.1 p.2) (by
      simpa [pred, target] using hmeas)).2 hfieldRoot
  simpa only [pred, target] using hprod

end MatedCRTHarmonic.ConeLemmaA10

