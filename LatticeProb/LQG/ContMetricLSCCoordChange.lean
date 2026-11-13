import LatticeProb.LQG.ContMetricLSCTranslate

/-!
# The coordinate change formula for continuous metrics as lower semicontinuous metrics

Let `D` assign to each distribution `h` a continuous metric `D_h` satisfying the coordinate change
formula of Gwynne-Miller (1.15): for a whole-plane Gaussian free field plus a continuous function
`h`, every `r > 0` and `z ∈ ℂ`, almost surely
`D_h(r u + z, r v + z) = D_{h(r · + z) + Q log r}(u, v)` for all `u, v`.

The same identity then holds for the associated lower semicontinuous metrics
`contToLSCMetric ∘ D`, in the form of the coordinate change axiom of Ding-Gwynne for strong LQG
metrics (radii in `Set.Ioi 0`, real scalar multiplication `r • u`), with the composed field written
as the affine composition `h(r · + z)`.
-/

open MeasureTheory

namespace LatticeProb.LQG

/-- **Coordinate change for `contToLSCMetric ∘ D`.** From the coordinate change formula of `D`
(Gwynne-Miller (1.15)), for every `r > 0` and `z ∈ ℂ`, almost surely
`(contToLSCMetric D_h)(r • u + z, r • v + z) = (contToLSCMetric D_{h(r · + z) + Q log r})(u, v)`
for all `u, v ∈ ℂ`. -/
theorem coordChange_contToLSCMetric_of_coord {Q' : ℝ}
    {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hcoord : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (r * u + z, r * v + z) =
          (D (LQGMetric.addConst (LQGMetric.affineComp r z (h ω)) (Q' * Real.log r))).1 (u, v)) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ (r : Set.Ioi (0 : ℝ)) (z : ℂ),
        ∀ᵐ ω ∂P, ∀ u v : ℂ,
          (contToLSCMetric (D (h ω))).1 ((r : ℝ) • u + z, (r : ℝ) • v + z) =
            (contToLSCMetric (D (LQGMetric.addConst (LQGMetric.affineComp (r : ℝ) z (h ω))
              (Q' * Real.log (r : ℝ))))).1 (u, v) := by
  intro Ω _ P _ h hh r z
  filter_upwards [hcoord P h hh (r : ℝ) r.2 z] with ω hω u v
  have key : (D (h ω)).1 ((r : ℝ) • u + z, (r : ℝ) • v + z) =
      (D (LQGMetric.addConst (LQGMetric.affineComp (r : ℝ) z (h ω))
        (Q' * Real.log (r : ℝ)))).1 (u, v) := by
    simpa only [Complex.real_smul] using hω u v
  exact (LQGMetric.ContMetric.edist_pt (D (h ω)) ((r : ℝ) • u + z) ((r : ℝ) • v + z)).trans
    ((congrArg ENNReal.ofReal key).trans
      (LQGMetric.ContMetric.edist_pt _ u v).symm)

end LatticeProb.LQG
