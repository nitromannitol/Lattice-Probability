/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.OInterfaces at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.Rotation

/-!
# Circle-average covariance inputs for the curve-law invariances

For a whole-plane GFF `h` (LQGMetric's `IsWholePlaneGFF`, any additive constant), we use the
**rotation covariance of circle averages at a fixed circle**: for every angle `θ`, radius `ρ > 0` and centre
`w`, almost surely

`circleAvg (rotateField θ (h ω)) ρ w = circleAvg (h ω) ρ (e^{iθ} w)`,

where `MoTPort.rotateField θ h = h(e^{iθ} ·)`. Only this fixed-circle form is used: the curve-law
arguments compare laws of circle-average *processes* on the product σ-algebra, where coordinatewise almost
sure equality suffices (`IGLaw.map_eq_of_forall_ae_eq` in `OProcLaw`).

The simultaneous (process-level) form `RotCircleAvgCovarianceAll` — one null set for all `ρ > 0` and
all `w` — is proved in `IGLaw/CircleAvgCovariance.lean`; it implies the fixed form
(`rotCircleAvgCovariance_of_all`).
This file only names the statements; nothing here is assumed by a frozen theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace MatedCRTHarmonic.IGLaw

open LQGMetric

/-- **Rotation covariance of circle averages at one fixed circle**. For every
whole-plane GFF `h` on a probability space, angle `θ`, radius `ρ > 0` and centre `w`, a.s.
`(h(e^{iθ}·))_ρ(w) = h_ρ(e^{iθ} w)`. This follows from `IGLaw/CircleAvgCovariance.lean` via
`rotCircleAvgCovariance_of_all`. -/
def RotCircleAvgCovariance : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC), IsWholePlaneGFF h P →
    ∀ (θ ρ : ℝ), 0 < ρ → ∀ w : ℂ,
      ∀ᵐ ω ∂P, circleAvg (MatedCRTHarmonic.MoTPort.rotateField θ (h ω)) ρ w =
        circleAvg (h ω) ρ (Complex.exp (θ * Complex.I) * w)

/-- **Process-level rotation covariance of circle averages** : one null set for all
radii `ρ > 0` and all centres `w`. -/
def RotCircleAvgCovarianceAll : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC), IsWholePlaneGFF h P →
    ∀ θ : ℝ, ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      circleAvg (MatedCRTHarmonic.MoTPort.rotateField θ (h ω)) ρ w =
        circleAvg (h ω) ρ (Complex.exp (θ * Complex.I) * w)

/-- The process-level form implies the fixed-circle form used here. -/
theorem rotCircleAvgCovariance_of_all (hall : RotCircleAvgCovarianceAll) :
    RotCircleAvgCovariance := by
  intro Ω _ P h hh θ ρ hρ w
  filter_upwards [hall P h hh θ] with ω hω
  exact hω ρ hρ w

end MatedCRTHarmonic.IGLaw
