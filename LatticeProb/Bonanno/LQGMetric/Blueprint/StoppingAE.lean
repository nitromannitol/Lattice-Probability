/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.StoppingAE at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-!
# Almost sure stopping times for the filled-ball filtration (D120)

Decision D120 (decisions/DEC-120.md §3.2): the radii `σ^ε_{τ,𝕣}` of CONF (3.17) are stopping
times for the filled-ball filtration only almost surely (CONF l. 1302, GM l. 2189: Axiom II holds
only a.s.), so CONF L3.6/L3.7 take an almost sure stopping-time hypothesis. The definition is kept
in this separate Blueprint file (instead of right after `IsFilledBallStoppingTime` in M2Defs) so
that adding it does not rebuild the modules importing M2Defs; the content is DEC-120 §3.2 verbatim.
-/

set_option autoImplicit false

namespace LQGMetric.Blueprint

section Sigma
variable {Ω : Type} [MeasurableSpace Ω]

/-- `τ` is an **almost sure** stopping time for the filled-ball filtration (D120): for every `t`,
`{τ < t}` is a.s. equal to an event of `𝓕_t` (`AEEventIn`, D30). This is the form in which the
radii `σ^ε_{τ,𝕣}` of CONF (3.17) are stopping times (CONF l. 1302, GM l. 2189): Axiom II holds
only a.s. -/
def IsFilledBallStoppingTimeAE (P : MeasureTheory.Measure Ω) (D : DistC → ContMetric)
    (h : Ω → DistC) (z : ℂ) (τ : Ω → ℝ) : Prop :=
  ∀ t : ℝ, AEEventIn P (filledBallSigma D h z t) {ω | τ ω < t}

theorem IsFilledBallStoppingTime.ae {D : DistC → ContMetric} {h : Ω → DistC} {z : ℂ}
    {τ : Ω → ℝ} (hτ : IsFilledBallStoppingTime D h z τ) (P : MeasureTheory.Measure Ω) :
    IsFilledBallStoppingTimeAE P D h z τ :=
  fun t => ⟨_, hτ t, Filter.EventuallyEq.rfl⟩

end Sigma

end LQGMetric.Blueprint
