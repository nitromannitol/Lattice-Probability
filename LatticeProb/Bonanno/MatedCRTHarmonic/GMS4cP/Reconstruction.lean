/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.Reconstruction at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.SampleBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.PrimeTransfer

/-!
# Measurable Lemma 4.3 from a configuration reconstruction

Source: [18] Lemma 4.3.

If one Borel map `R₀` of the observation `(h|_V, h^IG|_V, U)` reproduces, almost surely under each of two
laws, the actual local configuration `(μ|_U, h|_U, η_L` excursions into `U)` of an excursion-regular Lebesgue
curve `η_L` whose quantum-time reparametrization `c = η_L ∘ φ` is parametrized by `μ`, then the escape event and
The all-visit inner-degree event on its complement are the preimages of two fixed Borel sets
(`l43pSegments U ⁻¹' locEsc …`, `… locInner …`) under `R₀` for both laws: this is `L43PLocalReconstruction`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4c MatedCRTHarmonic.MatedCRT

/-- The almost-sure model facts used at one sample: the reconstruction returns the actual configuration
of an excursion-regular Lebesgue curve, whose quantum-time reparametrization is the given curve. -/
def L43PSampleModel {V U : TopologicalSpace.Opens ℂ}
    (R₀ : L46TLocalFieldPhase V → LocalConfiguration U)
    (obs : L46TLocalFieldPhase V) (c : ℝ → ℂ) : Prop :=
  ∃ (μ : Measure ℂ) (h : LQGMetric.DistC) (ηL : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ),
    R₀ obs = localConfiguration U μ h ηL ∧ μ U < ⊤ ∧ ExcursionRegular U ηL ∧
    (∀ t, c t = ηL (φ t)) ∧ ∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s)

end MatedCRTHarmonic.GMS4cP
