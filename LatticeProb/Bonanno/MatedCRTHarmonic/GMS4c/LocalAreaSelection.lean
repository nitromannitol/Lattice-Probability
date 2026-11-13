/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalAreaSelection at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaMeasurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.MeasurabilityAE

/-!
# A Borel version of a local dyadic GMC limit

This is the measure-theoretic selection step. The domain law supplies the
almost-sure vague convergence and local integrability of the approximations;
The selected map is Borel on the entire space of restricted fields.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric QuantumZipper
attribute [local instance] Classical.propDecidable

/-- A local dyadic sample on which the vague limit exists, is finite on `V`,
and continuous compactly supported tests are integrable at all sufficiently
fine scales. Vague convergence is unchanged by finitely many coarse scales. -/
def LocalDyadicGood (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (T : DistOn (thickOpen V δ)) : Prop :=
  (∃ μ : Measure ℂ, IsVagueLimitOn V (localAreaApproxDy γ V δ T) μ ∧ μ V < ⊤) ∧
    ∀ (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
      tsupport f ⊆ V → ∀ᶠ k : ℕ in atTop,
        Integrable f (localAreaApproxDy γ V δ T k)

/-- The selected vague limit, with zero junk off the existence locus. -/
def localAreaVagueSelection (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (T : DistOn (thickOpen V δ)) : Measure ℂ :=
  if h : ∃ μ : Measure ℂ,
      IsVagueLimitOn V (localAreaApproxDy γ V δ T) μ ∧ μ V < ⊤
  then h.choose else 0

theorem localAreaVagueSelection_spec {γ : ℝ} {V : TopologicalSpace.Opens ℂ}
    {δ : ℝ} {T : DistOn (thickOpen V δ)}
    (h : LocalDyadicGood γ V δ T) :
    IsVagueLimitOn V (localAreaApproxDy γ V δ T)
      (localAreaVagueSelection γ V δ T) ∧
    (localAreaVagueSelection γ V δ T) V < ⊤ := by
  simpa [localAreaVagueSelection, h.1] using
    (Classical.choose_spec h.1)

end MatedCRTHarmonic.GMS4c

