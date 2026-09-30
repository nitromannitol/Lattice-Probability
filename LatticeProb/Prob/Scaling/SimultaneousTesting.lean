/- A common probability-one event for a continuous family of test identities.

Moved from Parking-Sharpness.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Bases

open MeasureTheory TopologicalSpace
namespace LatticeProb.Scaling.SimultaneousTesting

/-- Continuous identities indexed by a separable space hold simultaneously almost surely.
The qualifying event may depend on the sample but is fixed across the test family. -/
theorem ae_forall_eq_of_continuous
    {Ω T E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [TopologicalSpace T] [SeparableSpace T] [TopologicalSpace E] [T2Space E]
    {f g : Ω → T → E} {A : Ω → Prop}
    (hf : ∀ᵐ ω ∂μ, A ω → Continuous (f ω))
    (hg : ∀ᵐ ω ∂μ, A ω → Continuous (g ω))
    (heq : ∀ t, ∀ᵐ ω ∂μ, A ω → f ω t = g ω t) :
    ∀ᵐ ω ∂μ, A ω → ∀ t, f ω t = g ω t := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense T
  have hD : ∀ᵐ ω ∂μ, ∀ t ∈ D, A ω → f ω t = g ω t :=
    (ae_ball_iff hDc).mpr fun t _ => heq t
  filter_upwards [hf, hg, hD] with ω hf hg hD hA
  intro t
  exact closure_minimal (fun t ht => hD t ht hA)
    (isClosed_eq (hf hA) (hg hA)) (hDd t)

end LatticeProb.Scaling.SimultaneousTesting
