import LatticeProb.Analysis.LocalMinCountable
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianG0

/-!
# Local minima of correlated Brownian coordinates

For a two-sided correlated Brownian pair, both sets of coordinate local-minimum
times are almost surely countable.
-/

set_option autoImplicit false

open MeasureTheory Filter Set

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- Almost surely, each coordinate has only countably many local-minimum times. -/
theorem ae_countable_coordinate_localMin {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ i : Fin 2, {t | IsLocalMin (lrCoord i · ω) t}.Countable := by
  filter_upwards [ae_locMinDistinct hμ] with ω hω
  intro i
  exact countable_localMin_of_distinct_values (lrCoord i · ω) (hω i)

/-- Almost surely, the local-minimum times of either coordinate form a countable set. -/
theorem ae_countable_union_coordinate_localMin {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ({t | IsLocalMin (lrCoord 0 · ω) t} ∪
      {t | IsLocalMin (lrCoord 1 · ω) t}).Countable := by
  filter_upwards [ae_countable_coordinate_localMin hμ] with ω hω
  exact (hω 0).union (hω 1)

end LatticeProb.CorrelatedBM
