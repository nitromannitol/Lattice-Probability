import Mathlib
import LatticeProb.Prob.UpcrossLaplaceIdentity

/-!
# Law of the first up-crossing piece is invariant under time reversal

For Brownian motion with continuous paths and positive drift `mu`, with law `μ₀` on path space,
the push-forward of `μ₀` under `w ↦ firstUpcrossPiece c w` (a path from `0` to `c`) coincides with
the push-forward under `w ↦ upcrossRev c (firstUpcrossPiece c w)` (the same piece read backwards
from the level `c`).  This is the measure-theoretic form of `lintegral_piece_eq_rev_driftLaw`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The law of the first up-crossing piece is invariant under reversal**, for Brownian motion with
positive drift: a measure equality on `ℝ≥0 → ℝ` with the product σ-algebra. -/
theorem map_upcrossRev_firstUpcrossPiece_driftLaw [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu) {c : ℝ} (hc : 0 < c) :
    (driftLaw P B hcont mu).map
        (fun v : C(ℝ≥0, ℝ) => upcrossRev c (firstUpcrossPiece c (v : ℝ≥0 → ℝ)))
      = (driftLaw P B hcont mu).map
        (fun v : C(ℝ≥0, ℝ) => firstUpcrossPiece c (v : ℝ≥0 → ℝ)) := by
  have hpiece : Measurable fun v : C(ℝ≥0, ℝ) => firstUpcrossPiece c (v : ℝ≥0 → ℝ) :=
    measurable_firstUpcrossPiece c
  have hrev : Measurable fun v : C(ℝ≥0, ℝ) => upcrossRev c (firstUpcrossPiece c (v : ℝ≥0 → ℝ)) :=
    measurable_upcrossRev_firstUpcrossPiece hc
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hrev hs, Measure.map_apply hpiece hs]
  have hind : ∀ {g : C(ℝ≥0, ℝ) → ℝ≥0 → ℝ} (_ : Measurable g),
      ∫⁻ v, s.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞) (g v) ∂(driftLaw P B hcont mu)
        = driftLaw P B hcont mu (g ⁻¹' s) := by
    intro g hg
    have : (fun v => s.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞) (g v))
        = (g ⁻¹' s).indicator 1 := by
      funext v
      by_cases h : g v ∈ s <;> simp [Set.indicator, h]
    rw [this, lintegral_indicator_one (hg hs)]
  have key := lintegral_piece_eq_rev_driftLaw hB hm hcont hmu hc
    (f := s.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞))
    ((measurable_one.indicator hs).comp hpiece) ((measurable_one.indicator hs).comp hrev)
    (fun p => Set.indicator_le_self' (fun _ _ => zero_le) p |>.trans le_rfl)
  rw [hind hpiece, hind hrev] at key
  exact key.symm

end LatticeProb
