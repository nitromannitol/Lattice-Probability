import Mathlib
import LatticeProb.Prob.UpcrossReversalDuality
import LatticeProb.Prob.UpcrossReversalPathwise

/-!
# Lebesgue-start duality for the first up-crossing piece

For a Brownian motion `B` with continuous paths, a drift `m`, a level `c > 0` and a time `t`,
the integral over a Lebesgue starting point `x` and over `ω` of
`f(first up-crossing piece) · 1{d₁ ≤ t < d₂}` evaluated on `s ↦ x + B s ω + m s`
equals the same integral for the reversed piece `f ∘ upcrossRev c`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Lebesgue-start duality for the first up-crossing piece.** -/
theorem lintegral_lebesgue_upcrossOnce_rev (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (m : ℝ) {c : ℝ}
    (hc : 0 < c) (t : ℝ≥0) {f : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hf : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) :
    ∫⁻ x : ℝ, ∫⁻ ω, upcrossOnce c t f (fun s => x + B s ω + m * (s : ℝ)) ∂P
      = ∫⁻ x : ℝ, ∫⁻ ω, upcrossOnce c t (fun p => f (upcrossRev c p))
          (fun s => x + B s ω + m * (s : ℝ)) ∂P := by
  have key := lintegral_lebesgue_drift_rev_path hB hm hcont m c t
    (measurable_upcrossOnce hc t hf)
  have hcx : ∀ x ω, Continuous fun s : ℝ≥0 => x + B s ω + m * (s : ℝ) := fun x ω =>
    (affinePath x m (pathMap B hcont ω)).continuous
  have e1 : ∀ x ω, upcrossOnce c t f
      ((stopAt (t : ℝ≥0∞) (affinePath x m (pathMap B hcont ω)) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) =
      upcrossOnce c t f (fun s => x + B s ω + m * (s : ℝ)) := fun x ω => by
    have : ((stopAt (t : ℝ≥0∞) (affinePath x m (pathMap B hcont ω)) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) =
        fun s => (fun s => x + B s ω + m * (s : ℝ)) (min s t) := by
      funext s
      simp only [stopAt_coe, affinePath_apply, pathMap_apply]
    rw [this]
    exact upcrossOnce_stop (hcx x ω) hc t f
  have e2 : ∀ x ω, upcrossOnce c t f
      ((revStopC c t (affinePath x m (pathMap B hcont ω)) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) =
      upcrossOnce c t (fun p => f (upcrossRev c p)) (fun s => x + B s ω + m * (s : ℝ)) :=
    fun x ω => upcrossOnce_revStop (hcx x ω) hc t f
  simp only [e1, e2] at key
  exact key

end LatticeProb
