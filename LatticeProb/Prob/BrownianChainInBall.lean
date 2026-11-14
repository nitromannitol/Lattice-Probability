import LatticeProb.Prob.BrownianStayScaled
import LatticeProb.Prob.StepTimeChain

/-!
# Long separated chains inside a ball have superpolynomially small probability

For a Brownian motion `B` on `ℝ ^ d` started at `0`, the probability that there is a nondecreasing chain
of times `τ_0 ≤ ⋯ ≤ τ_K`, with `B` inside the ball of radius `a` up to time `τ_K` and moving by at least
`2 a r` between consecutive chain times, is at most `C r ^ p` for `K = ⌊r ^ -(2 + ζ)⌋`.  The constant does
not depend on `a`, nor on the chain.  This is the tightness of the number of exits of the smaller regions
of a partition of mesh `a r` that a Brownian motion performs before leaving the ball of radius `a`:
it follows from the staying estimate up to the `K`-th displacement time (`measure_stays_in_ball_superpoly_scaled`) and
the domination of separated chains by displacement times (`stepTime_le_of_separated_chain`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

universe u

namespace LatticeProb

/-- **Tightness of the number of steps.** For a Brownian motion `B` on `ℝ ^ d` started at `0`,
`0 < ζ < 1` and `p ∈ ℕ`, there is `C` such that for all `a > 0` and `0 < r < 1`, the probability that
some nondecreasing chain `τ` of times with `2 a r ≤ ‖B (τ (n+1)) - B (τ n)‖` for the first `K` steps,
`K = ⌊r ^ -(2 + ζ)⌋`, has `‖B t‖ < a` for all `t ≤ τ K` is at most `C r ^ p`. -/
theorem measure_separated_chain_in_ball_superpoly_scaled (d : ℕ) (hd : 0 < d) {ζ : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)), IsBrownianSpace d 0 B P →
      ∀ a : ℝ≥0, 0 < a → ∀ r : ℝ≥0, 0 < r → r < 1 →
      P {ω | ∃ τ : ℕ → ℝ≥0, Monotone τ ∧
            (∀ n < ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊, 2 * ((a : ℝ) * r) ≤ ‖B (τ (n + 1)) ω - B (τ n) ω‖) ∧
            ∀ t ≤ τ ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊, ‖B t ω‖ < a}
        ≤ ENNReal.ofReal (C * (r : ℝ) ^ p) := by
  obtain ⟨C, hC⟩ := measure_stays_in_ball_superpoly_scaled.{u} d hd hζ0 hζ1 p
  refine ⟨C, fun Ω _ P _ B hB a ha r hr0 hr1 => ?_⟩
  refine le_trans (measure_mono ?_) (hC Ω P B hB a ha r hr0 hr1)
  rintro ω ⟨τ, hτ, hsep, hin⟩ t ht
  have h1 := stepTime_le_of_separated_chain_of_le (f := fun s => B s ω) hτ hsep le_rfl
  exact hin t (ENNReal.coe_le_coe.1 (lt_of_lt_of_le ht h1).le)

end LatticeProb
