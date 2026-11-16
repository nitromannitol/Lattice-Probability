import LatticeProb.Prob.Process.BDGSquare

/-!
# The Burkholder–Davis–Gundy inequality for continuous martingales in terminal-value form

The proposition `LatticeProb.Process.BurkholderDavisGundy` states the Burkholder–Davis–Gundy
inequality with Doob's `Lᵖ` inequality for continuous martingales in terminal-value form. For
`p > 1` there are `0 < c` and `C` such that, for every real continuous martingale `M` from zero with
quadratic covariation `Q` at a deterministic time `T` (`HasQuadCovar`),
`c E Q^{p/2} ≤ E |M_T|^p ≤ C E Q^{p/2}`.

The theorem `burkholderDavisGundy_form` proves the proposition from the Burkholder–Davis–Gundy
theorem of the module `LatticeProb.Prob.Process.BDGSquare`.
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

namespace LatticeProb.Process

/-- Burkholder–Davis–Gundy with Doob's `Lᵖ` inequality for continuous martingales, terminal-value
form. -/
def BurkholderDavisGundy : Prop :=
  ∀ p : ℝ, 1 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0)
      (Q : Ω → Fin 1 → Fin 1 → ℝ),
      Martingale M ℱ P → (∀ ω, Continuous fun t => M t ω) → (∀ ω, M 0 ω = 0) →
      HasQuadCovar P M T Q →
        ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P ≤
            ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P ∧
          ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P ≤ ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P

/-- The Burkholder–Davis–Gundy inequality holds for continuous martingales. -/
theorem burkholderDavisGundy_form : BurkholderDavisGundy :=
  BdgUpperContinuous.burkholderDavisGundy_holds

end LatticeProb.Process
