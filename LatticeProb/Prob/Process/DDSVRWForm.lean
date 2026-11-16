import LatticeProb.Prob.Process.DDSDiscrete

/-!
# The Dambis–Dubins–Schwarz characteristic-function bound in terminal-value form

The proposition `LatticeProb.Process.DambisDubinsSchwarz` states the characteristic-function bound
that follows from the Dambis–Dubins–Schwarz theorem and Itô's formula for `e^{iB_t}`. For a real
continuous martingale `M` from zero with quadratic covariation `Q` at a deterministic time `T`
(`HasQuadCovar`) and every `q ≥ 0`,
`|E e^{i M_T} - e^{-q/2}| ≤ ½ E |Q - q|`, the right side taking values in `[0, ∞]`.

The theorem `dambisDubinsSchwarz_form` proves the proposition from the stopped dyadic skeleton of
the module `LatticeProb.Prob.Process.DDSPassage` and the discrete bound of the module
`LatticeProb.Prob.Process.DDSDiscrete`.
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

namespace LatticeProb.Process

/-- The characteristic-function bound for continuous martingales: for a continuous martingale `M`
started at zero with terminal bracket `Q = ⟨M⟩_T` and a constant `q ≥ 0`,
`|E e^{iM_T} - e^{-q/2}| ≤ ½ E|Q - q|`, the right side in `[0, ∞]`. -/
def DambisDubinsSchwarz : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0)
    (Q : Ω → Fin 1 → Fin 1 → ℝ),
    Martingale M ℱ P → (∀ ω, Continuous fun t => M t ω) → (∀ ω, M 0 ω = 0) →
    HasQuadCovar P M T Q → ∀ q : ℝ, 0 ≤ q →
      ENNReal.ofReal ‖∫ ω, Complex.exp (Complex.I * ((M T ω 0 : ℝ) : ℂ)) ∂P -
          Complex.exp ((-(q / 2) : ℝ) : ℂ)‖ ≤
        2⁻¹ * ∫⁻ ω, ENNReal.ofReal |Q ω 0 0 - q| ∂P

/-- The characteristic-function bound holds for continuous martingales. -/
theorem dambisDubinsSchwarz_form : DambisDubinsSchwarz :=
  BdgUpperContinuous.DdsPassage.dambisDubinsSchwarz_of_skeleton_exact
    BdgUpperContinuous.stoppedDyadicSkeletonExact_holds
    BdgUpperContinuous.DdsDiscrete.discreteCFBound_holds

end LatticeProb.Process
