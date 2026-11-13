import Mathlib
import LatticeProb.Prob.StoppedPathCoupling

/-!
# Continuity and measurability of stopped paths

For a metric space `E`, the map `(f, τ) ↦ f (· ∧ τ)` sending a continuous path `f : ℝ≥0 → E` and a
stopping time `τ ∈ ℝ≥0` to the stopped path is continuous for the compact-open topology on
`C(ℝ≥0, E)` (`continuous_stopPath_uncurry`).  Consequently, if the path space is second countable
with its Borel `σ`-algebra, a random path `F` and a random time `τ` that are measurable give a
measurable stopped path `ω ↦ stopPath (F ω) (τ ω)` (`measurable_stopPath`).  This supplies the
measurability hypotheses of `levyProkhorovEDist_stopPath_le`.
-/

open MeasureTheory

open scoped NNReal

noncomputable section

namespace LatticeProb

variable {E : Type*} [MetricSpace E]

/-- The map `τ ↦ (t ↦ t ∧ τ)` into the continuous self-maps of `ℝ≥0` is continuous. -/
theorem continuous_minCM : Continuous fun τ : ℝ≥0 =>
    (⟨fun t => min t τ, continuous_id.min continuous_const⟩ : C(ℝ≥0, ℝ≥0)) :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_snd.min continuous_fst)

/-- The stopped path `(f, τ) ↦ f (· ∧ τ)` is jointly continuous for the compact-open topology. -/
theorem continuous_stopPath_uncurry :
    Continuous fun p : C(ℝ≥0, E) × ℝ≥0 => stopPath p.1 p.2 :=
  ContinuousMap.continuous_comp'.comp
    ((continuous_minCM.comp continuous_snd).prodMk continuous_fst)

/-- A random path and a random time that are measurable give a measurable stopped path. -/
theorem measurable_stopPath {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace C(ℝ≥0, E)]
    [BorelSpace C(ℝ≥0, E)] [SecondCountableTopology C(ℝ≥0, E)]
    {F : Ω → C(ℝ≥0, E)} {τ : Ω → ℝ≥0} (hF : Measurable F) (hτ : Measurable τ) :
    Measurable fun ω => stopPath (F ω) (τ ω) :=
  continuous_stopPath_uncurry.measurable.comp (hF.prodMk hτ)

end LatticeProb
