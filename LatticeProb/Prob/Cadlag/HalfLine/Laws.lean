import LatticeProb.Prob.Cadlag.HalfLine.Evaluation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.ConditionalLExpectation

/-!
# Laws of half-line càdlàg processes

Finite-dimensional laws of a law on `D E`, the raw natural σ-algebra of a `D E`-valued process,
truncated increment powers, and two worked examples (a Dirac law at a constant path and a
constant process on a one-point space), as used by the Ethier–Kurtz statements.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal

noncomputable section

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The joint law of the evaluations at finitely many times. -/
def jointLaw (mu : ProbabilityMeasure (D E)) {k : ℕ} (ts : Fin k → Time) :
    ProbabilityMeasure (Fin k → E) :=
  mu.map (measurable_pi_lambda _ (fun i => measurable_eval (ts i))).aemeasurable

/-- The Dirac law at a genuine constant path. -/
def constantLaw (a : E) : ProbabilityMeasure (D E) :=
  ⟨Measure.dirac (const a), Measure.dirac.isProbabilityMeasure⟩

/-- Raw natural information through deterministic time `t`. -/
abbrev naturalSigma {Ω : Type*} (Y : Ω → D E) (t : Time) : MeasurableSpace Ω :=
  ⨆ s ≤ t, MeasurableSpace.comap (fun w => (Y w).1 s) inferInstance

omit [BorelSpace E] in
/-- Measurable evaluations ensure that natural information is a sub-σ-algebra. -/
theorem naturalSigma_le {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → D E)
    (hY : ∀ t, Measurable (fun w => (Y w).1 t)) (t : Time) :
    naturalSigma Y t ≤ ‹MeasurableSpace Ω› := by
  exact iSup_le fun s => iSup_le fun _ => (hY s).comap_le

/-- A nonnegative truncated increment power. -/
def incrementPower {Ω : Type*} (Y : Ω → D E) (beta : ℝ) (s t : Time)
    (w : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal ((min (dist ((Y w).1 s) ((Y w).1 t)) 1) ^ beta)

/-- A genuine one-point probability space. -/
def unitLaw : ProbabilityMeasure Unit :=
  ⟨Measure.dirac (), Measure.dirac.isProbabilityMeasure⟩

/-- The path law of a constant process on the one-point space. -/
def constantProcessLaw (a : E) : ProbabilityMeasure (D E) :=
  unitLaw.map (measurable_const : Measurable (fun _ : Unit => const a)).aemeasurable

end

end LatticeProb.Cadlag.HalfLine
