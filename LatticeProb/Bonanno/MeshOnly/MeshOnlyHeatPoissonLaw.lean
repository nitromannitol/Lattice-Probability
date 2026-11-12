/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyHeatPoissonLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatUniformization
import Mathlib.Probability.Distributions.Poisson.Basic

/-! The finite-time volume-clock law is the actual absorbed lazy chain at an
independent Poisson count. This construction does not use a heat estimate. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal

set_option backward.isDefEq.respectTransparency false

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] (N : FiniteConductanceNetwork V)

/-- Absorbed uniformized chain at an independent Poisson count of mean `λt`.
This is a probability measure on all ambient vertices; restricting to `S`
gives the killed subprobability law. -/
noncomputable def poissonizedUniformizedLaw (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) (x : V) (t : ℝ≥0) : Measure V := by
  let r : ℝ≥0 := ⟨(t : ℝ) * N.uniformizationRate m,
    mul_nonneg t.coe_nonneg (N.uniformizationRate_pos m hm).le⟩
  letI : IsProbabilityMeasure (poissonMeasure r) :=
    (hasSum_one_poissonMeasure r).isProbabilityMeasure_sum_dirac (fun _ => by positivity)
  exact (((poissonMeasure r).toPMF).bind
    (fun n => N.uniformizedNStepPMF m hm S n x)).toMeasure

instance poissonizedUniformizedLaw_isProbability (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) (x : V) (t : ℝ≥0) :
    IsProbabilityMeasure (N.poissonizedUniformizedLaw m hm S x t) := by
  unfold poissonizedUniformizedLaw
  infer_instance

end BouRabeeGwynne.FiniteConductanceNetwork
