import LatticeProb.Prob.Percolation.LatticeBondGraph
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Canonical Bernoulli bond law

The probability law is the product of Bernoulli measures on the genuine unordered lattice
bonds. Evaluation at any bond has the prescribed Bernoulli law, and all evaluations are
independent. At parameter one this law is the point mass at the fully open configuration.
-/

namespace LatticeProb.Percolation

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-- The canonical product Bernoulli law on genuine nearest-neighbor bonds. -/
noncomputable def latticeBondLaw (d : ℕ) (p : unitInterval) : Measure (Configuration d) :=
  Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true false p)

/-- The canonical bond law has total mass one, including in dimension zero. -/
instance latticeBondLaw_isProbabilityMeasure (d : ℕ) (p : unitInterval) :
    IsProbabilityMeasure (latticeBondLaw d p) := by
  unfold latticeBondLaw
  infer_instance

/-- Every actual bond evaluation has precisely its Bernoulli marginal. -/
theorem latticeBondLaw_map_eval (p : unitInterval) (e : Bond d) :
    (latticeBondLaw d p).map (fun ω => ω e) = bernoulliMeasure true false p :=
  Measure.infinitePi_map_eval _ e

/-- All actual bond evaluations are independent under the canonical law. -/
theorem latticeBondLaw_iIndepFun (p : unitInterval) :
    iIndepFun (fun e (ω : Configuration d) => ω e) (latticeBondLaw d p) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

/-- A prescribed bond is open with probability exactly the parameter. -/
theorem latticeBondLaw_open (p : unitInterval) (e : Bond d) :
    (latticeBondLaw d p) {ω | ω e = true} = ENNReal.ofReal (p : ℝ) := by
  have h := congrArg (fun μ : Measure Bool => μ {true}) (latticeBondLaw_map_eval p e)
  rw [Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton true)] at h
  change (latticeBondLaw d p) {ω | ω e = true} = _ at h
  rw [h]
  simp only [bernoulliMeasure_apply p (measurableSet_singleton true),
    Set.mem_singleton_iff, Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply NNReal.eq
  exact (max_eq_left p.property.1).symm

/-- At parameter one the product law is concentrated at the actual fully open configuration. -/
theorem latticeBondLaw_one (d : ℕ) : latticeBondLaw d 1 = Measure.dirac (allOpen d) := by
  simp only [latticeBondLaw, bernoulliMeasure_one, Measure.infinitePi_dirac]
  rfl

end LatticeProb.Percolation
