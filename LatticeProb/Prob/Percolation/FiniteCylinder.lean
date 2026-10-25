import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Data.ENNReal.BigOperators

/-!
# Finite patterns in a Bernoulli product

A finite pattern prescribes every coordinate in its finite index set. Its probability under
independent Bernoulli coordinates is the product of the prescribed one-coordinate masses.
The uniform lower bound is the cardinality power of the smaller of the two Bernoulli masses.
The coordinate type is arbitrary; countability is unnecessary for these finite events.
-/

namespace LatticeProb.Prob.Percolation.FiniteCylinder

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {ι : Type*}

/-- Prescribing every coordinate in a finite set is a measurable event. -/
theorem measurableSet_pattern (F : Finset ι) (ξ : ι → Bool) :
    MeasurableSet {ω : ι → Bool | ∀ i ∈ F, ω i = ξ i} := by
  have hset : {ω : ι → Bool | ∀ i ∈ F, ω i = ξ i} =
      Set.pi (F : Set ι) (fun i => {ξ i}) := rfl
  rw [hset]
  exact MeasurableSet.pi F.countable_toSet (fun _ _ => measurableSet_singleton _)

/-- A finite Bernoulli pattern has the product of its true and false masses. -/
theorem measure_pattern (p : unitInterval) (F : Finset ι) (ξ : ι → Bool) :
    (Measure.infinitePi (fun _ : ι => bernoulliMeasure true false p))
      {ω | ∀ i ∈ F, ω i = ξ i} =
      ∏ i ∈ F, ENNReal.ofReal (if ξ i then (p : ℝ) else 1 - (p : ℝ)) := by
  classical
  change (Measure.infinitePi (fun _ : ι => bernoulliMeasure true false p))
    (Set.pi (F : Set ι) (fun i => {ξ i})) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  apply Finset.prod_congr rfl
  intro i _
  cases ξ i <;>
    simp [bernoulliMeasure_apply p (measurableSet_singleton _),
      ENNReal.ofReal, unitInterval.toNNReal, unitInterval.coe_symm_eq]
  all_goals
    apply NNReal.eq
    simp only [Real.coe_toNNReal']
    first
    | rw [max_eq_left p.property.1]
    | rw [max_eq_left (sub_nonneg.mpr p.property.2)]
    rfl

/-- Every finite pattern has probability at least the power of the smaller mass. -/
theorem pow_min_le_measure_pattern (p : unitInterval) (F : Finset ι) (ξ : ι → Bool) :
    ENNReal.ofReal (min (p : ℝ) (1 - (p : ℝ))) ^ F.card ≤
      (Measure.infinitePi (fun _ : ι => bernoulliMeasure true false p))
        {ω | ∀ i ∈ F, ω i = ξ i} := by
  rw [measure_pattern, ← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro i _
  apply ENNReal.ofReal_le_ofReal
  cases ξ i
  · exact min_le_right _ _
  · exact min_le_left _ _

/-- When both Bernoulli masses are positive, every finite pattern has positive probability. -/
theorem measure_pattern_pos (p : unitInterval) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (F : Finset ι) (ξ : ι → Bool) :
    0 < (Measure.infinitePi (fun _ : ι => bernoulliMeasure true false p))
      {ω | ∀ i ∈ F, ω i = ξ i} := by
  have hmin : 0 < ENNReal.ofReal (min (p : ℝ) (1 - (p : ℝ))) :=
    ENNReal.ofReal_pos.mpr (lt_min hp0 (sub_pos.mpr hp1))
  exact (ENNReal.pow_pos hmin F.card).trans_le (pow_min_le_measure_pattern p F ξ)

/-- Independence and the specified Bernoulli marginals give the exact finite pattern law. -/
theorem independent_measure_pattern (P : Measure (ι → Bool)) [IsProbabilityMeasure P]
    (p : unitInterval) (hInd : iIndepFun (fun i (ω : ι → Bool) => ω i) P)
    (hMarg : ∀ i, P.map (fun ω => ω i) = bernoulliMeasure true false p)
    (F : Finset ι) (ξ : ι → Bool) :
    P {ω | ∀ i ∈ F, ω i = ξ i} =
      ∏ i ∈ F, ENNReal.ofReal (if ξ i then (p : ℝ) else 1 - (p : ℝ)) := by
  have h := hInd.map_fun_eq_infinitePi_map (fun i => measurable_pi_apply i)
  change P.map id = Measure.infinitePi (fun i => P.map (fun ω => ω i)) at h
  rw [Measure.map_id] at h
  rw [h]
  simp_rw [hMarg]
  exact measure_pattern p F ξ

/-- The lower bound is consumed directly by any independent law with Bernoulli marginals. -/
theorem pow_min_le_independent_measure_pattern (P : Measure (ι → Bool))
    [IsProbabilityMeasure P] (p : unitInterval)
    (hInd : iIndepFun (fun i (ω : ι → Bool) => ω i) P)
    (hMarg : ∀ i, P.map (fun ω => ω i) = bernoulliMeasure true false p)
    (F : Finset ι) (ξ : ι → Bool) :
    ENNReal.ofReal (min (p : ℝ) (1 - (p : ℝ))) ^ F.card ≤
      P {ω | ∀ i ∈ F, ω i = ξ i} := by
  rw [independent_measure_pattern P p hInd hMarg, ← measure_pattern p F ξ]
  exact pow_min_le_measure_pattern p F ξ

end LatticeProb.Prob.Percolation.FiniteCylinder
