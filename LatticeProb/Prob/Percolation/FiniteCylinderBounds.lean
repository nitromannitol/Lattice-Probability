import LatticeProb.Prob.Percolation.FiniteCylinder
import Mathlib.Probability.ConditionalProbability

/-!
# Bounds consumed by finite-pattern conditioning

These are quantitative consequences of the full finite-pattern law. They apply to any
independent coordinate law with the stated Bernoulli marginals. A conditional-success
bound is an explicit hypothesis of the generic multiplication lemma; constructing a
successful pattern is a separate application.
-/

namespace LatticeProb.Prob.Percolation.FiniteCylinderBounds

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LatticeProb.Prob.Percolation.FiniteCylinder

variable {ι : Type*}

/-- The real-valued probability of any finite pattern is at least the smaller-mass power. -/
theorem pow_min_le_real_independent_measure_pattern (P : Measure (ι → Bool))
    [IsProbabilityMeasure P] (p : unitInterval)
    (hInd : iIndepFun (fun i (ω : ι → Bool) => ω i) P)
    (hMarg : ∀ i, P.map (fun ω => ω i) = bernoulliMeasure true false p)
    (F : Finset ι) (ξ : ι → Bool) :
    min (p : ℝ) (1 - (p : ℝ)) ^ F.card ≤ (P {ω | ∀ i ∈ F, ω i = ξ i}).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P _)).mp
  rw [ENNReal.ofReal_pow (le_min p.property.1 (sub_nonneg.mpr p.property.2))]
  exact pow_min_le_independent_measure_pattern P p hInd hMarg F ξ

/-- Every finite pattern of a nondegenerate independent Bernoulli law has positive mass. -/
theorem independent_measure_pattern_pos (P : Measure (ι → Bool))
    [IsProbabilityMeasure P] (p : unitInterval) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hInd : iIndepFun (fun i (ω : ι → Bool) => ω i) P)
    (hMarg : ∀ i, P.map (fun ω => ω i) = bernoulliMeasure true false p)
    (F : Finset ι) (ξ : ι → Bool) : 0 < P {ω | ∀ i ∈ F, ω i = ξ i} := by
  rw [independent_measure_pattern P p hInd hMarg, ← measure_pattern p F ξ]
  exact measure_pattern_pos p hp0 hp1 F ξ

/-- A conditional-success bound on a full finite pattern gives an unconditional bound. -/
theorem conditional_pattern_lower_bound (P : Measure (ι → Bool))
    [IsProbabilityMeasure P] (p : unitInterval)
    (hInd : iIndepFun (fun i (ω : ι → Bool) => ω i) P)
    (hMarg : ∀ i, P.map (fun ω => ω i) = bernoulliMeasure true false p)
    (F : Finset ι) (ξ : ι → Bool) (E : Set (ι → Bool)) (c : ℝ≥0∞)
    (hSuccess : c ≤ ProbabilityTheory.cond P {ω | ∀ i ∈ F, ω i = ξ i} E) :
    c * ENNReal.ofReal (min (p : ℝ) (1 - (p : ℝ))) ^ F.card ≤ P E := by
  calc
    c * ENNReal.ofReal (min (p : ℝ) (1 - (p : ℝ))) ^ F.card ≤
        ProbabilityTheory.cond P {ω | ∀ i ∈ F, ω i = ξ i} E *
          P {ω | ∀ i ∈ F, ω i = ξ i} :=
      mul_le_mul' hSuccess (pow_min_le_independent_measure_pattern P p hInd hMarg F ξ)
    _ = P ({ω | ∀ i ∈ F, ω i = ξ i} ∩ E) :=
      cond_mul_eq_inter (measurableSet_pattern F ξ) E P
    _ ≤ P E := measure_mono Set.inter_subset_right

/-- Prescribing one closed and one open coordinate consumes both Bernoulli masses. -/
theorem measure_mixed_pair (p : unitInterval) :
    (Measure.infinitePi (fun _ : Bool => bernoulliMeasure true false p))
      {ω | ω false = false ∧ ω true = true} =
      ENNReal.ofReal (p : ℝ) * ENNReal.ofReal (1 - (p : ℝ)) := by
  have h := measure_pattern p (Finset.univ : Finset Bool) id
  simpa only [Finset.mem_univ, forall_const, Bool.forall_bool, id_eq, Fintype.prod_bool,
    Bool.false_eq_true, if_false, if_true] using h

end LatticeProb.Prob.Percolation.FiniteCylinderBounds
