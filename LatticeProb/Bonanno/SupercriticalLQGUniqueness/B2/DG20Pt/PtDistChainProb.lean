/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainProb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainEvent

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_chain_failure_measure_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : ℝ) (φ : Ω → ℂ → ℝ) (U : Set ℂ)
    (p : ℕ → ℂ) (N : ℕ) (A b : ℝ≥0∞)
    (hedge : ∀ j, j ≤ N →
      P {ω | ¬ lfppDOn ξ (φ ω) U (p j) (p (j + 1)) ≤ A} ≤ b) :
    P {ω | ¬ lfppDOn ξ (φ ω) U (p 0) (p (N + 1)) ≤
      (N + 1 : ℝ≥0∞) * A} ≤ (N + 1 : ℝ≥0∞) * b := by
  let E : ℕ → Set Ω := fun j =>
    {ω | ¬ lfppDOn ξ (φ ω) U (p j) (p (j + 1)) ≤ A}
  calc
    _ ≤ P (⋃ j ∈ Finset.range (N + 1), E j) :=
      measure_mono (pt_dist_chain_bad_subset_biUnion ξ φ U p N A)
    _ ≤ ∑ j ∈ Finset.range (N + 1), P (E j) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (N + 1), b := by
      apply Finset.sum_le_sum
      intro j hj
      exact hedge j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = (N + 1 : ℝ≥0∞) * b := by simp

end SupercriticalLQGUniqueness.B2.DG20Pt
