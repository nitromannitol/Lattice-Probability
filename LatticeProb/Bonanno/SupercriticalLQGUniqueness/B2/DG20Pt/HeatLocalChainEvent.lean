/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatLocalChainEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainTriangle

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_normalized_chain_upper_bad_subset
    {Ω : Type*} (ξ : ℝ) (φ : Ω → ℂ → ℝ) (U : Set ℂ)
    (p : ℕ → ℂ) (N : ℕ) (b A : ℝ≥0∞) :
    {ω | (N + 1 : ℝ≥0∞) * A <
      b * lfppDOn ξ (φ ω) U (p 0) (p (N + 1))} ⊆
      ⋃ j ∈ Finset.range (N + 1),
        {ω | A < b * lfppDOn ξ (φ ω) U (p j) (p (j + 1))} := by
  intro ω hω
  by_contra hnone
  have hedge (j : ℕ) (hj : j ∈ Finset.range (N + 1)) :
      b * lfppDOn ξ (φ ω) U (p j) (p (j + 1)) ≤ A := by
    by_contra hbad
    exact hnone (mem_biUnion hj (lt_of_not_ge hbad))
  have hsum := Finset.sum_le_sum (s := Finset.range (N + 1)) hedge
  have hchain := pt_dist_le_chain_sum ξ (φ ω) U p N
  change (N + 1 : ℝ≥0∞) * A <
    b * lfppDOn ξ (φ ω) U (p 0) (p (N + 1)) at hω
  apply (not_le_of_gt hω)
  calc
    b * lfppDOn ξ (φ ω) U (p 0) (p (N + 1)) ≤
        b * ∑ j ∈ Finset.range (N + 1),
          lfppDOn ξ (φ ω) U (p j) (p (j + 1)) := by gcongr
    _ = ∑ j ∈ Finset.range (N + 1),
          b * lfppDOn ξ (φ ω) U (p j) (p (j + 1)) := by rw [Finset.mul_sum]
    _ ≤ ∑ _j ∈ Finset.range (N + 1), A := hsum
    _ = (N + 1 : ℝ≥0∞) * A := by simp

end SupercriticalLQGUniqueness.B2.DG20Pt
