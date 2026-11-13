/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.SegmentPartitionCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.IntegralPartition
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.Basic




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

theorem segCost_interval_eq (ξ : ℝ) (f : ℂ → ℝ) (z w : ℂ)
    {s t : ℝ} (hst : s ≤ t) :
    segCost ξ f (segPath z w s) (segPath z w t) =
      ∫⁻ u in Icc s t, lenDens ξ f (segPath z w) u := by
  by_cases hstrict : s < t
  · rw [segCost, ← Exponent.LatticePath.segPath_subPath_eq, lfppLen_subPath (segPath z w) hstrict]
  · have heq : s = t := le_antisymm hst (le_of_not_gt hstrict)
    subst t
    simp [Exponent.PaidDuality.segCost_self, Set.Icc_self]

theorem segCost_partition (ξ : ℝ) (f : ℂ → ℝ) (z w : ℂ)
    (v : ℕ → ℝ) (hv : ∀ i, v i ≤ v (i+1))
    (n : ℕ) (h0 : v 0 = 0) (hn : v n = 1) :
    (∑ i ∈ Finset.range n,
      segCost ξ f (segPath z w (v i)) (segPath z w (v (i+1)))) =
        segCost ξ f z w := by
  have hsum := lintegral_partition (lenDens ξ f (segPath z w)) v hv n
  calc
    (∑ i ∈ Finset.range n,
      segCost ξ f (segPath z w (v i)) (segPath z w (v (i+1)))) =
        ∑ i ∈ Finset.range n,
          ∫⁻ u in Icc (v i) (v (i+1)), lenDens ξ f (segPath z w) u := by
        apply Finset.sum_congr rfl
        intro i hi
        exact segCost_interval_eq ξ f z w (hv i)
    _ = ∫⁻ u in Icc (v 0) (v n), lenDens ξ f (segPath z w) u := hsum
    _ = segCost ξ f z w := by rw [h0, hn]; rfl


end SupercriticalLQGUniqueness.Exponent.InwardMap
