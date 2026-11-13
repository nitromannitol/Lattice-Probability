/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.IntegralPartition at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.CellGradientCost




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

 

theorem lintegral_Icc_split (g : ℝ → ℝ≥0∞) {s t u : ℝ}
    (hst : s ≤ t) (htu : t ≤ u) :
    (∫⁻ x in Icc s u, g x) =
      (∫⁻ x in Icc s t, g x) + (∫⁻ x in Icc t u, g x) := by
  have hsu := Measure.restrict_congr_set
    (Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := s) (b := u))
  have hst' := Measure.restrict_congr_set
    (Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := s) (b := t))
  have htu' := Measure.restrict_congr_set
    (Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := t) (b := u))
  change (∫⁻ x, g x ∂MeasureTheory.volume.restrict (Icc s u)) =
    (∫⁻ x, g x ∂MeasureTheory.volume.restrict (Icc s t)) +
    (∫⁻ x, g x ∂MeasureTheory.volume.restrict (Icc t u))
  rw [← hsu, ← hst', ← htu', ← Ioc_union_Ioc_eq_Ioc hst htu]
  have hd : Disjoint (Ioc s t) (Ioc t u) := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.1
  rw [Measure.restrict_union hd measurableSet_Ioc, lintegral_add_measure]

 
theorem lintegral_partition (g : ℝ → ℝ≥0∞)
    (v : ℕ → ℝ) (hv : ∀ i, v i ≤ v (i+1)) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∫⁻ x in Icc (v i) (v (i+1)), g x) =
      ∫⁻ x in Icc (v 0) (v n), g x := by
  have hmon : Monotone v := monotone_nat_of_le_succ hv
  induction n with
  | zero =>
      simp [Set.Icc_self]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      exact (lintegral_Icc_split g (hmon (Nat.zero_le n)) (hv n)).symm


end SupercriticalLQGUniqueness.Exponent.InwardMap
