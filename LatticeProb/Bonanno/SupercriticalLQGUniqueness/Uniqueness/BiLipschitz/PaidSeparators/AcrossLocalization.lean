/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.AcrossLocalization at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import LatticeProb.Bonanno.LQGMetric.Metric.Internal




 






set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators

 


theorem len_eq_internalPartitionSup (D : LSCMetric) {Y : Set ℂ}
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (hY : ∀ t ∈ Icc a b, P t ∈ Y) :
    D.len P a b =
      ⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
        ∑ i ∈ Finset.range p.1,
          D.internal Y
            (⟨P (p.2.1 i), hY _ (p.2.2.2 i)⟩,
             ⟨P (p.2.1 (i + 1)), hY _ (p.2.2.2 (i + 1))⟩) := by
  change (⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
      ∑ i ∈ Finset.range p.1,
        edist (D.pt (P (p.2.1 (i + 1)))) (D.pt (P (p.2.1 i)))) = _
  apply le_antisymm
  · refine iSup_le fun p => le_iSup_of_le p ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [edist_comm]
    change D (P (p.2.1 i), P (p.2.1 (i + 1))) ≤ _
    exact BiLipschitz.Barrier.edist_le_internal' D Y
      (⟨P (p.2.1 i), hY _ (p.2.2.2 i)⟩,
       ⟨P (p.2.1 (i + 1)), hY _ (p.2.2.2 (i + 1))⟩)
  · refine iSup_le fun p => ?_
    have hsum :
        (∑ i ∈ Finset.range p.1,
          D.internal Y
            (⟨P (p.2.1 i), hY _ (p.2.2.2 i)⟩,
             ⟨P (p.2.1 (i + 1)), hY _ (p.2.2.2 (i + 1))⟩)) ≤
        ∑ i ∈ Finset.range p.1, D.len P (p.2.1 i) (p.2.1 (i + 1)) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hsub : Icc (p.2.1 i) (p.2.1 (i + 1)) ⊆ Icc a b :=
        Icc_subset_Icc (p.2.2.2 i).1 (p.2.2.2 (i + 1)).2
      exact BiLipschitz.Barrier.internal_le_len' D
        ⟨p.2.2.1 (Nat.le_succ i), hP.2.mono hsub⟩
        (fun t ht => hY t (hsub ht))
    calc
      (∑ i ∈ Finset.range p.1,
          D.internal Y
            (⟨P (p.2.1 i), hY _ (p.2.2.2 i)⟩,
             ⟨P (p.2.1 (i + 1)), hY _ (p.2.2.2 (i + 1))⟩))
          ≤ ∑ i ∈ Finset.range p.1, D.len P (p.2.1 i) (p.2.1 (i + 1)) := hsum
      _ = D.len P (p.2.1 0) (p.2.1 p.1) := by
        exact LQGMetric.MetricGeometry.sum_curveLength_eq (D.pt ∘ P) p.2.2.1 p.1
      _ ≤ D.len P a b :=
        LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P)
          (p.2.2.2 0).1 (p.2.2.2 p.1).2

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators
