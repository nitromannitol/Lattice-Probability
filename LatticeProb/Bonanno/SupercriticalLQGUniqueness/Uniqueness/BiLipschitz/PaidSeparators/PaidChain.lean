/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidChain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidRecursion




 





set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators

 

theorem mem_paid_interval_of_mem_prefix (S : ℕ → ℝ) (hS : Monotone S)
    (hS0 : S 0 = 0) (J : ℕ) {u : ℝ} (hu : u ∈ Ico 0 (S J)) :
    ∃ j < J, u ∈ Ico (S j) (S (j + 1)) := by
  induction J with
  | zero =>
      rw [hS0] at hu
      exact False.elim (not_lt_of_ge hu.1 hu.2)
  | succ J ih =>
      by_cases h : u < S J
      · obtain ⟨j, hj, hju⟩ := ih ⟨hu.1, h⟩
        exact ⟨j, by omega, hju⟩
      · exact ⟨J, Nat.lt_succ_self J,
          ⟨le_of_not_gt h, hu.2⟩⟩

 

theorem exists_selected_component_at_terminal {ι : Type*}
    (F : Finset ι) (V : ι → Set ℂ) {P : ℝ → ℂ} {t T : ℝ}
    (ht : 0 < t) (htT : t ≤ T)
    (hPc : ContinuousOn P (Icc 0 T))
    (hcov : P '' Ico 0 t ⊆ ⋃ i ∈ F, V i) :
    ∃ i ∈ F, P t ∈ closure (V i) := by
  have hcl : closure (Ico (0 : ℝ) t) = Icc 0 t :=
    closure_Ico ht.ne
  have hPc' : ContinuousOn P (closure (Ico 0 t)) := by
    rw [hcl]
    exact hPc.mono (Icc_subset_Icc le_rfl htT)
  have htcl : t ∈ closure (Ico (0 : ℝ) t) := by
    rw [hcl]
    exact right_mem_Icc.2 ht.le
  have hPtcl : P t ∈ closure (P '' Ico 0 t) :=
    hPc'.image_closure ⟨t, htcl, rfl⟩
  have hsubset : P t ∈ closure (⋃ i ∈ F, V i) :=
    closure_mono hcov hPtcl
  rw [Finset.closure_biUnion] at hsubset
  obtain ⟨i, hi, hmem⟩ := mem_iUnion₂.mp hsubset
  exact ⟨i, hi, hmem⟩

 


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators
