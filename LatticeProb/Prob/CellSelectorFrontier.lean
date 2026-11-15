import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellSelector
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Continuity sets for selectors built from finite partitions -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne

namespace LatticeProb

variable {X ι J : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [Fintype ι]

private theorem finite_union_frontier_null {α : Type*} [Fintype α]
    (γ : Measure X) (A : α → Set X)
    (hA : ∀ i, γ (frontier (A i)) = 0) (F : Finset α) :
    γ (frontier (⋃ i ∈ F, A i)) = 0 := by
  apply measure_mono_null (F.frontier_biUnion_subset A)
  exact measure_iUnion_null fun i => measure_iUnion_null fun _ => hA i

/-- A selector which is constant on each of finitely many disjoint continuity
cells has null frontier for every one of its fibers. -/
theorem cellSelector_fiber_frontier_null (γ : Measure X) (E : ι → Set X)
    (select : ι → Option J)
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hE : ∀ i, γ (frontier (E i)) = 0) (q : Option J) :
    γ (frontier (cellSelector E select ⁻¹' {q})) = 0 := by
  classical
  have hlabel (l : Option ι) : γ (frontier (cellLabel E ⁻¹' {l})) = 0 := by
    cases l with
    | none =>
      have heq : cellLabel E ⁻¹' {none} = (⋃ i, E i)ᶜ := by
        ext x
        simp only [mem_preimage, mem_singleton_iff, cellLabel_eq_none_iff,
          mem_compl_iff, mem_iUnion, not_exists]
      rw [heq, frontier_compl]
      simpa only [Finset.mem_univ, iUnion_true] using finite_union_frontier_null γ E hE Finset.univ
    | some i =>
      have heq : cellLabel E ⁻¹' {some i} = E i := by
        ext x
        exact cellLabel_eq_some_iff E hdisj x i
      rw [heq]
      exact hE i
  have heq : cellSelector E select ⁻¹' {q} =
      ⋃ l ∈ Finset.univ.filter (fun l : Option ι => l.bind select = q),
        cellLabel E ⁻¹' {l} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, cellSelector]
    constructor
    · intro hx
      exact ⟨cellLabel E x, hx, rfl⟩
    · rintro ⟨l, hl, hx⟩
      rw [hx]
      exact hl
  rw [heq]
  exact finite_union_frontier_null γ (fun l => cellLabel E ⁻¹' {l}) hlabel _

end LatticeProb
