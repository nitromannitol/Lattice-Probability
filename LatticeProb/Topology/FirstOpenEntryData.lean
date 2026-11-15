/- Copied from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery.FirstEntry
   at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82, declarations
   first_open_entry_data and first_open_entry_mem_closure; imports adapted. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Monotone

set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery

theorem first_open_entry_data (P : ℝ → ℂ) (V : Set ℂ)
    {a b : ℝ} (hab : a ≤ b) (_ha : P a ∉ V) (hb : P b ∈ V) :
    let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
    let e : ℝ := sInf E
    a ≤ e ∧ e ≤ b ∧
      (∀ u ∈ Icc a b, u < e → P u ∉ V) ∧
      (∀ δ : ℝ, 0 < δ →
        ∃ t ∈ Icc a b, P t ∈ V ∧ e ≤ t ∧ t < e + δ) := by
  let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
  let e : ℝ := sInf E
  have hEne : E.Nonempty := ⟨b, ⟨⟨hab, le_rfl⟩, hb⟩⟩
  have hEbelow : BddBelow E := ⟨a, by
    intro t ht
    exact ht.1.1⟩
  have haE : a ≤ e := le_csInf hEne (by
    intro t ht
    exact ht.1.1)
  have heB : e ≤ b := csInf_le hEbelow ⟨⟨hab, le_rfl⟩, hb⟩
  refine ⟨haE, heB, ?_, ?_⟩
  · intro u hu hue huv
    have heu : e ≤ u := csInf_le hEbelow ⟨hu, huv⟩
    exact (not_lt_of_ge heu) hue
  · intro δ hδ
    obtain ⟨t, ht, hlt⟩ := exists_lt_of_csInf_lt hEne (lt_add_of_pos_right e hδ)
    exact ⟨t, ht.1, ht.2, csInf_le hEbelow ht, hlt⟩

 

theorem first_open_entry_mem_closure (P : ℝ → ℂ) (V : Set ℂ)
    {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (ha : P a ∉ V) (hb : P b ∈ V) :
    let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
    P (sInf E) ∈ closure V := by
  let E : Set ℝ := {t ∈ Icc a b | P t ∈ V}
  let e : ℝ := sInf E
  have hEne : E.Nonempty := ⟨b, ⟨⟨hab, le_rfl⟩, hb⟩⟩
  have hEbelow : BddBelow E := ⟨a, by
    intro t ht
    exact ht.1.1⟩
  have hdata := first_open_entry_data P V hab ha hb
  dsimp only at hdata
  have hEe : e ∈ closure E := csInf_mem_closure hEne hEbelow
  have hcont : ContinuousWithinAt P E e :=
    (hP e ⟨hdata.1, hdata.2.1⟩).mono (by
      intro t ht
      exact ht.1)
  exact hcont.mem_closure hEe (by
    intro t ht
    exact ht.2)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery
