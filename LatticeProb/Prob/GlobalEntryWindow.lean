import LatticeProb.Prob.GlobalEntryFinite
import LatticeProb.Topology.FirstOpenEntryData

/-! # Global entry and finite entry windows -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- If all visits occur after `a` and a visit occurs at `b`, the global entry
is the infimum of the visits in the finite window `[a, b]`. -/
theorem globalOpenEntry_eq_coe_window_csInf {Ω E : Type*}
    (f : Ω → ℝ → E) (V : Set E) (ω : Ω) (a b : ℝ)
    (ha : ∀ t, f ω t ∈ V → a ≤ t) (hb : f ω b ∈ V) :
    globalOpenEntry f V ω =
      ((sInf {t ∈ Icc a b | f ω t ∈ V} : ℝ) : EReal) := by
  let S : Set ℝ := {t | f ω t ∈ V}
  let W : Set ℝ := {t ∈ Icc a b | f ω t ∈ V}
  have hab : a ≤ b := ha b hb
  have hs : S.Nonempty := ⟨b, hb⟩
  have hw : W.Nonempty := ⟨b, ⟨⟨hab, le_rfl⟩, hb⟩⟩
  have hS : BddBelow S := ⟨a, fun t ht => ha t ht⟩
  have hW : BddBelow W := ⟨a, fun _ ht => ht.1.1⟩
  have heq : sInf S = sInf W := by
    apply le_antisymm
    · apply le_csInf hw
      intro t ht
      exact csInf_le hS ht.2
    · apply le_csInf hs
      intro t ht
      by_cases htb : t ≤ b
      · exact csInf_le hW ⟨⟨ha t ht, htb⟩, ht⟩
      · exact (csInf_le hW ⟨⟨hab, le_rfl⟩, hb⟩).trans (le_of_not_ge htb)
  rw [globalOpenEntry_eq_coe_csInf f V ω hs hS, heq]

/-- A finite entry window for a continuous complex path gives the global entry,
its interval bounds and approximation by visits, and a closure endpoint. -/
theorem globalOpenEntry_window_data (P : ℝ → ℂ) (V : Set ℂ) (a b : ℝ)
    (ha : ∀ t, P t ∈ V → a ≤ t) (haV : P a ∉ V) (hb : P b ∈ V)
    (hP : ContinuousOn P (Icc a b)) :
    let e : ℝ := sInf {t ∈ Icc a b | P t ∈ V}
    globalOpenEntry (fun (_ : Unit) t => P t) V () = (e : EReal) ∧
      a ≤ e ∧ e ≤ b ∧
      (∀ u ∈ Icc a b, u < e → P u ∉ V) ∧
      (∀ δ : ℝ, 0 < δ →
        ∃ t ∈ Icc a b, P t ∈ V ∧ e ≤ t ∧ t < e + δ) ∧
      P e ∈ closure V := by
  have hab : a ≤ b := ha b hb
  have hdata :=
    SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery.first_open_entry_data
      P V hab haV hb
  have hclosure :=
    SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery.first_open_entry_mem_closure
      P V hab hP haV hb
  exact ⟨globalOpenEntry_eq_coe_window_csInf (fun (_ : Unit) t => P t) V () a b ha hb,
    hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2, hclosure⟩

end LatticeProb
