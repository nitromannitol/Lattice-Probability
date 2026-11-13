/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5ScaleCounting at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

 



set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

theorem many_good_scales_intersection {α : Type*} [DecidableEq α]
    (F A B : Finset α) (K : ℕ)
    (hA : A ⊆ F) (hB : B ⊆ F)
    (hF : 2 * F.card ≤ K)
    (hAc : 3 * K ≤ 8 * A.card)
    (hBc : 3 * K ≤ 8 * B.card) :
    K ≤ 4 * (A ∩ B).card := by
  have hu : (A ∪ B).card ≤ F.card :=
    Finset.card_le_card (Finset.union_subset hA hB)
  have hcount := Finset.card_union_add_card_inter A B
  omega

end SupercriticalLQGUniqueness.B2.QPos
