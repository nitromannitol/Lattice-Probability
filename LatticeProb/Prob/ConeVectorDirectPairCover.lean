import LatticeProb.Analysis.ConeVectorPartnerCover
import LatticeProb.Analysis.BackwardConeVectorPartnerCover
import LatticeProb.Prob.CorrelatedBMExceptionalPairs

/-!
# Cone-vector cover of direct-excursion pairs

Pairs formed by a common apex and either of two distinct direct partners are
covered by cone vectors and pairs with a local-minimum partner.
-/

set_option autoImplicit false

open Set
open MatedCRTHarmonic.MatedCRT (DirectRel)

namespace LatticeProb

/-- A direct-excursion pair is exceptional or is an image of a cone vector
of the paths or their time reversals. -/
theorem direct_excursion_pairs_subset_coneVectors (X Y : ℝ → ℝ) :
    {p : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel X p.1 a ∧ DirectRel Y p.1 b) ∨
       (DirectRel X a p.1 ∧ DirectRel Y b p.1)) ∧
      (p.2 = a ∨ p.2 = b)} ⊆
    {p : ℝ × ℝ | ∃ a b,
      ((DirectRel X p.1 a ∧ DirectRel Y p.1 b) ∨
       (DirectRel X a p.1 ∧ DirectRel Y b p.1)) ∧
      (IsLocalMin X a ∨ IsLocalMin Y b) ∧
      (p.2 = p.1 ∨ p.2 = a ∨ p.2 = b)} ∪
    (fun p : ℝ × ℝ => (p.2, p.1)) '' forwardConeVectors X Y ∪
    (fun p : ℝ × ℝ => (p.2, p.1)) '' backwardConeVectors X Y ∪
    (fun p : ℝ × ℝ => (-p.2, -p.1)) ''
      forwardConeVectors (fun t => X (-t)) (fun t => Y (-t)) ∪
    (fun p : ℝ × ℝ => (-p.2, -p.1)) ''
      backwardConeVectors (fun t => X (-t)) (fun t => Y (-t)) := by
  intro p hp
  rcases hp with ⟨a, b, hne, hrel, hp⟩
  by_cases he : IsLocalMin X a ∨ IsLocalMin Y b
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨a, b, hrel, he, Or.inr hp⟩)))
  · have hX : ¬ IsLocalMin X a := fun h => he (Or.inl h)
    have hY : ¬ IsLocalMin Y b := fun h => he (Or.inr h)
    rcases hrel with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hc := forward_excursion_partners_mem_coneVectors
        hx.1 hx.2.1 hx.2.2 hX hy.1 hy.2.1 hy.2.2 hY hne
      have hv := hp.elim (fun h => h ▸ hc.1) (fun h => h ▸ hc.2)
      rcases hv with hv | hv
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(p.2, p.1), hv, rfl⟩)))
      · exact Or.inr ⟨(-p.2, -p.1), hv, by simp only [neg_neg]⟩
    · have hc := backward_excursion_partners_mem_coneVectors
        hx.1 hx.2.1 hx.2.2 hX hy.1 hy.2.1 hy.2.2 hY hne
      have hv := hp.elim (fun h => h ▸ hc.1) (fun h => h ▸ hc.2)
      rcases hv with hv | hv
      · exact Or.inl (Or.inl (Or.inr ⟨(p.2, p.1), hv, rfl⟩))
      · exact Or.inl (Or.inr ⟨(-p.2, -p.1), hv, by simp only [neg_neg]⟩)

end LatticeProb
