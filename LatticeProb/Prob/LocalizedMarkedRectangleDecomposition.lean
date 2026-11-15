import LatticeProb.Prob.MarkedRectangleRestriction

/-! Finite decompositions of localized marked rectangle restrictions. -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace LatticeProb

/-- Restricting to a finite disjoint union of marked rectangles inside a
coordinate rectangle gives a sum of normalized nonempty rectangle products. -/
theorem restrict_localized_marked_rectangles {E ι : Type*} [MeasurableSpace E]
    (ρ : Measure E) [IsFiniteMeasure ρ] (n : ℕ) (s : Finset ι)
    (A : ι → Set E) (u v : ι → Fin n → ℝ) (p q : Fin n → ℝ)
    (hA : ∀ j, MeasurableSet (A j))
    (hd : (s : Set ι).PairwiseDisjoint
      (fun j => A j ×ˢ univ.pi (fun i => Ico (u j i) (v j i)))) :
    let B := univ ×ˢ univ.pi (fun i => Ico (p i) (q i))
    let R := fun j => A j ×ˢ univ.pi (fun i => Ico (u j i) (v j i))
    let lo := fun j i => max (u j i) (p i)
    let hi := fun j i => min (v j i) (q i)
    ((ρ.prod (volume : Measure (Fin n → ℝ))).restrict B).restrict (⋃ j ∈ s, R j) =
      ∑ j ∈ s.filter (fun j => ∀ i, lo j i < hi j i),
        ((∏ i, ENNReal.ofReal (hi j i - lo j i)) • ρ.restrict (A j)).prod
          ((∏ i, ENNReal.ofReal (hi j i - lo j i))⁻¹ •
            volume.restrict (univ.pi fun i => Ico (lo j i) (hi j i))) := by
  classical
  dsimp only
  let R := fun j => A j ×ˢ univ.pi (fun i => Ico (u j i) (v j i))
  have hR : ∀ j, MeasurableSet (R j) := by
    intro j
    exact (hA j).prod (MeasurableSet.univ_pi (fun i => measurableSet_Ico))
  have hs := Measure.sum_coe_finset s (fun j =>
    ((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).restrict (R j))
  rw [Measure.restrict_biUnion_finset hd hR]
  change Measure.sum (fun j : s =>
    ((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).restrict (R j)) = _
  rw [hs]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Measure.restrict_restrict (hR j)]
  change (ρ.prod (volume : Measure (Fin n → ℝ))).restrict
    ((A j ×ˢ univ.pi (fun i => Ico (u j i) (v j i))) ∩
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))) = _
  rw [marked_Ico_rectangle_inter]
  split_ifs with h
  · exact restrict_prod_marked_Ico_rectangle ρ n (A j) _ _ h
  · apply restrict_prod_marked_Ico_rectangle_eq_zero
    push Not at h
    exact h

end LatticeProb
