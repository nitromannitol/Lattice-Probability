import LatticeProb.Prob.MarkedRectanglePhaseFinite

/-! Restrictions of product measures to marked rectangles. -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace LatticeProb

/-- Intersecting a marked rectangle with a coordinate rectangle retains a
marked rectangle, with coordinatewise maximum and minimum bounds. -/
theorem marked_Ico_rectangle_inter {E : Type*} (n : ℕ) (A : Set E)
    (u v p q : Fin n → ℝ) :
    (A ×ˢ univ.pi (fun i => Ico (u i) (v i))) ∩
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i))) =
    A ×ˢ univ.pi (fun i => Ico (max (u i) (p i)) (min (v i) (q i))) := by
  rw [Set.prod_inter_prod, Set.inter_univ, ← Set.pi_inter_distrib]
  simp only [Set.Ico_inter_Ico]

/-- A marked rectangle restriction factors into a scaled mark measure and
normalized rectangle measure when all sides have positive length. -/
theorem restrict_prod_marked_Ico_rectangle {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) [IsFiniteMeasure ρ] (n : ℕ) (A : Set E)
    (u v : Fin n → ℝ) (huv : ∀ i, u i < v i) :
    (ρ.prod (volume : Measure (Fin n → ℝ))).restrict
        (A ×ˢ univ.pi (fun i => Ico (u i) (v i))) =
      ((∏ i, ENNReal.ofReal (v i - u i)) • ρ.restrict A).prod
        ((∏ i, ENNReal.ofReal (v i - u i))⁻¹ •
          volume.restrict (univ.pi fun i => Ico (u i) (v i))) := by
  classical
  let V : ℝ≥0∞ := ∏ i, ENNReal.ofReal (v i - u i)
  have h0 : V ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
    ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (huv i)))
  have ht : V ≠ ⊤ := ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  change (ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (A ×ˢ univ.pi (fun i => Ico (u i) (v i))) =
    (V • ρ.restrict A).prod (V⁻¹ • volume.restrict
      (univ.pi fun i => Ico (u i) (v i)))
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ENNReal.mul_inv_cancel h0 ht, one_smul, Measure.prod_restrict]

/-- A marked rectangle with a nonpositive side length has zero restriction. -/
theorem restrict_prod_marked_Ico_rectangle_eq_zero {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (n : ℕ) (A : Set E) (u v : Fin n → ℝ)
    (h : ∃ i, v i ≤ u i) :
    (ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (A ×ˢ univ.pi (fun i => Ico (u i) (v i))) = 0 := by
  obtain ⟨i, hi⟩ := h
  have he : univ.pi (fun i => Ico (u i) (v i)) = ∅ :=
    Set.univ_pi_eq_empty (Set.Ico_eq_empty (not_lt_of_ge hi))
  simp [he]

end LatticeProb
