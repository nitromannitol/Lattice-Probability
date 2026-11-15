import LatticeProb.Prob.UniformPhaseCell

/-! Phase pushforward for a finite sequence of complete intervals. -/

open MeasureTheory Set

namespace LatticeProb

/-- The phase pushforward of Lebesgue measure on consecutive complete
periods is the corresponding multiple of uniform measure. -/
theorem map_fract_mul_restrict_cells {a : ℝ} (ha : 0 < a) (u c : ℝ) (n : ℕ) :
    Measure.map (fun x : ℝ => Int.fract (a * x - c))
        (volume.restrict (Ico u (u + (n : ℝ) * a⁻¹))) =
      n • (ENNReal.ofReal a⁻¹ • volume.restrict (Ico 0 1)) := by
  have hphase : Measurable (fun x : ℝ => Int.fract (a * x - c)) := by
    exact measurable_fract.comp (by fun_prop)
  induction n with
  | zero => simp
  | succ n ih =>
    have h₁ : u ≤ u + (n : ℝ) * a⁻¹ := by
      have hn := mul_nonneg (Nat.cast_nonneg n) (inv_nonneg.mpr ha.le)
      linarith
    have h₂ : u + (n : ℝ) * a⁻¹ ≤ u + (n : ℝ) * a⁻¹ + a⁻¹ := by
      have := inv_pos.mpr ha
      linarith
    have hsplit : Ico u (u + ((n + 1 : ℕ) : ℝ) * a⁻¹) =
        Ico u (u + (n : ℝ) * a⁻¹) ∪
          Ico (u + (n : ℝ) * a⁻¹) (u + (n : ℝ) * a⁻¹ + a⁻¹) := by
      rw [Ico_union_Ico_eq_Ico h₁ h₂]
      congr 1
      push_cast
      ring
    rw [hsplit, Measure.restrict_union Ico_disjoint_Ico_same measurableSet_Ico,
      Measure.map_add _ _ hphase, ih, map_fract_mul_restrict_cell ha]
    simp only [succ_nsmul]

end LatticeProb
