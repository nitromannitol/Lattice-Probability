import LatticeProb.Analysis.CellWindowStrictProduct
import LatticeProb.Analysis.ClockedCellIntervalStrict

/-! # Strict cell windows under an increasing clock -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- An increasing reparametrization preserves countability of the phases at
which a weak comparison of shifted cell minima fails to be strict. -/
theorem countable_cellWindowStrict_failures_comp_orderIso
    (f : C(ℝ, ℝ)) (ψ : ℝ ≃o ℝ) (ε : ℝ) (hε : 0 < ε)
    (hdist : ∀ x y, x ≠ y → IsLocalMin f x → IsLocalMin f y → f x ≠ f y) :
    {θ : ℝ | ¬ cellWindowStrict ε ⟨fun t => f (ψ t), f.continuous.comp ψ.continuous⟩ θ}.Countable := by
  classical
  have hc := countable_clocked_cell_interval_strict_failures
    (fun _ : Unit => (f : ℝ → ℝ)) (fun _ => f.continuous) ψ ε hε (fun _ => hdist)
  apply hc.mono
  intro θ hθ
  simp only [mem_ofPred_eq, cellWindowStrict, not_forall] at hθ
  obtain ⟨i, j, hij, hle, hnot⟩ := hθ
  have hij' : (i : ℝ) + 1 < j := by exact_mod_cast hij
  have hab : ε * ((i : ℝ) - 1 + θ) ≤ ε * ((i : ℝ) + θ) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith
  have hbc : ε * ((i : ℝ) + θ) ≤ ε * ((j : ℝ) - 1 + θ) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith
  have hcd : ε * ((j : ℝ) - 1 + θ) ≤ ε * ((j : ℝ) + θ) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith
  have himg (a b : ℝ) : (fun t => f (ψ t)) '' Icc a b = f '' Icc (ψ a) (ψ b) := by
    rw [show (fun t => f (ψ t)) = (f : ℝ → ℝ) ∘ ψ from rfl,
      Set.image_comp, ψ.image_Icc]
  simp only [ContinuousMap.coe_mk, uIcc_of_le hab, uIcc_of_le hbc,
    uIcc_of_le hcd, himg] at hle hnot
  exact ⟨(), i, j, hij, hle, hnot⟩

end LatticeProb
