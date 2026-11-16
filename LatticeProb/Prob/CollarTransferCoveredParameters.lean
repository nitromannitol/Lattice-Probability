import LatticeProb.Prob.CollarTransferCompactParameters

/-! # Collar parameters subordinate to an open cover -/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace LatticeProb

/-- If an open set covers the closure of the domain, the ordered collar
parameters can be chosen so that the collar is also covered. -/
theorem exists_collar_transfer_covered_parameters
    {X : Type*} [MetricSpace X] [ProperSpace X] {J : Type*} [Finite J]
    {U O : Set X} (hU : Bornology.IsBounded U)
    (hO : IsOpen O) (hcover : closure U ⊆ O)
    (W : J → Set X) (hW : ∀ j, Bornology.IsBounded (W j))
    {r : ℝ≥0} (hr : 0 < r) :
    ∃ η τ : ℝ, 0 < η ∧ 0 < τ ∧
      ∀ c : ℝ, 0 < c →
        ∃ (a e δ mesh : ℝ) (C : Set X),
          0 < a ∧ 0 < e ∧ 0 < δ ∧ 0 < mesh ∧
          a + e ≤ c ∧ δ ≤ c ∧ a + e + mesh < δ ∧
          ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞) ∧
          IsCompact C ∧ thickening δ U ⊆ C ∧
          thickening δ U ⊆ O ∧ (∀ j, closure (W j) ⊆ C) ∧
          ∀ L : ℕ, ∃ b : ℝ, 0 < b ∧
            ((L + 1 : ℝ≥0∞) * ENNReal.ofReal b +
              (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
              (ENNReal.ofReal τ + (L + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤
                (r : ℝ≥0∞) := by
  obtain ⟨δ₀, hδ₀, hδ₀O⟩ := hU.isCompact_closure.exists_thickening_subset_open hO hcover
  obtain ⟨η, τ, hη, hτ, hparams⟩ := exists_collar_transfer_compact_parameters hU W hW hr
  refine ⟨η, τ, hη, hτ, ?_⟩
  intro c hc
  obtain ⟨a, e, δ, mesh, C, ha, he, hδ, hmesh, hae, hδc, hbuffer, hsmall,
    hC, hUC, hWC, hbudget⟩ := hparams (min c δ₀) (lt_min hc hδ₀)
  refine ⟨a, e, δ, mesh, C, ha, he, hδ, hmesh,
    hae.trans (min_le_left _ _), hδc.trans (min_le_left _ _), hbuffer, hsmall,
    hC, hUC, ?_, hWC, hbudget⟩
  exact (thickening_subset_of_subset δ subset_closure).trans
    ((thickening_mono (hδc.trans (min_le_right _ _)) _).trans hδ₀O)

end LatticeProb
