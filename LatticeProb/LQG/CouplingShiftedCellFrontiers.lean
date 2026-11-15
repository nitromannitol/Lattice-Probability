import LatticeProb.LQG.CouplingSharedSegmentFrontiers
import LatticeProb.Topology.CompactCurveRange

/-! # Shared frontiers of shifted cells -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- A curve whose ordered segments meet on their shared frontiers has the same
property for any two distinct positive-mesh shifted cells. -/
theorem shifted_cells_inter_eq_shared_frontier
    (η : C(ℝ, ℂ))
    (h : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      η '' Icc a b ∩ η '' Icc c d =
        frontier (η '' Icc a b) ∩ frontier (η '' Icc c d))
    {ε : ℝ} (hε : 0 < ε) (θ : ℝ) {j k : ℤ} (hjk : j ≠ k) :
    (LatticeProb.shiftedCompactCell η ε θ j : Set ℂ) ∩
      LatticeProb.shiftedCompactCell η ε θ k =
        frontier (LatticeProb.shiftedCompactCell η ε θ j : Set ℂ) ∩
          frontier (LatticeProb.shiftedCompactCell η ε θ k : Set ℂ) := by
  have hends (i : ℤ) : ε * ((i : ℝ) - 1 + θ) < ε * ((i : ℝ) + θ) :=
    mul_lt_mul_of_pos_left (by linarith) hε
  simp only [LatticeProb.coe_shiftedCompactCell, uIcc_of_le (hends _).le]
  rcases lt_or_gt_of_ne hjk with hjk' | hkj
  · have hle : (j : ℝ) + 1 ≤ k := by exact_mod_cast Int.add_one_le_iff.mpr hjk'
    exact h _ _ _ _ (hends j) (mul_le_mul_of_nonneg_left (by linarith) hε.le) (hends k)
  · have hle : (k : ℝ) + 1 ≤ j := by exact_mod_cast Int.add_one_le_iff.mpr hkj
    rw [inter_comm, inter_comm (frontier _)]
    exact h _ _ _ _ (hends k) (mul_le_mul_of_nonneg_left (by linarith) hε.le) (hends j)

/-- Simultaneously for all positive meshes and shifts, distinct cells of each
coupled curve meet exactly on their shared frontiers. -/
theorem ae_shifted_cell_shared_frontiers_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ f ∈ ({ηL, η, η₀} : Set (Ω → C(ℝ, ℂ))),
      ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, ∀ j k : ℤ, j ≠ k →
        (LatticeProb.shiftedCompactCell (f ω) ε θ j : Set ℂ) ∩
          LatticeProb.shiftedCompactCell (f ω) ε θ k =
            frontier (LatticeProb.shiftedCompactCell (f ω) ε θ j : Set ℂ) ∩
              frontier (LatticeProb.shiftedCompactCell (f ω) ε θ k : Set ℂ) := by
  filter_upwards [ae_shared_frontiers_of_coupling D] with ω hω
  intro f hf ε hε θ j k hjk
  simp only [mem_insert_iff, mem_singleton_iff] at hf
  have hf' : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      f ω '' Icc a b ∩ f ω '' Icc c d =
        frontier (f ω '' Icc a b) ∩ frontier (f ω '' Icc c d) := by
    intro a b c d hab hbc hcd
    rcases hf with hf | hf | hf
    · rw [hf]; exact (hω a b c d hab hbc hcd).1
    · rw [hf]; exact (hω a b c d hab hbc hcd).2.1
    · rw [hf]; exact (hω a b c d hab hbc hcd).2.2
  exact shifted_cells_inter_eq_shared_frontier (f ω) hf' hε θ hjk

end MatedCRTHarmonic.MoTInput
