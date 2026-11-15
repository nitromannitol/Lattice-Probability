import LatticeProb.Analysis.TouchingMinimaGridWindow
import Mathlib.Topology.Compactness.Compact

/-! # Shared frontier arcs on ordered windows -/

set_option autoImplicit false

open Set Function
open scoped unitInterval

namespace LatticeProb

/-- Reciprocal-grid frontier arcs extend to ordered windows when intersections
of ordered segments agree with their shared frontiers. -/
theorem shared_frontier_arc_of_grid_frontier_arcs
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (η : ℝ → X) (f : ℝ → ℝ) (hc : Continuous η) (hf : Continuous f)
    (hfront : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      η '' Icc a b ∩ η '' Icc c d =
        frontier (η '' Icc a b) ∩ frontier (η '' Icc c d))
    (hgrid : ∀ n : ℕ, 0 < n → ∀ i j : ℤ, i + 1 < j →
      let ε : ℝ := 1 / n
      max (sInf (f '' Icc (ε * ((i : ℝ) - 1)) (ε * i)))
        (sInf (f '' Icc (ε * ((j : ℝ) - 1)) (ε * j))) <
        sInf (f '' Icc (ε * i) (ε * ((j : ℝ) - 1))) →
      ∃ p : C(unitInterval, X), Injective p ∧
        (∀ t, p t ∈ frontier (η '' Icc (ε * ((i : ℝ) - 1)) (ε * i))) ∧
        (∀ t, p t ∈ frontier (η '' Icc (ε * ((j : ℝ) - 1)) (ε * j))))
    {a b c d : ℝ} (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hgap : max (sInf (f '' Icc a b)) (sInf (f '' Icc c d)) <
      sInf (f '' Icc b c)) :
    ∃ p : C(unitInterval, X), Injective p ∧
      (∀ t, p t ∈ frontier (η '' Icc a b)) ∧
      (∀ t, p t ∈ frontier (η '' Icc c d)) := by
  obtain ⟨n, hn, hwin⟩ :=
    exists_reciprocal_grid_window_of_interval_minima_le hf hab.le hbc hcd.le hgap
  obtain ⟨i, j, hij, hai, hib, hcj, hjd, hmin⟩ := hwin n le_rfl
  obtain ⟨p, hp, hpi, hpj⟩ := hgrid n hn i j hij hmin
  have hclosedI : IsClosed (η '' Icc ((1 / (n : ℝ)) * ((i : ℝ) - 1))
      ((1 / (n : ℝ)) * i)) := (isCompact_Icc.image hc).isClosed
  have hclosedJ : IsClosed (η '' Icc ((1 / (n : ℝ)) * ((j : ℝ) - 1))
      ((1 / (n : ℝ)) * j)) := (isCompact_Icc.image hc).isClosed
  have hmem (t : unitInterval) : p t ∈ η '' Icc a b ∩ η '' Icc c d := by
    constructor
    · exact image_mono (Icc_subset_Icc hai.le hib.le) (hclosedI.frontier_subset (hpi t))
    · exact image_mono (Icc_subset_Icc hcj.le hjd.le) (hclosedJ.frontier_subset (hpj t))
  refine ⟨p, hp, ?_, ?_⟩
  · intro t
    exact ((hfront a b c d hab hbc hcd) ▸ hmem t).1
  · intro t
    exact ((hfront a b c d hab hbc hcd) ▸ hmem t).2

end LatticeProb
