import LatticeProb.Analysis.TouchingMinimaGridWindow
import LatticeProb.Topology.AreaCurveNestedSharedArc

/-! # Shared arcs from fine-grid contour comparisons -/

set_option autoImplicit false

open Set MeasureTheory Function
open scoped unitInterval

namespace LatticeProb

/-- A strict contour window yields a shared frontier arc when every reciprocal
mesh has the corresponding grid-cell arc property for the same curve. -/
theorem shared_frontier_arc_of_reciprocal_grid_windows
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (η : ℝ → X) (μ : Measure X) (f : ℝ → ℝ)
    (hc : Continuous η) (hp : IsProperMap η) (hs : Surjective η)
    (hmap : Measure.map η volume = μ)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    (hf : Continuous f)
    (hgrid : ∀ n : ℕ, 0 < n → ∀ i j : ℤ, i + 1 < j →
      let ε : ℝ := 1 / n
      max (sInf (f '' Icc (ε * ((i : ℝ) - 1)) (ε * i)))
        (sInf (f '' Icc (ε * ((j : ℝ) - 1)) (ε * j))) <
        sInf (f '' Icc (ε * i) (ε * ((j : ℝ) - 1))) →
      ∃ p : C(unitInterval, X), Injective p ∧
        ∀ t, p t ∈ η '' Icc (ε * ((i : ℝ) - 1)) (ε * i) ∩
          η '' Icc (ε * ((j : ℝ) - 1)) (ε * j))
    {a b c d : ℝ} (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hgap : max (sInf (f '' Icc a b)) (sInf (f '' Icc c d)) <
      sInf (f '' Icc b c)) :
    ∃ p : C(unitInterval, X), Injective p ∧
      (∀ t, p t ∈ frontier (η '' Icc a b)) ∧
      (∀ t, p t ∈ frontier (η '' Icc c d)) := by
  obtain ⟨n, hn, hwin⟩ :=
    exists_reciprocal_grid_window_of_interval_minima_le hf hab.le hbc hcd.le hgap
  obtain ⟨i, j, hij, hai, hib, hcj, hjd, hmin⟩ := hwin n le_rfl
  obtain ⟨p, hpi, hpm⟩ := hgrid n hn i j hij hmin
  apply shared_frontier_arc_of_nested_segment_images η μ hc hp hs hmap hμ hab hbc hcd
    (Icc_subset_Icc hai.le hib.le) (Icc_subset_Icc hcj.le hjd.le) p hpi hpm

end LatticeProb
