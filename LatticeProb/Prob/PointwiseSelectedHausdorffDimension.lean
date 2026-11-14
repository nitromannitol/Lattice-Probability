import LatticeProb.Prob.SelectedHausdorffDimension

/-!
# Hausdorff dimension from pointwise eventual selected covers

A point-dependent starting scale can be handled by a countable decomposition
into sets covered at every scale beyond a fixed threshold.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace LatticeProb

open Classical in
/-- A uniform expected-cost bound gives a dimension bound when each point is
in the selected cover eventually, with the starting scale allowed to vary. -/
theorem ae_dimH_le_of_pointwise_selected_finite_cover
    {Ω X : Type*} [MeasurableSpace Ω] [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure Ω}
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (d : ℝ≥0) (hd : 0 < d) (S : Ω → Set X) (A : Set Ω)
    (C : ∀ n, ι n → Set X) (E : ∀ n, ι n → Set Ω)
    (hE : ∀ n i, MeasurableSet (E n i)) (r : ℕ → ℝ≥0∞)
    (hr : Tendsto r atTop (𝓝 0))
    (hdiam : ∀ n i, Metric.ediam (C n i) ≤ r n)
    (hcover : ∀ ω ∈ A, ∀ x ∈ S ω, ∀ᶠ n in atTop,
      x ∈ ⋃ i, if ω ∈ E n i then C n i else ∅)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hcost : ∀ n, (∑ i, Metric.ediam (C n i) ^ (d : ℝ) * μ (E n i)) ≤ K) :
    ∀ᵐ ω ∂μ, ω ∈ A → dimH (S ω) ≤ (d : ℝ≥0∞) := by
  classical
  let T : ℕ → Ω → Set X := fun N ω =>
    {x | x ∈ S ω ∧ ∀ n ≥ N, x ∈ ⋃ i, if ω ∈ E n i then C n i else ∅}
  have hT : ∀ N, ∀ᵐ ω ∂μ, ω ∈ A → dimH (T N ω) ≤ (d : ℝ≥0∞) := by
    intro N
    apply ae_dimH_le_of_selected_finite_cover d hd (T N) A C E hE r hr hdiam
    · intro ω hω
      filter_upwards [eventually_ge_atTop N] with n hn
      intro x hx
      exact hx.2 n hn
    · exact hK
    · exact hcost
  filter_upwards [ae_all_iff.2 hT] with ω hω hA
  calc
    dimH (S ω) ≤ dimH (⋃ N, T N ω) := by
      apply dimH_mono
      intro x hx
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hcover ω hA x hx)
      exact mem_iUnion.2 ⟨N, hx, hN⟩
    _ = ⨆ N, dimH (T N ω) := dimH_iUnion _
    _ ≤ (d : ℝ≥0∞) := iSup_le fun N => hω N hA

end LatticeProb
