import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Metrizable.Basic

/-! # Countable reference covers from separable representatives -/

set_option autoImplicit false

namespace LatticeProb

/-- A separable nonempty family of representatives admits countably many valid
references whenever label discrepancy is bounded by the distance between their
representatives. No metric properties of the discrepancy are required. -/
theorem exists_countable_reference_cover
    {X Y : Type*} [PseudoMetricSpace X] (V : Set X) [TopologicalSpace.SeparableSpace V]
    (hV : V.Nonempty) (q : X → Y) (D : Y → Y → ℝ)
    (hD : ∀ x ∈ V, ∀ y ∈ V, D (q x) (q y) ≤ dist x y) :
    ∃ r : ℕ → X, (∀ n, r n ∈ V) ∧
      ∀ x ∈ V, ∀ ε > 0, ∃ n, D (q (r n)) (q x) < ε := by
  let : Nonempty V := ⟨⟨hV.choose, hV.choose_spec⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq V
  refine ⟨fun n => u n, fun n => (u n).property, ?_⟩
  intro x hx ε hε
  obtain ⟨n, hn⟩ := hu.exists_dist_lt (⟨x, hx⟩ : V) hε
  exact ⟨n, lt_of_le_of_lt (hD (u n) (u n).property x hx) (by
    simpa only [Subtype.dist_eq, dist_comm] using hn)⟩

end LatticeProb
