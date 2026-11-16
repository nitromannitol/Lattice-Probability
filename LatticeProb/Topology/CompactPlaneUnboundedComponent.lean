import LatticeProb.Topology.PolygonalJaniszewskiProved

/-!
# Unbounded complementary component of a compact plane set

A compact subset of the plane has a unique unbounded complementary component.
-/

open Set Bornology

namespace LatticeProb.Topology

/-- A compact plane set has a complementary component containing precisely those points whose
complementary component is unbounded. -/
theorem exists_unbounded_compl_component {K : Set ℂ} (hK : IsCompact K) :
    ∃ p ∈ Kᶜ, ¬ IsBounded (connectedComponentIn Kᶜ p) ∧
      ∀ x ∈ Kᶜ, (x ∈ connectedComponentIn Kᶜ p ↔
        ¬ IsBounded (connectedComponentIn Kᶜ x)) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  let p : ℂ := ((|R| + 1 : ℝ) : ℂ)
  have hp : R < ‖p‖ := by
    dsimp [p]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (le_abs_self R).trans_lt ((lt_add_one _).trans_le (le_abs_self _))
  have hpK : p ∈ Kᶜ := QuantumZipper.CA.Topo.setOf_lt_norm_subset_compl hR hp
  have hfar : {z : ℂ | R < ‖z‖} ⊆ connectedComponentIn Kᶜ p :=
    (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R).subset_connectedComponentIn hp
      (QuantumZipper.CA.Topo.setOf_lt_norm_subset_compl hR)
  have hu : ¬ IsBounded (connectedComponentIn Kᶜ p) := fun h =>
    LatticeProb.Janiszewski.not_isBounded_setOf_lt_norm R (h.subset hfar)
  refine ⟨p, hpK, hu, ?_⟩
  intro x hx
  constructor
  · intro h hb
    rw [← connectedComponentIn_eq h] at hb
    exact hu hb
  · intro hb
    have hsub := QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hR
      isPreconnected_connectedComponentIn hb
      (Set.disjoint_left.2 fun _ hy hz => connectedComponentIn_subset _ _ hy hz) hp
    exact hsub (mem_connectedComponentIn hx)

end LatticeProb.Topology
