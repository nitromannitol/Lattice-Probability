/-
# Torhorst's theorem from simple polygonal access rays

Let `K ⊆ ℂ` be a nondegenerate locally connected continuum without cut points. If every point of the
frontier of every complementary component `C` of `K` is the limit of a simple polygonal ray with all edges
in `C`, then any two distinct frontier points of `C` are joined by a simple bi-infinite polygonal chain in
`C`, and hence the frontier of every complementary component is a simple closed curve.
-/
import LatticeProb.Topology.BiinfiniteFromAccess
import LatticeProb.Topology.BiinfiniteCrosscut

open Set Filter Topology

namespace LatticeProb.Topology

/-- **Torhorst's theorem from access rays.** If every frontier point `a` of every complementary component `C`
of a nondegenerate locally connected continuum `K ⊆ ℂ` without cut points is accessible from `C` by a simple
polygonal ray with edges in `C`, then the frontier of every complementary component of such a continuum is a
simple closed curve. -/
theorem torhorstSimpleLoop_of_access_rays
    (hAcc : ∀ K : Set ℂ, IsCompact K → IsConnected K → K.Nontrivial → IsLocallyConnectedSet K →
      (∀ x : ℂ, ¬ IsCutPoint K x) → ∀ C ∈ connectedComponentsIn Kᶜ, ∀ a ∈ frontier C,
      ∃ v : ℕ → ℂ, (∀ n, v n ≠ v (n + 1)) ∧
        (∀ n, segment ℝ (v n) (v (n + 1)) ∩ segment ℝ (v (n + 1)) (v (n + 2)) ⊆ {v (n + 1)}) ∧
        (∀ n m, n + 2 ≤ m →
          Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (v m) (v (m + 1)))) ∧
        Tendsto v atTop (𝓝 a) ∧ ∀ n, segment ℝ (v n) (v (n + 1)) ⊆ C) :
    TorhorstSimpleLoop :=
  torhorstSimpleLoop_of_simple_biinfinite_chains fun K hK hKc hKn hKlc hcut C hC a ha b hb hab => by
    have hCo : IsOpen C := isOpen_of_mem_connectedComponentsIn_compl hK.isClosed hC
    have haC : a ∉ C := by
      rw [hCo.frontier_eq] at ha
      exact ha.2
    have hbC : b ∉ C := by
      rw [hCo.frontier_eq] at hb
      exact hb.2
    obtain ⟨v, hvne, hvadj, hvfar, hva, hvC⟩ := hAcc K hK hKc hKn hKlc hcut C hC a ha
    obtain ⟨w, hwne, hwadj, hwfar, hwb, hwC⟩ := hAcc K hK hKc hKn hKlc hcut C hC b hb
    exact exists_simple_biinfinite_of_simple_rays hCo
      (isConnected_of_mem_connectedComponentsIn hC).isPreconnected hab haC hbC hvne hvadj hvfar
      hwne hwadj hwfar hva hwb hvC hwC

end LatticeProb.Topology
