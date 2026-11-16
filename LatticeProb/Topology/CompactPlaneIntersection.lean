import LatticeProb.Topology.CompactConnectedNeighborhood
import LatticeProb.Topology.PlaneExteriorBarrier
import LatticeProb.Topology.PlaneDomainSimplyConnected
import LatticeProb.Topology.SimplyConnectedNeighborhoodLog
import LatticeProb.Topology.LogarithmicIntersection
import LatticeProb.Topology.CompactPlaneComplementConnected

/-! # Intersections of nonseparating compact plane sets -/

open Set Metric Bornology

namespace LatticeProb.Topology

/-- A compact plane set with connected complement admits exterior barriers inside any open neighborhood. -/
theorem exists_exterior_barrier {K V : Set ℂ} (hK : IsCompact K)
    (hKc : IsPreconnected Kᶜ) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ E : Set ℂ, IsClosed E ∧ IsConnected E ∧ ¬ IsBounded E ∧
      Disjoint K E ∧ Vᶜ ⊆ E := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  let P : Set ℂ := {z | R < ‖z‖}
  let Q := closure P
  let p : ℂ := ((|R| + 1 : ℝ) : ℂ)
  have hpP : p ∈ P := by
    dsimp [p, P]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (le_abs_self R).trans_lt ((lt_add_one _).trans_le (le_abs_self _))
  have hPc : IsPreconnected P := QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R
  have hPu : ¬ IsBounded P := LatticeProb.Janiszewski.not_isBounded_setOf_lt_norm R
  have hQc : IsConnected Q := ⟨⟨p, subset_closure hpP⟩, hPc.closure⟩
  have hQK : Q ⊆ Kᶜ := by
    apply (closure_minimal ?_ isOpen_ball.isClosed_compl).trans (compl_subset_compl.mpr hR)
    intro z hz hzb
    have : ‖z‖ < R := by simpa only [mem_ball_zero_iff] using hzb
    exact (not_lt_of_ge this.le) hz
  have hKne : (Kᶜ).Nonempty := ⟨p, hQK (subset_closure hpP)⟩
  let S := Vᶜ ∩ closedBall (0 : ℂ) R
  have hSc : IsCompact S := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    (hV.isClosed_compl.inter isClosed_closedBall) inter_subset_right
  have hSK : S ⊆ Kᶜ := fun _ hx hk => hx.1 (hKV hk)
  obtain ⟨T, hTc, hTconn, hST, hpT, hTK⟩ :=
    exists_compact_connected_superset hK.isClosed.isOpen_compl ⟨hKne, hKc⟩
      (hQK (subset_closure hpP)) hSc hSK
  refine ⟨Q ∪ T, isClosed_closure.union hTc.isClosed,
    hQc.union ⟨p, subset_closure hpP, hpT⟩ hTconn, ?_, ?_, ?_⟩
  · intro h
    exact hPu (h.subset (subset_closure.trans subset_union_left))
  · apply disjoint_left.mpr
    intro x hx hxe
    rcases hxe with hxq | hxt
    · exact hQK hxq hx
    · exact hTK hxt hx
  · intro x hx
    by_cases hxball : x ∈ closedBall (0 : ℂ) R
    · exact Or.inr (hST ⟨hx, hxball⟩)
    · apply Or.inl
      apply subset_closure
      have : ¬ ‖x‖ ≤ R := by simpa only [mem_closedBall_zero_iff] using hxball
      exact lt_of_not_ge this

/-- Compact plane continua with connected complement have a basis of simply connected domains. -/
theorem exists_simplyConnected_nhds_of_compl_preconnected {K V : Set ℂ}
    (hK : IsCompact K) (hKc : IsConnected K) (hKcom : IsPreconnected Kᶜ)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ U ⊆ V ∧ IsSimplyConnected U := by
  obtain ⟨E, hE, hEc, hEu, hKE, hVE⟩ := exists_exterior_barrier hK hKcom hV hKV
  obtain ⟨U, hKU, hUV, hUo, hUc, _, hUu, hcomp⟩ :=
    exists_domain_of_compact_exterior_barrier hK hKc hE hEc hEu hKE hVE
  have hUp : U ≠ univ := by
    intro h
    rw [h, compl_univ] at hUu
    exact hUu isBounded_empty
  exact ⟨U, hUo, hKU, hUV,
    isSimplyConnected_of_unbounded_compl_components hUo hUc.isPreconnected hUc.nonempty hUp hcomp⟩

/-- Two compact plane continua have preconnected intersection if their union has connected complement. -/
theorem isPreconnected_inter_of_compl_union_preconnected {A B : Set ℂ}
    (hA : IsCompact A) (hB : IsCompact B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hcom : IsPreconnected (A ∪ B)ᶜ) : IsPreconnected (A ∩ B) := by
  by_cases hAB : (A ∩ B).Nonempty
  · have hKc : IsConnected (A ∪ B) := hAc.union hAB hBc
    apply isPreconnected_inter_of_hasLogOn_union hA.isClosed hB.isClosed
      hAc.isPreconnected hBc.isPreconnected
    intro f hf hf0
    apply exists_continuousOn_exp_eq_of_simplyConnected_nhds (hA.union hB).isClosed ?_ hf hf0
    intro V hV hKV
    exact exists_simplyConnected_nhds_of_compl_preconnected (hA.union hB) hKc hcom hV hKV
  · rw [not_nonempty_iff_eq_empty.mp hAB]
    exact isPreconnected_empty

/-- If the union has no bounded complementary components, the intersection has at most one component. -/
theorem cardinal_inter_components_le_one_of_no_bounded_compl {A B : Set ℂ}
    (hA : IsCompact A) (hB : IsCompact B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hcom : IsEmpty (BoundedPlaneComplementComponent (A ∪ B))) :
    Cardinal.mk (ConnectedComponents ↥(A ∩ B)) ≤ 1 := by
  have h := isPreconnected_inter_of_compl_union_preconnected hA hB hAc hBc
    (isPreconnected_compl_of_no_bounded_components (hA.union hB) hcom)
  let : PreconnectedSpace ↥(A ∩ B) := isPreconnected_iff_preconnectedSpace.mp h
  exact Cardinal.le_one_iff_subsingleton.mpr inferInstance

end LatticeProb.Topology
