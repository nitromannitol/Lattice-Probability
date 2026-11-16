import LatticeProb.Topology.DirectedCompactConnected
import Mathlib.Order.Zorn

/-! # Minimal continua between points -/

open Set

namespace LatticeProb.Topology

/-- A compact preconnected set contains a minimal compact preconnected subset
containing any two prescribed points. -/
theorem exists_minimal_compact_preconnected_between_points
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    {K : Set X} {a b : X} (hK : IsCompact K) (hconn : IsPreconnected K)
    (ha : a ∈ K) (hb : b ∈ K) :
    ∃ M : Set X, M ⊆ K ∧ IsCompact M ∧ IsPreconnected M ∧ a ∈ M ∧ b ∈ M ∧
      ∀ N : Set X, IsCompact N → IsPreconnected N → N ⊆ M →
        a ∈ N → b ∈ N → N = M := by
  classical
  let S : Set (Set X) := {N | N ⊆ K ∧ IsCompact N ∧ IsPreconnected N ∧ a ∈ N ∧ b ∈ N}
  have hKS : K ∈ S := ⟨Subset.rfl, hK, hconn, ha, hb⟩
  obtain ⟨M, _, hmin⟩ := zorn_superset_nonempty S (fun c hcS hc hne => by
    let ι := c
    have : Nonempty ι := hne.to_subtype
    let F : ι → Set X := fun i => i.1
    have hFc (i : ι) : IsCompact (F i) := (hcS i.2).2.1
    have hFp (i : ι) : IsPreconnected (F i) := (hcS i.2).2.2.1
    have hdir : Directed (· ⊇ ·) F := by
      intro i j
      obtain hij | hji := hc.total i.2 j.2
      · exact ⟨i, Subset.rfl, hij⟩
      · exact ⟨j, hji, Subset.rfl⟩
    let I := ⋂ i, F i
    have hIp : IsPreconnected I := isPreconnected_iInter_of_directed_isCompact hdir hFc hFp
    have hIclosed : IsClosed I := isClosed_iInter fun i => (hFc i).isClosed
    let i₀ : ι := Classical.choice inferInstance
    have hIsub : I ⊆ F i₀ := iInter_subset F i₀
    have hIc : IsCompact I := (hFc i₀).of_isClosed_subset hIclosed hIsub
    have hIK : I ⊆ K := hIsub.trans (hcS i₀.2).1
    have haI : a ∈ I := mem_iInter.mpr fun i => (hcS i.2).2.2.2.1
    have hbI : b ∈ I := mem_iInter.mpr fun i => (hcS i.2).2.2.2.2
    refine ⟨I, ⟨hIK, hIc, hIp, haI, hbI⟩, ?_⟩
    intro N hNc
    exact iInter_subset F ⟨N, hNc⟩) K hKS
  refine ⟨M, hmin.prop.1, hmin.prop.2.1, hmin.prop.2.2.1,
    hmin.prop.2.2.2.1, hmin.prop.2.2.2.2, ?_⟩
  intro N hNc hNp hNM haN hbN
  exact (hmin.eq_of_ge ⟨hNM.trans hmin.prop.1, hNc, hNp, haN, hbN⟩ hNM).symm

end LatticeProb.Topology
