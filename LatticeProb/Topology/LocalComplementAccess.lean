import LatticeProb.Topology.BoundaryAccess
import LatticeProb.Topology.EmbeddedClosedDiskExterior
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! # Local access to a complementary component -/

open Set Metric
open scoped Topology

namespace LatticeProb.Topology

/-- A point in the closure of a complementary component of a locally connected compact
plane set can be joined to that component by a compact connected set in any prescribed
open neighborhood. -/
theorem exists_local_access_continuum {K W V : Set ℂ}
    (hK : IsCompact K) (hlc : IsLocallyConnectedSet K)
    (hW : W ∈ connectedComponentsIn Kᶜ) {x : ℂ} (hx : x ∈ closure W)
    (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ (q : ℂ) (P : Set ℂ), q ∈ W ∩ V ∧ IsCompact P ∧ IsConnected P ∧
      x ∈ P ∧ q ∈ P ∧ P ⊆ V ∩ (insert x W) := by
  obtain ⟨β, hβc, hβ1, hβW⟩ := exists_access_curve_of_mem_closure hK hlc hW hx
  have hev : β ⁻¹' V ∈ 𝓝[Icc 0 1] (1 : ℝ) :=
    (hβc 1 (by norm_num)).eventually (hβ1 ▸ hV.mem_nhds hxV)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let t : ℝ := 1 - min r 1 / 2
  have ht0 : 0 ≤ t := by dsimp [t]; have := min_le_right r 1; linarith
  have ht1 : t < 1 := by dsimp [t]; have : 0 < min r 1 := lt_min hr zero_lt_one; linarith
  have htsub : Icc t 1 ⊆ ball (1 : ℝ) r ∩ Icc 0 1 := by
    intro s hs
    refine ⟨?_, ⟨le_trans ht0 hs.1, hs.2⟩⟩
    rw [mem_ball, Real.dist_eq]
    have hm : min r 1 ≤ r := min_le_left _ _
    have hslo : 1 - s ≤ min r 1 / 2 := by
      have hs0 : t ≤ s := hs.1
      dsimp [t] at hs0
      linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hs.2)]
    linarith
  refine ⟨β t, β '' Icc t 1, ⟨hβW ⟨t, ⟨ht0, ht1⟩, rfl⟩, hrsub (htsub ⟨le_rfl, le_of_lt ht1⟩)⟩,
    (isCompact_Icc.image_of_continuousOn (hβc.mono (fun s hs => (htsub hs).2))),
    (isConnected_Icc (le_of_lt ht1)).image β (hβc.mono (fun s hs => (htsub hs).2)),
    ⟨1, ⟨le_of_lt ht1, le_rfl⟩, hβ1⟩, ⟨t, ⟨le_rfl, le_of_lt ht1⟩, rfl⟩, ?_⟩
  rintro z ⟨s, hs, rfl⟩
  refine ⟨hrsub (htsub hs), ?_⟩
  rcases eq_or_lt_of_le hs.2 with heq | hlt
  · left
    simpa only [heq] using hβ1
  · right
    exact hβW ⟨s, ⟨le_trans ht0 hs.1, hlt⟩, rfl⟩

/-- A boundary point of an embedded disk outside a closed set is accessible from the
complement of their union. -/
theorem exists_embedded_disk_local_access {A B : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ A) (hB : IsClosed B)
    {x : ℂ} (hx : x ∈ frontier A) (hxB : x ∉ B) :
    ∃ (q : ℂ) (P : Set ℂ), q ∈ (A ∪ B)ᶜ ∧ IsCompact P ∧ IsConnected P ∧
      x ∈ P ∧ q ∈ P ∧ P ⊆ Bᶜ ∩ closure Aᶜ := by
  let : LocallyPathConnectedSpace (closedBall (0 : ℂ) 1) :=
    (convex_closedBall (0 : ℂ) 1).locallyPathConnectedSpace
  let : LocallyConnectedSpace A := e.isQuotientMap.isCoinducing.locallyConnectedSpace
  have hlc : IsLocallyConnectedSet A := isLocallyConnectedSet_iff_locallyConnectedSpace.mpr inferInstance
  have hcompact : IsCompact A := by
    have h := isCompact_range (continuous_subtype_val.comp e.continuous)
    have hrange : Set.range (fun z => (e z : ℂ)) = A := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact (e w).property
      · intro hz
        exact ⟨e.symm ⟨z, hz⟩, by simp⟩
    change IsCompact (Set.range (fun z => (e z : ℂ))) at h
    rwa [hrange] at h
  have hpc := (LatticeProb.complex_embedded_closed_disk_compl_preconnected_unbounded e).1
  have hxcl : x ∈ closure Aᶜ := by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  obtain ⟨y, hy⟩ := closure_nonempty_iff.mp ⟨x, hxcl⟩
  have heq : connectedComponentIn Aᶜ y = Aᶜ :=
    Subset.antisymm (connectedComponentIn_subset _ _) (hpc.subset_connectedComponentIn hy subset_rfl)
  have hW : Aᶜ ∈ connectedComponentsIn Aᶜ := ⟨y, hy, heq⟩
  obtain ⟨q, P, hq, hPcomp, hPconn, hxP, hqP, hP⟩ :=
    exists_local_access_continuum hcompact hlc hW hxcl hB.isOpen_compl hxB
  refine ⟨q, P, ?_, hPcomp, hPconn, hxP, hqP, ?_⟩
  · exact fun h => h.elim hq.1 hq.2
  · intro z hz
    obtain ⟨hzB, hzA⟩ := hP hz
    refine ⟨hzB, ?_⟩
    rcases hzA with rfl | hzA
    · exact hxcl
    · exact subset_closure hzA

end LatticeProb.Topology
