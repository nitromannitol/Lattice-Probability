import LatticeProb.Topology.PlaneTopology

/-!
# Locally connected plane sets and uniform local connectedness

* `isLocallyConnectedSet_iff_locallyConnectedSpace`: a set `X ⊆ ℂ` is locally connected in the sense of relative
  neighbourhoods (`IsLocallyConnectedSet`) iff the subspace `X` is a locally connected space.
* `IsLocallyConnectedSet.uniformly_locallyConnected`: a compact locally connected set `K ⊆ ℂ` is uniformly locally
  connected: for every `ε > 0` there is `δ > 0` such that any two points of `K` at distance less than `δ` lie in a
  compact connected subset of `K` of diameter less than `ε` (Whyburn, *Analytic Topology*, Chapter I; Kuratowski,
  *Topology* II, §50).
-/

namespace LatticeProb.Topology

open Set Metric
open scoped _root_.Topology

/-- The relative-neighbourhood notion of local connectedness of a subset of `ℂ` agrees with local connectedness of
the subspace. -/
theorem isLocallyConnectedSet_iff_locallyConnectedSpace {X : Set ℂ} :
    IsLocallyConnectedSet X ↔ LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  constructor
  · intro H x U hU
    obtain ⟨V', hV'n, hV'sub, hV'c⟩ := H x x.2 _ (mem_nhds_subtype_iff_nhdsWithin.1 hU)
    refine ⟨(↑) ⁻¹' V', preimage_coe_mem_nhds_subtype.2 hV'n, ?_, ?_⟩
    · rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
        inter_eq_right.2 (hV'sub.trans inter_subset_right)]
      exact hV'c.isPreconnected
    · intro y hy
      obtain ⟨u, hu, huy⟩ := (hV'sub hy).1
      rwa [Subtype.val_injective huy] at hu
  · intro H x hx N hN
    obtain ⟨V, hVn, hVc, hVU⟩ := H ⟨x, hx⟩ _ (preimage_coe_mem_nhds_subtype.2 hN)
    refine ⟨(↑) '' V, mem_nhds_subtype_iff_nhdsWithin.1 hVn, ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨hVU hv, v.2⟩
    · exact ⟨⟨x, ⟨x, hx⟩, mem_of_mem_nhds hVn, rfl⟩,
        hVc.image _ continuous_subtype_val.continuousOn⟩

/-- **Uniform local connectedness.** In a compact locally connected set `K ⊆ ℂ`, for every `ε > 0` there is `δ > 0`
such that any two points of `K` at distance less than `δ` lie in a compact connected subset of `K` of diameter less
than `ε`. -/
theorem IsLocallyConnectedSet.uniformly_locallyConnected {K : Set ℂ} (hK : IsCompact K)
    (hlc : IsLocallyConnectedSet K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
      ∃ L ⊆ K, IsCompact L ∧ IsConnected L ∧ x ∈ L ∧ y ∈ L ∧ diam L < ε := by
  have hε4 : 0 < ε / 4 := by positivity
  have hloc : ∀ z ∈ K, ∃ r > 0, ∃ V : Set ℂ, IsConnected V ∧ V ⊆ ball z (ε / 4) ∩ K ∧ ball z r ∩ K ⊆ V := by
    intro z hz
    obtain ⟨V, hVn, hVsub, hVc⟩ := hlc z hz _ (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z hε4))
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhdsWithin_iff.1 hVn
    exact ⟨r, hr, V, hVc, hVsub, hrV⟩
  choose! r hr V hVc hVsub hrV using hloc
  obtain ⟨δ, hδ, hcov⟩ := lebesgue_number_lemma_of_metric (c := fun i : K => ball (i : ℂ) (r i)) hK
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hr x hx)⟩)
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  obtain ⟨⟨z, hz⟩, hball⟩ := hcov x hx
  have hxV : x ∈ V z := hrV z hz ⟨hball (mem_ball_self hδ), hx⟩
  have hyV : y ∈ V z := hrV z hz ⟨hball (mem_ball'.2 hxy), hy⟩
  have hVK : V z ⊆ K := (hVsub z hz).trans inter_subset_right
  have hcl : closure (V z) ⊆ closedBall z (ε / 4) :=
    closure_minimal ((hVsub z hz).trans (inter_subset_left.trans ball_subset_closedBall)) isClosed_closedBall
  refine ⟨closure (V z), closure_minimal hVK hK.isClosed, hK.of_isClosed_subset isClosed_closure
    (closure_minimal hVK hK.isClosed), (hVc z hz).closure, subset_closure hxV, subset_closure hyV, ?_⟩
  calc diam (closure (V z)) ≤ diam (closedBall z (ε / 4)) := diam_mono hcl isBounded_closedBall
    _ ≤ 2 * (ε / 4) := diam_closedBall hε4.le
    _ < ε := by linarith

end LatticeProb.Topology
