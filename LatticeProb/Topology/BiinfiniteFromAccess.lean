/-
# A simple bi-infinite polygonal chain from two access rays

In an open connected planar set `C`, two simple polygonal rays with edges in `C`, tending to distinct points
`a` and `b` outside `C`, can be combined with a polygonal chain in `C` into a simple bi-infinite polygonal
chain in `C` from `a` to `b`.
-/
import LatticeProb.Topology.BiinfiniteFromRays
import LatticeProb.Topology.PolygonalRayTail
import LatticeProb.Topology.PolygonalContact
import LatticeProb.Topology.PolygonalRayCompact

open Set Filter Topology

namespace LatticeProb.Topology

/-- **Two access rays give a simple bi-infinite chain.** Let `C ⊆ ℂ` be open and connected and let
`a ≠ b` be points outside `C`. If simple polygonal rays `v → a` and `w → b` have all their edges in
`C`, then there is a simple bi-infinite polygonal chain `u : ℤ → ℂ` with all edges in `C`, tending
to `a` at `-∞` and to `b` at `+∞`, with neither `a` nor `b` on any edge.

The tails of the two rays beyond suitable indices lie in disjoint balls around `a` and `b`; their
closures `A ∋ a` and `B ∋ b` are compact. A polygonal chain in `C` from the first tail to the
second is cut at its last contact `s` with `A` and then at its first contact `t` with `B`, and its
loops are removed. The ray from `s` along the `a`-tail and the chain from `s` to `t` followed by
the ray from `t` along the `b`-tail meet only at `s`; gluing them gives `u`. -/
theorem exists_simple_biinfinite_of_simple_rays {C : Set ℂ} (hC : IsOpen C)
    (hconn : IsPreconnected C) {a b : ℂ} (hab : a ≠ b) (haC : a ∉ C) (hbC : b ∉ C)
    {v w : ℕ → ℂ} (hvne : ∀ n, v n ≠ v (n + 1))
    (hvadj : ∀ n, segment ℝ (v n) (v (n + 1)) ∩ segment ℝ (v (n + 1)) (v (n + 2)) ⊆ {v (n + 1)})
    (hvfar : ∀ n m, n + 2 ≤ m →
      Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (v m) (v (m + 1))))
    (hwne : ∀ n, w n ≠ w (n + 1))
    (hwadj : ∀ n, segment ℝ (w n) (w (n + 1)) ∩ segment ℝ (w (n + 1)) (w (n + 2)) ⊆ {w (n + 1)})
    (hwfar : ∀ n m, n + 2 ≤ m →
      Disjoint (segment ℝ (w n) (w (n + 1))) (segment ℝ (w m) (w (m + 1))))
    (hva : Tendsto v atTop (𝓝 a)) (hwb : Tendsto w atTop (𝓝 b))
    (hvC : ∀ n, segment ℝ (v n) (v (n + 1)) ⊆ C) (hwC : ∀ n, segment ℝ (w n) (w (n + 1)) ⊆ C) :
    ∃ u : ℤ → ℂ, (∀ n, u n ≠ u (n + 1)) ∧
      (∀ n, segment ℝ (u n) (u (n + 1)) ∩ segment ℝ (u (n + 1)) (u (n + 2)) ⊆ {u (n + 1)}) ∧
      (∀ n m : ℤ, n + 2 ≤ m →
        Disjoint (segment ℝ (u n) (u (n + 1))) (segment ℝ (u m) (u (m + 1)))) ∧
      Tendsto u atBot (𝓝 a) ∧ Tendsto u atTop (𝓝 b) ∧
      (∀ n, a ∉ segment ℝ (u n) (u (n + 1))) ∧ (∀ n, b ∉ segment ℝ (u n) (u (n + 1))) ∧
      ∀ n, segment ℝ (u n) (u (n + 1)) ⊆ C := by
  -- Step 1: tails in disjoint balls, with compact closures `A` and `B`.
  set ε : ℝ := dist a b / 2 with hε_def
  have hε : 0 < ε := half_pos (dist_pos.mpr hab)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hva.eventually (Metric.ball_mem_nhds a hε))
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hwb.eventually (Metric.ball_mem_nhds b hε))
  set A : Set ℂ := insert a (⋃ n, segment ℝ (v (n + N)) (v (n + 1 + N))) with hA_def
  set B : Set ℂ := insert b (⋃ n, segment ℝ (w (n + M)) (w (n + 1 + M))) with hB_def
  have hAc : IsCompact A :=
    isCompact_insert_iUnion_segment (v := fun n => v (n + N))
      ((tendsto_add_atTop_iff_nat N).mpr hva)
  have hBc : IsCompact B :=
    isCompact_insert_iUnion_segment (v := fun n => w (n + M))
      ((tendsto_add_atTop_iff_nat M).mpr hwb)
  have hAball : A ⊆ Metric.ball a ε := by
    refine insert_subset (Metric.mem_ball_self hε) (iUnion_subset fun n => ?_)
    exact (convex_ball a ε).segment_subset (hN _ (by omega)) (hN _ (by omega))
  have hBball : B ⊆ Metric.ball b ε := by
    refine insert_subset (Metric.mem_ball_self hε) (iUnion_subset fun n => ?_)
    exact (convex_ball b ε).segment_subset (hM _ (by omega)) (hM _ (by omega))
  have hAB : Disjoint A B :=
    (Metric.ball_disjoint_ball (by rw [hε_def]; linarith)).mono hAball hBball
  have hvA : ∀ m, N ≤ m → segment ℝ (v m) (v (m + 1)) ⊆ A := fun m hm z hz =>
    mem_insert_of_mem _ (mem_iUnion.mpr ⟨m - N, by
      rw [show m - N + N = m by omega, show m - N + 1 + N = m + 1 by omega]; exact hz⟩)
  have hwB : ∀ m, M ≤ m → segment ℝ (w m) (w (m + 1)) ⊆ B := fun m hm z hz =>
    mem_insert_of_mem _ (mem_iUnion.mpr ⟨m - M, by
      rw [show m - M + M = m by omega, show m - M + 1 + M = m + 1 by omega]; exact hz⟩)
  -- Step 2: a polygonal chain in `C` from the `a`-tail to the `b`-tail.
  have hvN : v N ∈ C := hvC N (left_mem_segment ℝ _ _)
  have hwM : w M ∈ C := hwC M (left_mem_segment ℝ _ _)
  obtain ⟨γ0, h0, hγ0C, hγ0head, hγ0last⟩ :=
    exists_polygonal_chain_of_isPreconnected hC hconn hvN hwM
  -- Step 3: last contact with `A`, first contact with `B`, loop removal.
  obtain ⟨s, hsA, ws1, hw1, hw1head, hw1last, hw1sub, hw1A⟩ :=
    exists_suffix_inter_eq_singleton hAc.isClosed h0
      ⟨v N, hγ0head ▸ head_mem_polygonal_chain h0, hvA N le_rfl (left_mem_segment ℝ _ _)⟩
  have hwM1 : w M ∈ polygonalChain ws1 := by
    have h := getLast_mem_polygonal_chain hw1
    rwa [hw1last, hγ0last] at h
  obtain ⟨t, htB, ws2, hw2, hw2head, hw2last, hw2sub, hw2B⟩ :=
    exists_prefix_inter_eq_singleton hBc.isClosed hw1
      ⟨w M, hwM1, hwB M le_rfl (left_mem_segment ℝ _ _)⟩
  obtain ⟨γ, hγne, hγs, hγhead, hγlast, hγsub⟩ := exists_simple_polygonal_chain ws2 hw2
  have hγC : polygonalChain γ ⊆ C := hγsub.trans (hw2sub.trans (hw1sub.trans hγ0C))
  have hγA : polygonalChain γ ∩ A ⊆ {s} := fun z hz =>
    hw1A.subset ⟨hw2sub (hγsub hz.1), hz.2⟩
  have hγB : polygonalChain γ ∩ B ⊆ {t} := fun z hz => hw2B.subset ⟨hγsub hz.1, hz.2⟩
  have hγh : γ.head hγne = s := by rw [hγhead, hw2head, hw1head]
  have hγl : γ.getLast hγne = t := by rw [hγlast, hw2last]
  have hsC : s ∈ C := hγC (hγh ▸ head_mem_polygonal_chain hγne)
  have htC : t ∈ C := hγC (hγl ▸ getLast_mem_polygonal_chain hγne)
  -- Step 4: rays from `s` along the `a`-tail and from `t` along the `b`-tail.
  have hs' : s ∈ ⋃ n, segment ℝ (v (n + N)) (v (n + 1 + N)) :=
    (mem_insert_iff.mp hsA).resolve_left fun h => haC (h ▸ hsC)
  obtain ⟨k0, hk0⟩ := mem_iUnion.mp hs'
  rw [show k0 + 1 + N = k0 + N + 1 by omega] at hk0
  obtain ⟨ra, ja, -, hra0, hras, hrane, hraadj, hrafar, hratr⟩ :=
    exists_simple_ray_tail hvne hvadj hvfar hk0
  have ht' : t ∈ ⋃ n, segment ℝ (w (n + M)) (w (n + 1 + M)) :=
    (mem_insert_iff.mp htB).resolve_left fun h => hbC (h ▸ htC)
  obtain ⟨k1, hk1⟩ := mem_iUnion.mp ht'
  rw [show k1 + 1 + M = k1 + M + 1 by omega] at hk1
  obtain ⟨rb, jb, -, hrb0, hrbs, hrbne, hrbadj, hrbfar, hrbtr⟩ :=
    exists_simple_ray_tail hwne hwadj hwfar hk1
  have hraA : (⋃ n, segment ℝ (ra n) (ra (n + 1))) ⊆ A := fun z hz => by
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hratr hz)
    exact hvA _ (by omega) hn
  have hraC : (⋃ n, segment ℝ (ra n) (ra (n + 1))) ⊆ C := fun z hz => by
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hratr hz)
    exact hvC _ hn
  have hrbB : (⋃ n, segment ℝ (rb n) (rb (n + 1))) ⊆ B := fun z hz => by
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hrbtr hz)
    exact hwB _ (by omega) hn
  have hrbC : (⋃ n, segment ℝ (rb n) (rb (n + 1))) ⊆ C := fun z hz => by
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hrbtr hz)
    exact hwC _ hn
  have hra_lim : Tendsto ra atTop (𝓝 a) := by
    refine (tendsto_add_atTop_iff_nat 1).mp ?_
    simp only [hras]
    exact (tendsto_add_atTop_iff_nat (ja + 1)).mpr hva
  have hrb_lim : Tendsto rb atTop (𝓝 b) := by
    refine (tendsto_add_atTop_iff_nat 1).mp ?_
    simp only [hrbs]
    exact (tendsto_add_atTop_iff_nat (jb + 1)).mpr hwb
  -- Step 5: the simple chain from `s` to `t` followed by the ray from `t`.
  obtain ⟨rc, k, hrc0, hrck, hrcne, hrcadj, hrcfar, hrctr⟩ :=
    exists_simple_ray_of_simplePolygonalChain hrbne hrbadj hrbfar hγs
      (by rw [hrb0]; exact hγl)
      (fun z hz => by rw [hrb0]; exact hγB ⟨hz.1, hrbB hz.2⟩)
  have hrc_lim : Tendsto rc atTop (𝓝 b) := by
    refine (tendsto_add_atTop_iff_nat k).mp ?_
    simp only [hrck]
    exact hrb_lim
  have hrcC : (⋃ n, segment ℝ (rc n) (rc (n + 1))) ⊆ C := by
    rw [hrctr]
    exact union_subset hγC hrbC
  -- Step 6: the two rays from `s` meet only at `s`.
  have h0' : ra 0 = rc 0 := by
    rw [hra0, hrc0]
    exact hγh.symm
  obtain ⟨hjoin, hcross⟩ :=
    disjoint_segments_of_simple_rays h0' hrane hrcne hraadj hrcadj hrafar hrcfar
      (fun z hz => by
        rw [hrctr] at hz
        obtain ⟨hz1, hz2 | hz2⟩ := hz
        · rw [hra0]
          exact hγA ⟨hz2, hraA hz1⟩
        · exact absurd (hrbB hz2) (disjoint_left.mp hAB (hraA hz1)))
  -- Step 7: glue the two rays.
  have hseg_ra : ∀ n, segment ℝ (ra n) (ra (n + 1)) ⊆ C := fun n =>
    (subset_iUnion (fun n => segment ℝ (ra n) (ra (n + 1))) n).trans hraC
  have hseg_rc : ∀ n, segment ℝ (rc n) (rc (n + 1)) ⊆ C := fun n =>
    (subset_iUnion (fun n => segment ℝ (rc n) (rc (n + 1))) n).trans hrcC
  obtain ⟨u, hune, huadj, hufar, hua, hub, hauγ, hbuγ, hutr⟩ :=
    exists_biinfinite_of_two_rays h0' hrane hrcne hraadj hrcadj hrafar hrcfar hjoin hcross
      hra_lim hrc_lim (fun n h => haC (hseg_ra n h)) (fun n h => haC (hseg_rc n h))
      (fun n h => hbC (hseg_ra n h)) (fun n h => hbC (hseg_rc n h))
  refine ⟨u, hune, huadj, hufar, hua, hub, hauγ, hbuγ, fun n => ?_⟩
  refine (subset_iUnion (fun n : ℤ => segment ℝ (u n) (u (n + 1))) n).trans ?_
  rw [hutr]
  exact union_subset hraC hrcC

end LatticeProb.Topology
