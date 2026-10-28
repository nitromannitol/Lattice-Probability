import LatticeProb.Prob.Percolation.LatticeBoxGeometry

/-!
# Connected families of local crossing components

Local crossing components in adjacent AP boxes glue inside a common finite
ambient region. Connectedness of the actual center graph propagates the gluing.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ} [NeZero d]

/-- In a finite region, a connected nonempty family of good AP boxes has a single
ambient open component containing every local outer crossing component. -/
theorem ap_connected_family_backbone
    (ω : Configuration d) (N : {n : ℕ // 0 < n}) (S Q : Finset (Vertex d))
    (hS : S.Nonempty)
    (hconnected : ((nearestNeighborGraph d).induce (S : Set (Vertex d))).Connected)
    (hQ : ∀ c ∈ S, apOuter c N ⊆ Q)
    (hp : ∀ c ∈ S,
      apProjectedProperty c N ((openGraph ω).induce (apOuter c N : Set (Vertex d)))) :
    ∃ H : ((openGraph ω).induce (Q : Set (Vertex d))).ConnectedComponent,
      ∀ c, ∀ hc : c ∈ S,
        ∃ C : ((openGraph ω).induce (apOuter c N : Set (Vertex d))).ConnectedComponent,
          latticeCubeComponentCrosses (fun i => (c i : ℝ))
            ⟨5 * (N.val : ℝ) / 4, by
              simp only [Set.mem_Ioi]
              have hn : (0 : ℝ) < N.val := by exact_mod_cast N.property
              positivity⟩ ((openGraph ω).induce (apOuter c N : Set (Vertex d))) C ∧
          ∀ D : ((openGraph ω).induce (apOuter c N : Set (Vertex d))).ConnectedComponent,
            latticeCubeComponentCrosses (fun i => (c i : ℝ))
              ⟨5 * (N.val : ℝ) / 4, by
                simp only [Set.mem_Ioi]
                have hn : (0 : ℝ) < N.val := by exact_mod_cast N.property
                positivity⟩ ((openGraph ω).induce (apOuter c N : Set (Vertex d))) D →
            ∀ x : {z : Vertex d // z ∈ apOuter c N}, x ∈ D.supp →
              (⟨x.val, hQ c hc x.property⟩ : {z : Vertex d // z ∈ Q}) ∈ H.supp := by
  classical
  let GQ := (openGraph ω).induce (Q : Set (Vertex d))
  let localGraph (c : {z : Vertex d // z ∈ S}) :=
    (openGraph ω).induce (apOuter c.val N : Set (Vertex d))
  let lift (c : {z : Vertex d // z ∈ S}) : localGraph c →g GQ :=
    ((openGraph ω).induceHomOfLE (by
      intro z hz
      exact hQ c.val c.property hz)).toHom
  let selected (c : {z : Vertex d // z ∈ S}) : (localGraph c).ConnectedComponent :=
    Classical.choose (hp c.val c.property)
  have selected_spec (c : {z : Vertex d // z ∈ S}) :=
    Classical.choose_spec (hp c.val c.property)
  let target (c : {z : Vertex d // z ∈ S}) : GQ.ConnectedComponent :=
    (selected c).map (lift c)
  have map_mem (c : {z : Vertex d // z ∈ S}) (C : (localGraph c).ConnectedComponent)
      (x : {z : Vertex d // z ∈ apOuter c.val N}) (hx : x ∈ C.supp) :
      lift c x ∈ (C.map (lift c)).supp := by
    change GQ.connectedComponentMk (lift c x) = C.map (lift c)
    have heq : (localGraph c).connectedComponentMk x = C := hx
    rw [← heq]
    rfl
  have step (c c' : {z : Vertex d // z ∈ S})
      (hadj : ((nearestNeighborGraph d).induce (S : Set (Vertex d))).Adj c c') :
      target c = target c' := by
    change (nearestNeighborGraph d).Adj c.val c'.val at hadj
    let q : Vertex d := fun i => max (c.val i) (c'.val i) - N.val
    have hinner := apInner_common_outer_of_adj c.val c'.val N hadj
    change apInner q N ⊆ apOuter c.val N ∧ apInner q N ⊆ apOuter c'.val N at hinner
    obtain ⟨A, B, hA, hB, z, hzA, hzB, hzCA, hzCB⟩ :=
      ap_projected_components_intersect ω c.val c'.val q N hinner.1 hinner.2
        (hp c.val c.property) (hp c'.val c'.property)
    have heqA : A = selected c := (selected_spec c).2.1 A hA
    have heqB : B = selected c' := (selected_spec c').2.1 B hB
    have hzselA : (⟨z, hzA⟩ : {z : Vertex d // z ∈ apOuter c.val N}) ∈
        (selected c).supp := by rw [← heqA]; exact hzCA
    have hzselB : (⟨z, hzB⟩ : {z : Vertex d // z ∈ apOuter c'.val N}) ∈
        (selected c').supp := by rw [← heqB]; exact hzCB
    have ha := map_mem c (selected c) ⟨z, hzA⟩ hzselA
    have hb := map_mem c' (selected c') ⟨z, hzB⟩ hzselB
    have ha' : (⟨z, hQ c.val c.property hzA⟩ : {z : Vertex d // z ∈ Q}) ∈
        (target c).supp := ha
    have hb' : (⟨z, hQ c.val c.property hzA⟩ : {z : Vertex d // z ∈ Q}) ∈
        (target c').supp := hb
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex ha' hb'
  have all_eq (c c' : {z : Vertex d // z ∈ S}) : target c = target c' := by
    obtain ⟨w⟩ := hconnected.preconnected c c'
    induction w with
    | nil => rfl
    | cons h w ih => exact (step _ _ h).trans ih
  obtain ⟨c₀, hc₀⟩ := hS
  let c0 : {z : Vertex d // z ∈ S} := ⟨c₀, hc₀⟩
  refine ⟨target c0, ?_⟩
  intro c hc
  let t : {z : Vertex d // z ∈ S} := ⟨c, hc⟩
  refine ⟨selected t, (selected_spec t).1, ?_⟩
  intro D hD x hx
  have heq : D = selected t := (selected_spec t).2.1 D hD
  have hxs : x ∈ (selected t).supp := heq ▸ hx
  have hm : lift t x ∈ (target t).supp := map_mem t (selected t) x hxs
  have ht : target t = target c0 := all_eq t c0
  rw [ht] at hm
  exact hm

end
end LatticeProb.Percolation
