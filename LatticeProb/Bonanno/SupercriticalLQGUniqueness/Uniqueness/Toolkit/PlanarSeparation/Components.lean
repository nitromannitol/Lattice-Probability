/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.Components at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PathHit
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoEilenberg
import LatticeProb.Bonanno.LQGMetric.Field.GreenFnSquare




 
set_option autoImplicit false
noncomputable section
open Set Metric
namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

theorem annular_component_bounds {K : Set ℂ} {z : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hK : IsCompact K)
    (hann : K ⊆ {w | r < dist w z ∧ dist w z < R})
    (hsep : LQGMetric.Disconnects K (sphere z r) (sphere z R)) :
    closedBall z r ⊆ connectedComponentIn Kᶜ z ∧
      connectedComponentIn Kᶜ z ⊆ ball z R := by
  have hinner : closedBall z r ⊆ Kᶜ := by
    intro w hw hwK
    have hwr : dist w z ≤ r := by simpa only [mem_closedBall] using hw
    exact (not_lt_of_ge hwr) (hann hwK).1
  have hzinner : z ∈ closedBall z r := by simp [hr.le]
  have hzin : z ∈ Kᶜ := hinner hzinner
  constructor
  · exact (convex_closedBall z r).isPreconnected.subset_connectedComponentIn
      hzinner hinner
  · intro w hw
    by_contra hnot
    have hwout : w ∈ (ball z R)ᶜ := hnot
    have h := not_mem_component_of_disconnects hK.isClosed
      (LQGMetric.Disconnects.closedBall_compl_ball hrR.le hsep) hzinner hwout
    exact h hw

 
theorem candidate_annulus_subset_radii
    (A : SupercriticalLQGUniqueness.EuclideanAnnulus) :
    A.toSet ⊆ {w | A.innerRadius < dist w A.center ∧
      dist w A.center < A.outerRadius} := by
  intro w hw
  change w ∈ ball A.center A.outerRadius \ closure (ball A.center A.innerRadius) at hw
  have hnr : ¬ dist w A.center ≤ A.innerRadius := by
    intro hle
    have hr : A.innerRadius ≠ 0 := ne_of_gt A.2.1
    exact hw.2 (by rw [closure_ball A.center hr]; exact hle)
  exact ⟨lt_of_not_ge hnr, hw.1⟩

 
theorem bounded_component_subset_ball_of_compact {K : Set ℂ} {x : ℂ} {M : ℝ}
    (hK : IsCompact K) (hKM : K ⊆ closedBall 0 M) (hM : 0 ≤ M)
    (hV : Bornology.IsBounded (connectedComponentIn Kᶜ x)) :
    connectedComponentIn Kᶜ x ⊆ ball 0 M := by
  have hclosed : connectedComponentIn Kᶜ x ⊆ closedBall 0 M := by
    intro z hz
    by_contra hzM
    have hzU : z ∉ closedBall (0 : ℂ) M := hzM
    have hunb : ¬ Bornology.IsBounded
        (connectedComponentIn (closedBall (0 : ℂ) M)ᶜ z) :=
      LQGMetric.not_isBounded_connectedComponentIn_compl_of_convex
        (convex_closedBall 0 M) (mem_closedBall_self hM) hzU
    have hsub : connectedComponentIn (closedBall (0 : ℂ) M)ᶜ z ⊆
        connectedComponentIn Kᶜ x := by
      have hmono := connectedComponentIn_mono z (compl_subset_compl.mpr hKM)
      rw [← connectedComponentIn_eq hz] at hmono
      exact hmono
    exact hunb (hV.subset hsub)
  have hVo : IsOpen (connectedComponentIn Kᶜ x) :=
    hK.isClosed.isOpen_compl.connectedComponentIn
  intro z hz
  have hzi : z ∈ interior (closedBall (0 : ℂ) M) :=
    (interior_maximal hclosed hVo) hz
  simpa only [interior_closedBall'] using hzi

theorem not_mutual_enclosure {K₁ K₂ : Set ℂ} {x₁ x₂ : ℂ}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty)
    (hb₁ : Bornology.IsBounded (connectedComponentIn K₁ᶜ x₁))
    (hb₂ : Bornology.IsBounded (connectedComponentIn K₂ᶜ x₂)) :
    ¬ (K₂ ⊆ connectedComponentIn K₁ᶜ x₁ ∧ K₁ ⊆ connectedComponentIn K₂ᶜ x₂) := by
  rintro ⟨h₂in₁, h₁in₂⟩
  obtain ⟨a, ha, hmax₁⟩ := hK₁.exists_isMaxOn hne₁ continuous_norm.continuousOn
  obtain ⟨b, hb, hmax₂⟩ := hK₂.exists_isMaxOn hne₂ continuous_norm.continuousOn
  have hK₁ball : K₁ ⊆ closedBall 0 ‖a‖ := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    exact hmax₁ hw
  have hK₂ball : K₂ ⊆ closedBall 0 ‖b‖ := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    exact hmax₂ hw
  have hlt₁ : ‖b‖ < ‖a‖ := by
    have := bounded_component_subset_ball_of_compact hK₁ hK₁ball (norm_nonneg a) hb₁
      (h₂in₁ hb)
    simpa only [mem_ball_zero_iff] using this
  have hlt₂ : ‖a‖ < ‖b‖ := by
    have := bounded_component_subset_ball_of_compact hK₂ hK₂ball (norm_nonneg b) hb₂
      (h₁in₂ ha)
    simpa only [mem_ball_zero_iff] using this
  exact (lt_asymm hlt₁ hlt₂)

 
theorem bounded_complementary_components_noncrossing
    {K₁ K₂ : Set ℂ} {x₁ x₂ : ℂ}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hc₁ : IsConnected K₁) (hc₂ : IsConnected K₂)
    (hdisj : Disjoint K₁ K₂)
    (hb₁ : Bornology.IsBounded (connectedComponentIn K₁ᶜ x₁))
    (hb₂ : Bornology.IsBounded (connectedComponentIn K₂ᶜ x₂)) :
    Disjoint (connectedComponentIn K₁ᶜ x₁) (connectedComponentIn K₂ᶜ x₂) ∨
      connectedComponentIn K₁ᶜ x₁ ⊆ connectedComponentIn K₂ᶜ x₂ ∨
      connectedComponentIn K₂ᶜ x₂ ⊆ connectedComponentIn K₁ᶜ x₁ := by
  classical
  let V₁ := connectedComponentIn K₁ᶜ x₁
  let V₂ := connectedComponentIn K₂ᶜ x₂
  by_cases hV : (V₁ ∩ V₂).Nonempty
  · by_cases hK₂V₁ : (K₂ ∩ V₁).Nonempty
    · have h₂in₁ : K₂ ⊆ V₁ :=
        preconnected_subset_component_of_meets hc₂.isPreconnected
          (fun z hz₂ hz₁ => Set.disjoint_left.mp hdisj hz₁ hz₂) hK₂V₁
      by_cases hV₂V₁ : V₂ ⊆ V₁
      · exact Or.inr (Or.inr hV₂V₁)
      · have hK₁V₂ : (K₁ ∩ V₂).Nonempty := by
          by_contra hnone
          have hV₂K₁ : V₂ ⊆ K₁ᶜ := by
            intro z hz₂ hz₁
            exact hnone ⟨z, hz₁, hz₂⟩
          have hV₂V₁' : V₂ ⊆ V₁ :=
            preconnected_subset_component_of_meets isPreconnected_connectedComponentIn
              hV₂K₁ (by simpa only [Set.inter_comm] using hV)
          exact hV₂V₁ hV₂V₁'
        have h₁in₂ : K₁ ⊆ V₂ :=
          preconnected_subset_component_of_meets hc₁.isPreconnected
            (fun z hz₁ hz₂ => Set.disjoint_left.mp hdisj hz₁ hz₂) hK₁V₂
        exact False.elim
          (not_mutual_enclosure hK₁ hK₂ hc₁.nonempty hc₂.nonempty hb₁ hb₂
            ⟨h₂in₁, h₁in₂⟩)
    · have hV₁K₂ : V₁ ⊆ K₂ᶜ := by
        intro z hz₁ hz₂
        exact hK₂V₁ ⟨z, hz₂, hz₁⟩
      have hV₁V₂ : V₁ ⊆ V₂ :=
        preconnected_subset_component_of_meets isPreconnected_connectedComponentIn
          hV₁K₂ hV
      exact Or.inr (Or.inl hV₁V₂)
  · exact Or.inl (Set.disjoint_left.mpr fun z hz₁ hz₂ => hV ⟨z, hz₁, hz₂⟩)

 
theorem compact_obstacles_inter_of_components_inter_of_incomparable
    {K₁ K₂ : Set ℂ} {x₁ x₂ : ℂ}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hc₁ : IsConnected K₁) (hc₂ : IsConnected K₂)
    (hb₁ : Bornology.IsBounded (connectedComponentIn K₁ᶜ x₁))
    (hb₂ : Bornology.IsBounded (connectedComponentIn K₂ᶜ x₂))
    (hoverlap : (connectedComponentIn K₁ᶜ x₁ ∩
      connectedComponentIn K₂ᶜ x₂).Nonempty)
    (hn₁₂ : ¬ connectedComponentIn K₁ᶜ x₁ ⊆ connectedComponentIn K₂ᶜ x₂)
    (hn₂₁ : ¬ connectedComponentIn K₂ᶜ x₂ ⊆ connectedComponentIn K₁ᶜ x₁) :
    (K₁ ∩ K₂).Nonempty := by
  by_contra h
  have hdisj : Disjoint K₁ K₂ := Set.disjoint_left.mpr fun z hz₁ hz₂ =>
    h ⟨z, hz₁, hz₂⟩
  rcases bounded_complementary_components_noncrossing hK₁ hK₂ hc₁ hc₂ hdisj hb₁ hb₂
    with h | h | h
  · obtain ⟨z, hz₁, hz₂⟩ := hoverlap
    exact Set.disjoint_left.mp h hz₁ hz₂
  · exact hn₁₂ h
  · exact hn₂₁ h

 
theorem preconnected_biUnion_of_cover_meets {ι : Type*} (S : Finset ι)
    (V : ι → Set ℂ) (A : Set ℂ) (hA : IsPreconnected A)
    (hcov : A ⊆ ⋃ i ∈ S, V i)
    (hmeet : ∀ i ∈ S, (V i ∩ A).Nonempty)
    (hpc : ∀ i ∈ S, IsPreconnected (V i)) :
    IsPreconnected (⋃ i ∈ S, V i) := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  obtain ⟨i, hiS, hxi⟩ := mem_iUnion₂.mp hx
  obtain ⟨j, hjS, hyj⟩ := mem_iUnion₂.mp hy
  have h₁ : IsPreconnected (V i ∪ A) :=
    (hpc i hiS).union' (hmeet i hiS) hA
  have h₂ : IsPreconnected ((V i ∪ A) ∪ V j) := by
    refine h₁.union' ?_ (hpc j hjS)
    obtain ⟨z, hzV, hzA⟩ := hmeet j hjS
    exact ⟨z, Or.inr hzA, hzV⟩
  refine ⟨(V i ∪ A) ∪ V j, ?_, Or.inl (Or.inl hxi), Or.inr hyj, h₂⟩
  refine union_subset (union_subset ?_ hcov) ?_
  · exact subset_biUnion_of_mem (Finset.mem_coe.mpr hiS)
  · exact subset_biUnion_of_mem (Finset.mem_coe.mpr hjS)

 
theorem component_overlap_chain_of_cover {ι : Type*} (S : Finset ι)
    (V : ι → Set ℂ) (A : Set ℂ) (hA : IsPreconnected A)
    (hcov : A ⊆ ⋃ i ∈ S, V i)
    (hmeet : ∀ i ∈ S, (V i ∩ A).Nonempty)
    (hpc : ∀ i ∈ S, IsPreconnected (V i))
    (hopen : ∀ i ∈ S, IsOpen (V i))
    (i j : {i // i ∈ S}) :
    Relation.TransGen (fun a b : {i // i ∈ S} =>
      (V a.val ∩ V b.val).Nonempty) i j := by
  have hconn : IsPreconnected (⋃ t : {i // i ∈ S}, V t.val) := by
    simpa only [Set.iUnion_subtype] using
      preconnected_biUnion_of_cover_meets S V A hA hcov hmeet hpc
  exact hconn.transGen_of_iUnion (fun t => hopen t.val t.property) i j
    (by obtain ⟨z, hz, -⟩ := hmeet i.val i.property; exact ⟨z, hz⟩)
    (by obtain ⟨z, hz, -⟩ := hmeet j.val j.property; exact ⟨z, hz⟩)

 
theorem exists_minimal_finite_subcover {ι : Type*} [DecidableEq ι] (S₀ : Finset ι)
    (V : ι → Set ℂ) (A : Set ℂ) (hcov : A ⊆ ⋃ i ∈ S₀, V i) :
    ∃ S ⊆ S₀, A ⊆ (⋃ i ∈ S, V i) ∧
      (∀ j ∈ S, (V j ∩ A).Nonempty) ∧
      ∀ j ∈ S, ¬ V j ⊆ ⋃ i ∈ S.erase j, V i := by
  classical
  let C : Finset (Finset ι) :=
    S₀.powerset.filter fun S => A ⊆ ⋃ i ∈ S, V i
  have hCne : C.Nonempty :=
    ⟨S₀, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self _, hcov⟩⟩
  obtain ⟨S, hSC, hSmin⟩ := C.exists_min_image Finset.card hCne
  obtain ⟨hSP, hSA⟩ := Finset.mem_filter.mp hSC
  have herase : ∀ j ∈ S, ¬ A ⊆ ⋃ i ∈ S.erase j, V i := by
    intro j hj h
    have hmem : S.erase j ∈ C := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset j S).trans
        (Finset.mem_powerset.mp hSP)), h⟩
    have hle := hSmin _ hmem
    have hlt := Finset.card_erase_lt_of_mem hj
    omega
  refine ⟨S, Finset.mem_powerset.mp hSP, hSA, ?_, ?_⟩
  · intro j hj
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    refine herase j hj fun a ha => ?_
    obtain ⟨i, hiS, hai⟩ := mem_iUnion₂.mp (hSA ha)
    by_cases hij : i = j
    · subst hij
      exact False.elim (show a ∈ (∅ : Set ℂ) from hne ▸ ⟨hai, ha⟩)
    · exact mem_biUnion (Finset.mem_erase.mpr ⟨hij, hiS⟩) hai
  · intro j hj hsub
    refine herase j hj fun a ha => ?_
    obtain ⟨i, hiS, hai⟩ := mem_iUnion₂.mp (hSA ha)
    by_cases hij : i = j
    · subst hij
      exact hsub hai
    · exact mem_biUnion (Finset.mem_erase.mpr ⟨hij, hiS⟩) hai

 
theorem obstacle_inter_of_minimal_component_overlap {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (K : ι → Set ℂ) (x : ι → ℂ)
    (hcompact : ∀ i ∈ S, IsCompact (K i))
    (hconnected : ∀ i ∈ S, IsConnected (K i))
    (hbounded : ∀ i ∈ S, Bornology.IsBounded
      (connectedComponentIn (K i)ᶜ (x i)))
    (hminimal : ∀ i ∈ S, ¬ connectedComponentIn (K i)ᶜ (x i) ⊆
      ⋃ j ∈ S.erase i, connectedComponentIn (K j)ᶜ (x j))
    (i j : {i // i ∈ S})
    (hoverlap : (connectedComponentIn (K i.val)ᶜ (x i.val) ∩
      connectedComponentIn (K j.val)ᶜ (x j.val)).Nonempty) :
    i = j ∨ (K i.val ∩ K j.val).Nonempty := by
  classical
  by_cases hij : i = j
  · exact Or.inl hij
  · right
    have hne : i.val ≠ j.val := fun e => hij (Subtype.ext e)
    have hn₁₂ : ¬ connectedComponentIn (K i.val)ᶜ (x i.val) ⊆
        connectedComponentIn (K j.val)ᶜ (x j.val) := by
      intro hsub
      apply hminimal i.val i.property
      exact hsub.trans (subset_biUnion_of_mem
        (u := fun k => connectedComponentIn (K k)ᶜ (x k))
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne.symm, j.property⟩)))
    have hn₂₁ : ¬ connectedComponentIn (K j.val)ᶜ (x j.val) ⊆
        connectedComponentIn (K i.val)ᶜ (x i.val) := by
      intro hsub
      apply hminimal j.val j.property
      exact hsub.trans (subset_biUnion_of_mem
        (u := fun k => connectedComponentIn (K k)ᶜ (x k))
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, i.property⟩)))
    exact compact_obstacles_inter_of_components_inter_of_incomparable
      (hcompact i.val i.property) (hcompact j.val j.property)
      (hconnected i.val i.property) (hconnected j.val j.property)
      (hbounded i.val i.property) (hbounded j.val j.property)
      hoverlap hn₁₂ hn₂₁

 

theorem simple_obstacle_chain_of_transGen {ι : Type*} {S : Finset ι}
    (K : ι → Set ℂ) {a b : {i // i ∈ S}}
    (h : Relation.TransGen (fun u v : {i // i ∈ S} =>
      u = v ∨ (K u.val ∩ K v.val).Nonempty) a b) :
    ∃ (l : List {i // i ∈ S}) (hne : l ≠ []),
      l.head hne = a ∧ l.getLast hne = b ∧ l.Nodup ∧
      l.IsChain (fun u v => (K u.val ∩ K v.val).Nonempty) := by
  classical
  let G : SimpleGraph {i // i ∈ S} :=
    SimpleGraph.fromRel (fun u v => (K u.val ∩ K v.val).Nonempty)
  have hstep : ∀ u v : {i // i ∈ S},
      (u = v ∨ (K u.val ∩ K v.val).Nonempty) → G.Reachable u v := by
    intro u v huv
    rcases huv with rfl | hc
    · exact SimpleGraph.Reachable.refl _
    · by_cases hne : u = v
      · subst v
        exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable (show G.Adj u v from ⟨hne, Or.inl hc⟩)
  have hreach : ∀ u v : {i // i ∈ S},
      Relation.ReflTransGen (fun x y => x = y ∨ (K x.val ∩ K y.val).Nonempty) u v →
      G.Reachable u v := by
    intro u v huv
    induction huv with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hlast ih => exact ih.trans (hstep _ _ hlast)
  obtain ⟨w⟩ := hreach a b h.to_reflTransGen
  let p : G.Path a b := w.toPath
  refine ⟨(p : G.Walk a b).support, (p : G.Walk a b).support_ne_nil,
    ?_, ?_, p.nodup_support, ?_⟩
  · simpa only [List.head?_eq_some_head] using (p : G.Walk a b).head_support
  · exact (p : G.Walk a b).getLast_support
  · exact (p : G.Walk a b).isChain_adj_support.imp (by
      intro u v huv
      rcases huv.2 with hc | hc
      · exact hc
      · simpa only [Set.inter_comm] using hc)

 
theorem finiteObstacle_chain {ι : Type*} [DecidableEq ι]
    (S₀ : Finset ι) (K : ι → Set ℂ) (x : ι → ℂ) (A : Set ℂ)
    (_hAne : A.Nonempty) (hA : IsPreconnected A)
    (hcov : A ⊆ ⋃ i ∈ S₀, connectedComponentIn (K i)ᶜ (x i))
    (hcompact : ∀ i ∈ S₀, IsCompact (K i))
    (hconnected : ∀ i ∈ S₀, IsConnected (K i))
    (hbounded : ∀ i ∈ S₀, Bornology.IsBounded
      (connectedComponentIn (K i)ᶜ (x i))) :
    ∃ S ⊆ S₀,
      A ⊆ (⋃ i ∈ S, connectedComponentIn (K i)ᶜ (x i)) ∧
      (∀ i ∈ S, (connectedComponentIn (K i)ᶜ (x i) ∩ A).Nonempty) ∧
      (∀ i ∈ S, ¬ connectedComponentIn (K i)ᶜ (x i) ⊆
        ⋃ j ∈ S.erase i, connectedComponentIn (K j)ᶜ (x j)) ∧
      ∀ i j : {i // i ∈ S},
        ∃ (l : List {t // t ∈ S}) (hne : l ≠ []),
          l.head hne = i ∧ l.getLast hne = j ∧ l.Nodup ∧
          l.IsChain (fun u v => (K u.val ∩ K v.val).Nonempty) := by
  classical
  let V : ι → Set ℂ := fun i => connectedComponentIn (K i)ᶜ (x i)
  obtain ⟨S, hSS₀, hSA, hmeet, hmin⟩ :=
    exists_minimal_finite_subcover S₀ V A hcov
  refine ⟨S, hSS₀, hSA, hmeet, hmin, ?_⟩
  intro i j
  have hpc : ∀ k ∈ S, IsPreconnected (V k) :=
    fun _ _ => isPreconnected_connectedComponentIn
  have hopen : ∀ k ∈ S, IsOpen (V k) :=
    fun k hk => (hcompact k (hSS₀ hk)).isClosed.isOpen_compl.connectedComponentIn
  have hgraph := component_overlap_chain_of_cover S V A hA hSA hmeet hpc hopen i j
  have hcontact : Relation.TransGen
      (fun a b : {t // t ∈ S} => a = b ∨ (K a.val ∩ K b.val).Nonempty) i j :=
    (Relation.TransGen.mono (fun a b hab =>
      obstacle_inter_of_minimal_component_overlap S K x
        (fun k hk => hcompact k (hSS₀ hk))
        (fun k hk => hconnected k (hSS₀ hk))
        (fun k hk => hbounded k (hSS₀ hk))
        hmin a b hab)) i j hgraph
  exact simple_obstacle_chain_of_transGen K hcontact

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation
