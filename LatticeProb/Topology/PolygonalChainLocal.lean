/-
# Local structure of a simple polygonal chain

Near a point of a geometrically simple finite polygonal chain which is neither its first nor
its last vertex, the chain coincides with the union of two segments issuing from that point in
directions that are not positive multiples of each other. A point in the open interior of an
edge sees the two endpoints of the edge; an interior vertex sees its two neighbouring vertices.
-/
import LatticeProb.Topology.SimplePolygonalChain

open Metric Set

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A closed set not containing `y` misses a small ball around `y`. -/
theorem exists_ball_inter_eq_empty_of_isClosed {K : Set E} (hK : IsClosed K) {y : E}
    (hy : y ∉ K) : ∃ r > 0, K ∩ ball y r = ∅ := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 (hK.isOpen_compl.mem_nhds hy)
  refine ⟨r, hr, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzK, hz⟩
  exact hsub hz hzK

/-- A segment is covered by the two subsegments cut at one of its points. -/
theorem segment_subset_segment_union {a b y : E} (hy : y ∈ segment ℝ a b) :
    segment ℝ a b ⊆ segment ℝ y a ∪ segment ℝ y b := by
  intro z hz
  rw [segment_eq_image'] at hy hz
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hy
  obtain ⟨τ, ⟨hτ0, hτ1⟩, rfl⟩ := hz
  rcases le_total τ s with h | h
  · left
    rw [segment_eq_image']
    by_cases hs : s = 0
    · have hτ : τ = 0 := le_antisymm (hs ▸ h) hτ0
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [hs, hτ]⟩
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hq : 0 ≤ τ / s := div_nonneg hτ0 hspos.le
      have hq1 : τ / s ≤ 1 := (div_le_one hspos).2 h
      refine ⟨1 - τ / s, ⟨by linarith, by linarith⟩, ?_⟩
      match_scalars <;> field_simp <;> ring
  · right
    rw [segment_eq_image']
    by_cases hs : s = 1
    · have hτ : τ = 1 := le_antisymm hτ1 (hs ▸ h)
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [hs, hτ]⟩
    · have hspos : 0 < 1 - s := sub_pos.2 (lt_of_le_of_ne hs1 hs)
      have hq : 0 ≤ (τ - s) / (1 - s) := div_nonneg (sub_nonneg.2 h) hspos.le
      have hq1 : (τ - s) / (1 - s) ≤ 1 := (div_le_one hspos).2 (by linarith)
      refine ⟨(τ - s) / (1 - s), ⟨hq, hq1⟩, ?_⟩
      match_scalars <;> field_simp <;> ring

/-- The conclusion of the local structure theorem: near `y`, the set `C` is a union of two
segments issuing from `y` whose directions are not positively proportional. -/
private def HasLocalTwoSegments (C : Set E) (y : E) : Prop :=
  ∃ r > 0, ∃ a b : E, a ≠ y ∧ b ≠ y ∧ (∀ t : ℝ, 0 < t → b - y ≠ t • (a - y)) ∧
    r ≤ ‖a - y‖ ∧ r ≤ ‖b - y‖ ∧ C ∩ ball y r = (segment ℝ y a ∪ segment ℝ y b) ∩ ball y r

private theorem local_two_segments_aux : ∀ (l : List E) (a : E), IsSimplePolygonalChain (a :: l) →
    ∀ {y : E}, y ∈ polygonalChain (a :: l) → y ≠ a →
    y ≠ (a :: l).getLast (List.cons_ne_nil _ _) →
    HasLocalTwoSegments (polygonalChain (a :: l)) y
  | [], a, _, y, hy, hya, _ => absurd (mem_singleton_iff.1 hy) hya
  | b :: rest, a, hs, y, hy, hya, hyl => by
    have hab : a ≠ b := hs.1
    have htail : IsSimplePolygonalChain (b :: rest) := hs.2.1
    have hmeet : segment ℝ a b ∩ polygonalChain (b :: rest) = {b} := hs.2.2
    have hclT : IsClosed (polygonalChain (b :: rest)) := (isCompact_polygonal_chain _).isClosed
    have hclS : IsClosed (segment ℝ a b) := (isCompact_segment a b).isClosed
    rw [polygonal_chain_cons_cons] at hy ⊢
    by_cases hyb : y = b
    · -- the vertex `b`
      subst hyb
      rcases rest with _ | ⟨c, rest'⟩
      · exact absurd rfl hyl
      · have hbc : y ≠ c := htail.1
        have hmeet2 : segment ℝ y c ∩ polygonalChain (c :: rest') = {c} := htail.2.2
        have hclT' : IsClosed (polygonalChain (c :: rest')) :=
          (isCompact_polygonal_chain _).isClosed
        have hyT' : y ∉ polygonalChain (c :: rest') := by
          intro h
          have : y ∈ segment ℝ y c ∩ polygonalChain (c :: rest') := ⟨left_mem_segment ℝ y c, h⟩
          rw [hmeet2] at this
          exact hbc this
        obtain ⟨r1, hr1, hr1e⟩ := exists_ball_inter_eq_empty_of_isClosed hclT' hyT'
        have hay : a - y ≠ 0 := sub_ne_zero.2 hab
        have hcy : c - y ≠ 0 := sub_ne_zero.2 hbc.symm
        have hpa : 0 < ‖a - y‖ := norm_pos_iff.2 hay
        have hpc : 0 < ‖c - y‖ := norm_pos_iff.2 hcy
        refine ⟨min (min r1 ‖a - y‖) ‖c - y‖, lt_min (lt_min hr1 hpa) hpc, a, c, hab, hbc.symm,
          ?_, (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _, ?_⟩
        · intro t ht heq
          set u : ℝ := min 1 t⁻¹ with hu
          have hu0 : 0 < u := lt_min one_pos (inv_pos.2 ht)
          have hu1 : u ≤ 1 := min_le_left _ _
          have hut : u * t ≤ 1 :=
            calc u * t ≤ t⁻¹ * t := mul_le_mul_of_nonneg_right (min_le_right _ _) ht.le
              _ = 1 := inv_mul_cancel₀ ht.ne'
          have hz1 : y + u • (c - y) ∈ segment ℝ y c := by
            rw [segment_eq_image']; exact ⟨u, ⟨hu0.le, hu1⟩, rfl⟩
          have hz2 : y + u • (c - y) ∈ segment ℝ a y := by
            rw [segment_symm, segment_eq_image']
            exact ⟨u * t, ⟨(mul_pos hu0 ht).le, hut⟩, by simp only [mul_smul, ← heq]⟩
          have hz3 : y + u • (c - y) ∈ segment ℝ a y ∩ polygonalChain (y :: c :: rest') :=
            ⟨hz2, Or.inl hz1⟩
          rw [hmeet] at hz3
          have h0 : u • (c - y) = 0 := by
            have := mem_singleton_iff.1 hz3
            simpa using this
          rcases smul_eq_zero.1 h0 with h | h
          · exact hu0.ne' h
          · exact hcy h
        · ext z
          constructor
          · rintro ⟨hz | hz | hz, hzr⟩
            · exact ⟨Or.inl (by rwa [segment_symm]), hzr⟩
            · exact ⟨Or.inr hz, hzr⟩
            · exact absurd (Set.eq_empty_iff_forall_notMem.1 hr1e z
                ⟨hz, ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hzr⟩)
                (fun h => h)
          · rintro ⟨hz | hz, hzr⟩
            · exact ⟨Or.inl (by rwa [segment_symm]), hzr⟩
            · exact ⟨Or.inr (Or.inl hz), hzr⟩
    · by_cases hyT : y ∈ polygonalChain (b :: rest)
      · -- `y` lies on the tail, away from its first vertex
        obtain ⟨r', hr', a', b', ha', hb', hpar, hra, hrb, hC⟩ :=
          local_two_segments_aux rest b htail hyT hyb hyl
        have hyS : y ∉ segment ℝ a b := by
          intro h
          have : y ∈ segment ℝ a b ∩ polygonalChain (b :: rest) := ⟨h, hyT⟩
          rw [hmeet] at this
          exact hyb this
        obtain ⟨r'', hr'', hr''e⟩ := exists_ball_inter_eq_empty_of_isClosed hclS hyS
        refine ⟨min r' r'', lt_min hr' hr'', a', b', ha', hb', hpar,
          (min_le_left _ _).trans hra, (min_le_left _ _).trans hrb, ?_⟩
        ext z
        constructor
        · rintro ⟨hz | hz, hzr⟩
          · exact absurd (Set.eq_empty_iff_forall_notMem.1 hr''e z
              ⟨hz, ball_subset_ball (min_le_right _ _) hzr⟩) (fun h => h)
          · have hz' : z ∈ polygonalChain (b :: rest) ∩ ball y r' :=
              ⟨hz, ball_subset_ball (min_le_left _ _) hzr⟩
            rw [hC] at hz'
            exact ⟨hz'.1, hzr⟩
        · rintro ⟨hz, hzr⟩
          have hz' : z ∈ (segment ℝ y a' ∪ segment ℝ y b') ∩ ball y r' :=
            ⟨hz, ball_subset_ball (min_le_left _ _) hzr⟩
          rw [← hC] at hz'
          exact ⟨Or.inr hz'.1, hzr⟩
      · -- `y` lies in the open edge from `a` to `b`
        have hyS : y ∈ segment ℝ a b := hy.resolve_right hyT
        obtain ⟨r1, hr1, hr1e⟩ := exists_ball_inter_eq_empty_of_isClosed hclT hyT
        have hay : a - y ≠ 0 := sub_ne_zero.2 (Ne.symm hya)
        have hby : b - y ≠ 0 := sub_ne_zero.2 (Ne.symm hyb)
        have hpa : 0 < ‖a - y‖ := norm_pos_iff.2 hay
        have hpb : 0 < ‖b - y‖ := norm_pos_iff.2 hby
        refine ⟨min (min r1 ‖a - y‖) ‖b - y‖, lt_min (lt_min hr1 hpa) hpb, a, b, Ne.symm hya,
          Ne.symm hyb, ?_, (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _, ?_⟩
        · intro t ht heq
          have hS := hyS
          rw [segment_eq_image'] at hS
          obtain ⟨s, ⟨hs0, hs1⟩, hys⟩ := hS
          subst hys
          have hs0' : s ≠ 0 := by
            rintro rfl
            exact hya (by simp)
          have hs1' : s ≠ 1 := by
            rintro rfl
            exact hyb (by simp)
          have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs0')
          have hslt : s < 1 := lt_of_le_of_ne hs1 hs1'
          have hsm : ((1 - s) + t * s) • (b - a) = 0 := by
            linear_combination (norm := module) heq
          rcases smul_eq_zero.1 hsm with h | h
          · have := mul_pos ht hspos
            linarith
          · exact hab (sub_eq_zero.1 h).symm
        · ext z
          constructor
          · rintro ⟨hz | hz, hzr⟩
            · exact ⟨segment_subset_segment_union hyS hz, hzr⟩
            · exact absurd (Set.eq_empty_iff_forall_notMem.1 hr1e z
                ⟨hz, ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hzr⟩)
                (fun h => h)
          · rintro ⟨hz | hz, hzr⟩
            · exact ⟨Or.inl ((convex_segment a b).segment_subset hyS (left_mem_segment ℝ a b) hz),
                hzr⟩
            · exact ⟨Or.inl ((convex_segment a b).segment_subset hyS (right_mem_segment ℝ a b) hz),
                hzr⟩

/-- **Local structure of a simple polygonal chain.** At a point `y` of a simple finite polygonal
chain which is neither its first nor its last vertex, there are two points `a`, `b`, not on a
common open ray from `y`, such that in a small ball around `y` the chain coincides with the union
of the segments `[y, a]` and `[y, b]`. -/
theorem IsSimplePolygonalChain.exists_two_segments_inter_ball {vs : List E}
    (hs : IsSimplePolygonalChain vs) {y : E} (hy : y ∈ polygonalChain vs)
    (hy0 : y ≠ vs.head hs.ne_nil) (hy1 : y ≠ vs.getLast hs.ne_nil) :
    ∃ r > 0, ∃ a b : E, a ≠ y ∧ b ≠ y ∧ (∀ t : ℝ, 0 < t → b - y ≠ t • (a - y)) ∧
      r ≤ ‖a - y‖ ∧ r ≤ ‖b - y‖ ∧
      polygonalChain vs ∩ ball y r = (segment ℝ y a ∪ segment ℝ y b) ∩ ball y r := by
  cases vs with
  | nil => exact hs.elim
  | cons a l => exact local_two_segments_aux l a hs hy hy0 hy1

end LatticeProb.Topology
