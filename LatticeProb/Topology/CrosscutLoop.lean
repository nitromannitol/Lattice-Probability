/-
# A transverse crossing of an arc disconnects a domain

Let `C ⊆ ℂ` be open and `K` a preconnected set disjoint from `C`, and let `γ` be an arc whose two endpoints lie
in `K`. Suppose a segment `[p, q] ⊆ C` meets `γ` at one interior point `e` only, where `γ` contains a straight
open segment through `e` transverse to `[p, q]`. Then `C \ γ` is not preconnected.

The proof uses no winding numbers. If `C \ γ` were preconnected, a simple polygonal chain inside `C \ γ` from
`q` to `p`, closed by the edge `[p, q]`, would be a closed polygon. The set `K ∪ (γ \ {e})` is preconnected, misses
this polygon, and approaches `e` from both sides of the closing edge, which the parity separation at an
interior point of an edge (`exists_closing_edge_separation`) forbids.

## Main results

* `IsSimplePolygonalChain.zip_ne`: consecutive vertices of a simple chain are distinct.
* `exists_nondegenerate_polygonal_chain`: polygonal connectedness by chains with distinct consecutive vertices.
* `not_mem_closure_both_sides_of_closing_edge`: a preconnected set missing a closed polygon does not accumulate
  at an interior point of an edge from both sides.
* `mem_closure_openSegment_inter_sides`: an open segment through `e`, transverse to a direction, reaches `e`
  from both sides.
* `isPreconnected_union_image_diff`: a preconnected set containing both endpoints of an arc stays preconnected
  after adding the arc punctured at an interior point.
* `not_isPreconnected_diff_arc_of_transverse`: the disconnection statement above.
-/
import LatticeProb.Topology.PolygonalParityComplex
import LatticeProb.Topology.SimplePolygonalChain

open Set Filter Topology ComplexConjugate

namespace LatticeProb.Topology

section Chains

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Consecutive vertices of a geometrically simple chain are distinct. -/
theorem IsSimplePolygonalChain.zip_ne : ∀ {u : E} {rest : List E}, IsSimplePolygonalChain (u :: rest) →
    ∀ P ∈ (u :: rest).zip rest, P.1 ≠ P.2
  | _, [], _ => by simp
  | _, v :: rest, h => by
    intro P hP
    rw [List.zip_cons_cons, List.mem_cons] at hP
    rcases hP with rfl | hP
    · exact h.1
    · exact IsSimplePolygonalChain.zip_ne h.2.1 P hP

/-- **Polygonal connectedness with distinct consecutive vertices.** Two points of an open preconnected set are
joined inside it by a polygonal chain whose consecutive vertices are distinct. -/
theorem exists_nondegenerate_polygonal_chain {Ω : Set E} {x y : E} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∃ rest : List E, (x :: rest).getLast (List.cons_ne_nil _ _) = y ∧
      (∀ P ∈ (x :: rest).zip rest, P.1 ≠ P.2) ∧ polygonalChain (x :: rest) ⊆ Ω := by
  obtain ⟨vs, hv, hvΩ, hvx, hvy⟩ := exists_polygonal_chain_of_isPreconnected hΩ hconn hx hy
  obtain ⟨us, hu, hs, hux, huy, husub⟩ := exists_simple_polygonal_chain vs hv
  obtain _ | ⟨u, rest⟩ := us
  · exact absurd rfl hu
  have hu' : u = x := by rw [← hvx, ← hux]; rfl
  subst hu'
  exact ⟨rest, huy.trans hvy, hs.zip_ne, husub.trans hvΩ⟩

end Chains

/-- **A preconnected set missing a closed polygon does not reach an edge from both sides.** Let a polygonal
chain from `b` to `a` with distinct consecutive vertices be closed by the edge `[a, b]`, and let `e` be an
interior point of that edge off the chain. A preconnected set disjoint from the polygon cannot accumulate at `e`
both from the left and from the right of the closing edge. -/
theorem not_mem_closure_both_sides_of_closing_edge {b a e : ℂ} {rest : List ℂ}
    (hlast : (b :: rest).getLast (List.cons_ne_nil _ _) = a)
    (hnd : ∀ P ∈ (b :: rest).zip rest, P.1 ≠ P.2) (huu : a ≠ b)
    (he : e ∈ openSegment ℝ a b) (heL : e ∉ polygonalChain (b :: rest))
    {S : Set ℂ} (hS : IsPreconnected S)
    (hSP : Disjoint S (polygonalChain (b :: rest) ∪ segment ℝ a b))
    (hpos : e ∈ closure (S ∩ {x | 0 < (conj (b - a) * (x - e)).im})) :
    e ∉ closure (S ∩ {x | (conj (b - a) * (x - e)).im < 0}) := by
  intro hneg
  obtain ⟨U, hU, heU, hsep⟩ := exists_closing_edge_separation hlast hnd huu he heL
  obtain ⟨x, hxU, hxS, hx⟩ := mem_closure_iff.1 hpos U hU heU
  obtain ⟨y, hyU, hyS, hy⟩ := mem_closure_iff.1 hneg U hU heU
  obtain ⟨z, hzS, hzP⟩ := hsep x hxU y hyU hx hy S hS hxS hyS
  exact Set.disjoint_left.1 hSP hzS hzP

/-- Along a segment `t ↦ c + t • (d - c)`, the sign of `Im (w * (x - e))` is that of `t - θ`, where `e` is the
point of parameter `θ`. -/
theorem im_mul_sub_lineMap (w c d : ℂ) (t θ : ℝ) :
    (w * (c + t • (d - c) - (c + θ • (d - c)))).im = (t - θ) * (w * (d - c)).im := by
  have h : c + t • (d - c) - (c + θ • (d - c)) = (t - θ) • (d - c) := by rw [sub_smul]; abel
  rw [h, mul_smul_comm, Complex.smul_im, smul_eq_mul]

/-- An open segment through `e`, transverse to the direction determined by `w`, reaches `e` from both sides: from
the side where `Im (w * (x - e)) > 0` and from the side where it is negative. -/
theorem mem_closure_openSegment_inter_sides {c d e w : ℂ} (he : e ∈ openSegment ℝ c d)
    (hw : (w * (d - c)).im ≠ 0) :
    e ∈ closure (openSegment ℝ c d ∩ {x | 0 < (w * (x - e)).im}) ∧
      e ∈ closure (openSegment ℝ c d ∩ {x | (w * (x - e)).im < 0}) := by
  rw [openSegment_eq_image'] at he ⊢
  obtain ⟨θ, hθ, rfl⟩ := he
  set g : ℝ → ℂ := fun t => c + t • (d - c) with hg
  have hcont : Tendsto g (𝓝 θ) (𝓝 (g θ)) :=
    ((continuous_const.add (continuous_id.smul continuous_const)).tendsto θ)
  have hseg : ∀ t ∈ Ioo (0 : ℝ) 1, g t ∈ g '' Ioo 0 1 := fun t ht => ⟨t, ht, rfl⟩
  -- points of parameter `t > θ` and `t < θ` lie on opposite sides
  have hright : ∀ s : Set ℂ, (∀ t ∈ Ioo θ 1, g t ∈ s) → g θ ∈ closure s := fun s hs =>
    mem_closure_of_tendsto (hcont.mono_left nhdsWithin_le_nhds)
      (Filter.mem_of_superset (Ioo_mem_nhdsGT hθ.2) hs)
  have hleft : ∀ s : Set ℂ, (∀ t ∈ Ioo 0 θ, g t ∈ s) → g θ ∈ closure s := fun s hs =>
    mem_closure_of_tendsto (hcont.mono_left nhdsWithin_le_nhds)
      (Filter.mem_of_superset (Ioo_mem_nhdsLT hθ.1) hs)
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · refine ⟨hleft _ fun t ht => ⟨hseg t ⟨ht.1, ht.2.trans hθ.2⟩, ?_⟩,
      hright _ fun t ht => ⟨hseg t ⟨hθ.1.trans ht.1, ht.2⟩, ?_⟩⟩
    · show 0 < (w * (g t - g θ)).im
      rw [hg, im_mul_sub_lineMap]
      exact mul_pos_of_neg_of_neg (sub_neg.2 ht.2) hneg
    · show (w * (g t - g θ)).im < 0
      rw [hg, im_mul_sub_lineMap]
      exact mul_neg_of_pos_of_neg (sub_pos.2 ht.1) hneg
  · refine ⟨hright _ fun t ht => ⟨hseg t ⟨hθ.1.trans ht.1, ht.2⟩, ?_⟩,
      hleft _ fun t ht => ⟨hseg t ⟨ht.1, ht.2.trans hθ.2⟩, ?_⟩⟩
    · show 0 < (w * (g t - g θ)).im
      rw [hg, im_mul_sub_lineMap]
      exact mul_pos (sub_pos.2 ht.1) hpos
    · show (w * (g t - g θ)).im < 0
      rw [hg, im_mul_sub_lineMap]
      exact mul_neg_of_neg_of_pos (sub_neg.2 ht.2) hpos

/-- **An arc punctured at an interior point, joined at both ends.** If `K` is preconnected and contains both
endpoints of the arc `f([0,1])`, then `K` together with the arc minus an interior point `f t₀` is preconnected. -/
theorem isPreconnected_union_image_diff {X : Type*} [TopologicalSpace X] {K : Set X} {f : ℝ → X} {t₀ : ℝ}
    (hK : IsPreconnected K) (hf : ContinuousOn f (Icc 0 1)) (hfi : InjOn f (Icc 0 1))
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (h0 : f 0 ∈ K) (h1 : f 1 ∈ K) :
    IsPreconnected (K ∪ (f '' Icc 0 1 \ {f t₀})) := by
  have ht₀I : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀
  have hsplit : f '' Icc 0 1 \ {f t₀} = f '' Ico 0 t₀ ∪ f '' Ioc t₀ 1 := by
    ext z
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hne⟩
      have hst : s ≠ t₀ := fun h => hne (h ▸ rfl)
      rcases lt_or_gt_of_ne hst with h | h
      · exact Or.inl ⟨s, ⟨hs.1, h⟩, rfl⟩
      · exact Or.inr ⟨s, ⟨h, hs.2⟩, rfl⟩
    · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
      · have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le.trans ht₀.2.le⟩
        exact ⟨⟨s, hsI, rfl⟩, fun h => hs.2.ne (hfi hsI ht₀I h)⟩
      · have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨ht₀.1.le.trans hs.1.le, hs.2⟩
        exact ⟨⟨s, hsI, rfl⟩, fun h => hs.1.ne' (hfi hsI ht₀I h)⟩
  have hA : IsPreconnected (f '' Ico 0 t₀) :=
    isPreconnected_Ico.image f (hf.mono fun s hs => ⟨hs.1, hs.2.le.trans ht₀.2.le⟩)
  have hB : IsPreconnected (f '' Ioc t₀ 1) :=
    isPreconnected_Ioc.image f (hf.mono fun s hs => ⟨ht₀.1.le.trans hs.1.le, hs.2⟩)
  rw [hsplit, ← union_assoc]
  refine IsPreconnected.union (f 1) (Or.inl h1) ⟨1, ⟨ht₀.2, le_rfl⟩, rfl⟩ ?_ hB
  exact IsPreconnected.union (f 0) h0 ⟨0, ⟨le_rfl, ht₀.1⟩, rfl⟩ hK hA

/-- **A transverse crossing disconnects.** Let `C ⊆ ℂ` be open and `K` preconnected and disjoint from `C`, and let
`γ = f([0,1])` be an arc with both endpoints in `K`. Suppose a segment `[p, q] ⊆ C` meets `γ` only at the point
`f t₀` (`0 < t₀ < 1`), which lies in its interior, and `γ` contains an open segment `(c, d)` through `f t₀`
transverse to `[p, q]`. Then `C \ γ` is not preconnected. -/
theorem not_isPreconnected_diff_arc_of_transverse {C K : Set ℂ} {f : ℝ → ℂ} {t₀ : ℝ} {p q c d : ℂ}
    (hC : IsOpen C) (hK : IsPreconnected K) (hCK : Disjoint C K)
    (hf : ContinuousOn f (Icc 0 1)) (hfi : InjOn f (Icc 0 1)) (h0 : f 0 ∈ K) (h1 : f 1 ∈ K)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hpqC : segment ℝ p q ⊆ C) (he : f t₀ ∈ openSegment ℝ p q)
    (hpqγ : segment ℝ p q ∩ f '' Icc 0 1 ⊆ {f t₀})
    (hcd : f t₀ ∈ openSegment ℝ c d) (hcdγ : openSegment ℝ c d ⊆ f '' Icc 0 1)
    (htrans : (conj (q - p) * (d - c)).im ≠ 0) :
    ¬ IsPreconnected (C \ f '' Icc 0 1) := by
  set γ := f '' Icc 0 1 with hγ
  set e := f t₀ with he_def
  have hγc : IsClosed γ := (isCompact_Icc.image_of_continuousOn hf).isClosed
  have hpq : p ≠ q := by
    rintro rfl
    simp at htrans
  -- the endpoints of the transverse segment lie off the arc
  have hend : ∀ z ∈ segment ℝ p q, z ≠ e → z ∈ C \ γ := fun z hz hze =>
    ⟨hpqC hz, fun hzγ => hze (hpqγ ⟨hz, hzγ⟩)⟩
  have hpe : p ≠ e := fun h => hpq (left_mem_openSegment_iff.1 (by rwa [← h] at he))
  have hqe : q ≠ e := fun h => hpq (right_mem_openSegment_iff.1 (by rwa [← h] at he))
  intro hpre
  obtain ⟨rest, hlast, hnd, hsub⟩ := exists_nondegenerate_polygonal_chain (hC.sdiff hγc) hpre
    (hend q (right_mem_segment ℝ p q) hqe) (hend p (left_mem_segment ℝ p q) hpe)
  have heL : e ∉ polygonalChain (q :: rest) := fun h => (hsub h).2 ⟨t₀, Ioo_subset_Icc_self ht₀, rfl⟩
  have hS : IsPreconnected (K ∪ (γ \ {e})) := isPreconnected_union_image_diff hK hf hfi ht₀ h0 h1
  have hSP : Disjoint (K ∪ (γ \ {e})) (polygonalChain (q :: rest) ∪ segment ℝ p q) := by
    rw [Set.disjoint_left]
    rintro z (hzK | ⟨hzγ, hze⟩) (hzL | hzτ)
    · exact Set.disjoint_left.1 hCK (hsub hzL).1 hzK
    · exact Set.disjoint_left.1 hCK (hpqC hzτ) hzK
    · exact (hsub hzL).2 hzγ
    · exact hze (hpqγ ⟨hzτ, hzγ⟩)
  -- points of the open segment `(c, d)` off `e` belong to `K ∪ (γ \ {e})`
  have hside : ∀ s : Set ℂ, (∀ x ∈ s, x ≠ e) → openSegment ℝ c d ∩ s ⊆ (K ∪ (γ \ {e})) ∩ s :=
    fun s hs x hx => ⟨Or.inr ⟨hcdγ hx.1, hs x hx.2⟩, hx.2⟩
  have hne : ∀ x : ℂ, (conj (q - p) * (x - e)).im ≠ 0 → x ≠ e := by
    rintro x hx rfl
    simp at hx
  obtain ⟨hpos, hneg⟩ := mem_closure_openSegment_inter_sides hcd htrans
  exact not_mem_closure_both_sides_of_closing_edge hlast hnd hpq he heL hS hSP
    (closure_mono (hside _ fun x hx => hne x hx.ne') hpos)
    (closure_mono (hside _ fun x hx => hne x hx.ne) hneg)

end LatticeProb.Topology
