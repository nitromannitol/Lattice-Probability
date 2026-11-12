/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W8

/-!
# DZZ Lemma 3.12: one of the two segments has at most one parent (D93, packet P-8)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, l. 1471–1488
(D93's counting replacing "by connectivity", l. 1476–1477).

* `pick_arc_x`: the case where `𝖢_{i,2}` is not a parent;
* **`pick_arc`**: unless both `𝖢_{i,1}`, `𝖢_{i,2}` are parents, one segment
  `𝖢_{i,1}, R, 𝖢_{i,2}` has at most one parent.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- At most one parent in a list. -/
def LeOneParent (C : DyBox) (W : List DyBox) : Prop :=
  ∀ c ∈ W, ∀ c' ∈ W, C.side < c.side → C.side < c'.side → c = c'

lemma pick_arc_x {C x y w : DyBox} {R₁ R₂ Z : List DyBox} (hC : IsCell m δ C)
    (hW₁ : (x :: R₁ ++ [y]).IsChain Neighbour) (hW₂ : (x :: R₂ ++ [y]).IsChain Neighbour)
    (hperm : (R₁ ++ R₂ ++ [x, y]).Perm Z)
    (hZ : ∀ c ∈ Z, IsCell m δ c ∧ (c.closedBox ∩ C.largeBox).Nonempty)
    (hcount : ∀ p ∈ Z, C.side < p.side → Z.count p = 1) (hxy : x ≠ y)
    (hw : Neighbour x w) (hwc : IsCell m δ w) (hwL : (w.closedBox ∩ C.largeBox).Nonempty)
    (hwZ : w ∉ Z) (hy : ¬ C.side < y.side) :
    LeOneParent C (x :: R₁ ++ [y]) ∨ LeOneParent C (x :: R₂ ++ [y]) := by
  have hmemZ : ∀ c, c ∈ R₁ ++ R₂ ++ [x, y] → c ∈ Z := fun c hc => hperm.subset hc
  have hR1Z : ∀ c ∈ R₁, c ∈ Z := fun c hc => hmemZ c (by simp [hc])
  have hR2Z : ∀ c ∈ R₂, c ∈ Z := fun c hc => hmemZ c (by simp [hc])
  have hxZ : x ∈ Z := hmemZ x (by simp)
  have hpar : ∀ c ∈ Z, C.side < c.side → IsParent m δ C c := fun c hc hs =>
    ⟨(hZ c hc).1, hs, (hZ c hc).2⟩
  have hcnt : ∀ p ∈ Z, C.side < p.side →
      R₁.count p + R₂.count p + [x, y].count p = 1 := by
    intro p hp hs
    have := hcount p hp hs
    rw [← hperm.count_eq, List.count_append, List.count_append] at this
    exact this
  have f1 : ∀ p ∈ R₁, C.side < p.side → p ∉ R₂ := by
    intro p hp hs hp2
    have := hcnt p (hR1Z p hp) hs
    have := List.count_pos_iff.2 hp; have := List.count_pos_iff.2 hp2
    omega
  have f2 : C.side < x.side → x ∉ R₁ ∧ x ∉ R₂ := by
    intro hs
    have := hcnt x hxZ hs
    have h0 : 0 < [x, y].count x := List.count_pos_iff.2 (by simp)
    exact ⟨fun h => by have := List.count_pos_iff.2 h; omega,
      fun h => by have := List.count_pos_iff.2 h; omega⟩
  have get : ∀ {R : List DyBox}, ∀ a ∈ x :: R ++ [y], ∀ a' ∈ x :: R ++ [y],
      C.side < a.side → C.side < a'.side → a ≠ a' → ∃ p ∈ R, C.side < p.side ∧ p ≠ x := by
    intro R a ha a' ha' hs hs' hne
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha ha'
    have hay : a ≠ y := fun e => hy (e ▸ hs)
    have hay' : a' ≠ y := fun e => hy (e ▸ hs')
    by_cases hax : a = x
    · rcases ha' with e | e | e
      · exact absurd (hax.trans e.symm) hne
      · exact ⟨a', e, hs', fun e' => hne (hax.trans e'.symm)⟩
      · exact absurd e hay'
    · rcases ha with e | e | e
      · exact absurd e hax
      · exact ⟨a, e, hs, hax⟩
      · exact absurd e hay
  by_contra hcon
  simp only [LeOneParent, not_or, not_forall] at hcon
  obtain ⟨⟨a, ha, a', ha', hsa, hsa', haa'⟩, ⟨b, hb, b', hb', hsb, hsb', hbb'⟩⟩ := hcon
  by_cases hxp : C.side < x.side
  · obtain ⟨p1, hp1, hs1, hp1x⟩ := get a ha a' ha' hsa hsa' haa'
    obtain ⟨p2, hp2, hs2, hp2x⟩ := get b hb b' hb' hsb hsb' hbb'
    have hp12 : p1 ≠ p2 := by rintro rfl; exact f1 p1 hp1 hs1 hp2
    have hx12 := f2 hxp
    -- the successor of a diagonal parent `p ∈ R` inside `x, R, y`
    have succ : ∀ {R : List DyBox}, (x :: R ++ [y]).IsChain Neighbour → (∀ c ∈ R, c ∈ Z) →
        ∀ p ∈ R, ∀ q, (∀ z, IsCell m δ z → Neighbour p z →
          (z.closedBox ∩ C.largeBox).Nonempty → z = x ∨ z = q) →
        C.side < q.side → q ∉ R → x ∉ R → False := by
      intro R hW hRZ p hp q hdiag hq hqR hxR
      obtain ⟨S, T, rfl⟩ := List.append_of_mem hp
      rcases T with _ | ⟨z, T⟩
      · have hn : Neighbour p y := List.isChain_pair.1
          (hW.infix ⟨x :: S, [], by simp⟩)
        rcases hdiag y (hZ y (hmemZ y (by simp))).1 hn (hZ y (hmemZ y (by simp))).2 with e | e
        · exact hxy e.symm
        · exact hy (e ▸ hq)
      · have hn : Neighbour p z := List.isChain_pair.1
          (hW.infix ⟨x :: S, T ++ [y], by simp⟩)
        have hzZ := hRZ z (by simp)
        rcases hdiag z (hZ z hzZ).1 hn (hZ z hzZ).2 with e | e
        · exact hxR (by rw [← e]; simp)
        · exact hqR (by rw [← e]; simp)
    rcases three_parents hC (hpar x hxZ hxp) (hpar p1 (hR1Z p1 hp1) hs1) (hpar p2 (hR2Z p2 hp2) hs2)
      hp1x.symm hp2x.symm hp12 with h | h | h
    · rcases h w hwc hw hwL with e | e
      · exact hwZ (e ▸ hR1Z p1 hp1)
      · exact hwZ (e ▸ hR2Z p2 hp2)
    · exact succ hW₁ hR1Z p1 hp1 p2 h hs2 (fun h' => f1 p2 h' hs2 hp2) hx12.1
    · exact succ hW₂ hR2Z p2 hp2 p1 (fun z hz hn hzL => (h z hz hn hzL)) hs1
        (f1 p1 hp1 hs1) hx12.2
  · have inR : ∀ {R : List DyBox}, ∀ c ∈ x :: R ++ [y], C.side < c.side → c ∈ R := by
      intro R c hc hs
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
      rcases hc with e | e | e
      · exact absurd (e ▸ hs) hxp
      · exact e
      · exact absurd (e ▸ hs) hy
    have ha1 := inR a ha hsa; have ha2 := inR a' ha' hsa'
    have hb1 := inR b hb hsb; have hb2 := inR b' hb' hsb'
    have ne : ∀ {c c'}, c ∈ R₁ → c' ∈ R₂ → C.side < c.side → c ≠ c' := by
      intro c c' hc hc' hs e; exact f1 c hc hs (e ▸ hc')
    exact no_four_parents hC (hpar a (hR1Z a ha1) hsa) (hpar a' (hR1Z a' ha2) hsa')
      (hpar b (hR2Z b hb1) hsb) (hpar b' (hR2Z b' hb2) hsb') haa' (ne ha1 hb1 hsa)
      (ne ha1 hb2 hsa) (ne ha2 hb1 hsa') (ne ha2 hb2 hsa') hbb'

lemma leOneParent_rev {C x y : DyBox} {R : List DyBox}
    (h : LeOneParent C (y :: R.reverse ++ [x])) : LeOneParent C (x :: R ++ [y]) := by
  intro c hc c' hc' hs hs'
  refine h c ?_ c' ?_ hs hs' <;> simp only [List.cons_append, List.mem_cons, List.mem_append,
    List.mem_reverse, List.mem_singleton] at hc hc' ⊢ <;> tauto

lemma isChain_rev {x y : DyBox} {R : List DyBox} (h : (x :: R ++ [y]).IsChain Neighbour) :
    (y :: R.reverse ++ [x]).IsChain Neighbour := by
  have := List.isChain_reverse.2 (h.imp fun a b h => Neighbour.symm h)
  simpa using this

/-- **One of the two segments has at most one parent** (DZZ l. 1471–1488, D93), unless
`𝖢_{i,1}` and `𝖢_{i,2}` are both parents (Case 3). -/
theorem pick_arc {C x y w w' : DyBox} {R₁ R₂ Z : List DyBox} (hC : IsCell m δ C)
    (hW₁ : (x :: R₁ ++ [y]).IsChain Neighbour) (hW₂ : (x :: R₂ ++ [y]).IsChain Neighbour)
    (hperm : (R₁ ++ R₂ ++ [x, y]).Perm Z)
    (hZ : ∀ c ∈ Z, IsCell m δ c ∧ (c.closedBox ∩ C.largeBox).Nonempty)
    (hcount : ∀ p ∈ Z, C.side < p.side → Z.count p = 1) (hxy : x ≠ y)
    (hw : Neighbour x w) (hwc : IsCell m δ w) (hwL : (w.closedBox ∩ C.largeBox).Nonempty)
    (hwZ : w ∉ Z) (hw' : Neighbour w' y) (hwc' : IsCell m δ w')
    (hwL' : (w'.closedBox ∩ C.largeBox).Nonempty) (hwZ' : w' ∉ Z)
    (hnot : ¬ (C.side < x.side ∧ C.side < y.side)) :
    LeOneParent C (x :: R₁ ++ [y]) ∨ LeOneParent C (x :: R₂ ++ [y]) := by
  by_cases hy : C.side < y.side
  · have hx : ¬ C.side < x.side := fun h => hnot ⟨h, hy⟩
    have hperm' : (R₁.reverse ++ R₂.reverse ++ [y, x]).Perm Z := by
      refine List.Perm.trans ?_ hperm
      rw [List.perm_iff_count]; intro a
      simp only [List.count_append, List.count_reverse, List.count_cons, List.count_nil]
      omega
    rcases pick_arc_x hC (isChain_rev hW₁) (isChain_rev hW₂) hperm' hZ hcount hxy.symm hw'.symm
      hwc' hwL' hwZ' hx with h | h
    · exact Or.inl (leOneParent_rev h)
    · exact Or.inr (leOneParent_rev h)
  · exact pick_arc_x hC hW₁ hW₂ hperm hZ hcount hxy hw hwc hwL hwZ hy

end DZZ
end LQGMetric
