import LatticeProb.Topology.ArcCharacterization
import LatticeProb.Topology.ArcUnion
import LatticeProb.Topology.NonCutPoints

/-!
# R. L. Moore's characterisation of the simple closed curve

A compact connected second countable Hausdorff space `X` with two points, such that `X \ {a, b}` is disconnected
for all `a ≠ b`, is homeomorphic to a circle (R. L. Moore; Kuratowski, *Topology II*, §47-49; Nadler, *Continuum
Theory*, Chapter IX). The proof:

* `isPreconnected_compl_singleton_of_forall_not_isPreconnected_compl_pair`: such a space has no cut point. If
  `X \ {p} = U ∪ V` were a separation, pick non-cut points `q ∈ U` and `r ∈ V` of `X`; then
  `X \ {q, r} = ((U ∪ {p}) \ {q}) ∪ ((V ∪ {p}) \ {r})` is a union of two connected sets through `p`;
* for a separation `X \ {a, b} = U ∪ V`: `closure U ⊆ U ∪ {a, b}`, `a ∈ closure U`, and `A = U ∪ {a, b}` is a
  closed connected set (`isPreconnected_insert_insert_of_union_eq_compl_pair`); `a` and `b` are non-cut points of
  `A` (`isPreconnected_insert_of_union_eq_compl_pair`); a splitting of `A \ {x}`, `x ∈ U`, separates `a` from `b`
  (`diff_singleton_inter_eq_empty_of_union_eq_compl_pair`); hence every `x ∈ U` is a cut point of `A`
  (`not_isPreconnected_diff_singleton_of_union_eq_compl_pair`);
* `exists_arc_of_union_eq_compl_pair`: by the characterisation of the arc, `A` is an arc from `a` to `b`;
* `nonempty_homeomorph_circle_of_forall_not_isPreconnected_compl_pair`: the two arcs `U ∪ {a, b}` and
  `V ∪ {a, b}` meet only at `a` and `b`, so `X` is a circle; for plane sets:
  `nonempty_homeomorph_circle_of_forall_not_isPreconnected_diff_pair`.

Separations are written as two disjoint open subsets of `X` covering the open set in question; in a `T₁` space
`X \ {a, b}` is open.
-/

namespace LatticeProb.Topology

open Set

variable {X : Type*} [TopologicalSpace X]

/-- A disconnected open set `O` is the union of two disjoint nonempty open sets. -/
theorem exists_separation_of_isOpen_of_not_isPreconnected {O : Set X} (hO : IsOpen O)
    (h : ¬ IsPreconnected O) :
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ Disjoint A B ∧ A ∪ B = O ∧ A.Nonempty ∧ B.Nonempty := by
  simp only [IsPreconnected, not_forall, not_nonempty_iff_eq_empty] at h
  obtain ⟨u, v, hu, hv, hsuv, hsu, hsv, hne⟩ := h
  refine ⟨O ∩ u, O ∩ v, hO.inter hu, hO.inter hv, ?_, ?_, hsu, hsv⟩
  · refine Set.disjoint_left.2 fun y hy hy' => ?_
    have hy'' : y ∈ O ∩ (u ∩ v) := ⟨hy.1, hy.2, hy'.2⟩
    rw [hne] at hy''
    exact hy''
  · rw [← inter_union_distrib_left]
    exact inter_eq_left.2 hsuv

/-- If `U` and `V` are disjoint open sets covering `X \ {p}` and `q ∈ U` is a non-cut point of `X`, then
`(U ∪ {p}) \ {q}` is connected. -/
theorem isPreconnected_insert_diff_singleton_of_union_eq_compl_singleton {p q : X} {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcover : U ∪ V = {p}ᶜ) (hqU : q ∈ U)
    (hq : IsPreconnected ({q}ᶜ : Set X)) : IsPreconnected (insert p U \ {q}) := by
  have hpU : p ∉ U := fun h => by
    have : p ∈ U ∪ V := Or.inl h
    rw [hcover] at this
    exact this (mem_singleton p)
  have hpq : p ≠ q := fun h => hpU (h ▸ hqU)
  have key : ∀ u v : Set X, IsOpen u → IsOpen v → insert p U \ {q} ⊆ u ∪ v →
      (insert p U \ {q}) ∩ (u ∩ v) = ∅ → p ∈ u → ((insert p U \ {q}) ∩ v).Nonempty → False := by
    intro u v hu hv hsub hne hpu hSv
    obtain ⟨z, hzS, hzv⟩ := hSv
    have hzp : z ≠ p := fun h => by
      have : p ∈ (insert p U \ {q}) ∩ (u ∩ v) := ⟨⟨mem_insert p U, hpq⟩, hpu, h ▸ hzv⟩
      rw [hne] at this
      exact this
    have hzU : z ∈ U := hzS.1.resolve_left hzp
    have hcov : ({q}ᶜ : Set X) ⊆ (u ∪ V) ∪ (v ∩ U) := by
      intro y hy
      by_cases hyp : y = p
      · exact Or.inl (Or.inl (hyp ▸ hpu))
      · have hyUV : y ∈ U ∪ V := hcover ▸ mem_compl_singleton_iff.2 hyp
        rcases hyUV with hyU | hyV
        · rcases hsub ⟨mem_insert_of_mem p hyU, hy⟩ with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr ⟨h, hyU⟩
        · exact Or.inl (Or.inr hyV)
    obtain ⟨w, hwq, hwu, hwv⟩ := hq (u ∪ V) (v ∩ U) (hu.union hV) (hv.inter hU) hcov
      ⟨p, mem_compl_singleton_iff.2 hpq, Or.inl hpu⟩ ⟨z, hzS.2, hzv, hzU⟩
    have hwu' : w ∈ u := hwu.resolve_right fun h => disjoint_left.1 hUV hwv.2 h
    have : w ∈ (insert p U \ {q}) ∩ (u ∩ v) := ⟨⟨mem_insert_of_mem p hwv.2, hwq⟩, hwu', hwv.1⟩
    rw [hne] at this
    exact this
  intro u v hu hv hsub hSu hSv
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  rcases hsub ⟨mem_insert p U, hpq⟩ with hpu | hpv
  · exact key u v hu hv hsub hne hpu hSv
  · exact key v u hv hu (by rwa [union_comm]) (by rwa [inter_comm v u]) hpv hSu

/-- **No cut points.** In a compact connected `T₁` space in which `X \ {a, b}` is disconnected for all `a ≠ b`,
every `X \ {p}` is connected. -/
theorem isPreconnected_compl_singleton_of_forall_not_isPreconnected_compl_pair [T1Space X] [CompactSpace X]
    [ConnectedSpace X] (hpair : ∀ a b : X, a ≠ b → ¬ IsPreconnected ({a, b}ᶜ : Set X)) (p : X) :
    IsPreconnected ({p}ᶜ : Set X) := by
  by_contra hp
  obtain ⟨U, V, hU, hV, hUV, hcover, hUne, hVne⟩ := exists_separation_of_not_isPreconnected_compl_singleton hp
  have hcover' : V ∪ U = {p}ᶜ := (union_comm V U).trans hcover
  obtain ⟨q, hqU, hq⟩ :=
    exists_isPreconnected_compl_singleton_mem_of_union_eq_compl_singleton hU hV hUV hcover hUne
  obtain ⟨r, hrV, hr⟩ :=
    exists_isPreconnected_compl_singleton_mem_of_union_eq_compl_singleton hV hU hUV.symm hcover' hVne
  have hqr : q ≠ r := fun h => disjoint_left.1 hUV hqU (h ▸ hrV)
  have hpq : p ≠ q := fun h => by
    have : q ∈ U ∪ V := Or.inl hqU
    rw [hcover] at this
    exact this h.symm
  have hpr : p ≠ r := fun h => by
    have : r ∈ U ∪ V := Or.inr hrV
    rw [hcover] at this
    exact this h.symm
  have h1 := isPreconnected_insert_diff_singleton_of_union_eq_compl_singleton hU hV hUV hcover hqU hq
  have h2 := isPreconnected_insert_diff_singleton_of_union_eq_compl_singleton hV hU hUV.symm hcover' hrV hr
  have heq : ({q, r}ᶜ : Set X) = (insert p U \ {q}) ∪ (insert p V \ {r}) := by
    ext z
    have hz : z = p ∨ z ∈ U ∨ z ∈ V := by
      by_cases h : z = p
      · exact Or.inl h
      · have : z ∈ U ∪ V := hcover ▸ mem_compl_singleton_iff.2 h
        exact Or.inr this
    constructor
    · intro hzqr
      have hzq : z ≠ q := fun h => hzqr (Or.inl h)
      have hzr : z ≠ r := fun h => hzqr (Or.inr h)
      rcases hz with h | h | h
      · exact Or.inl ⟨Or.inl h, hzq⟩
      · exact Or.inl ⟨Or.inr h, hzq⟩
      · exact Or.inr ⟨Or.inr h, hzr⟩
    · rintro (⟨h | h, hzq⟩ | ⟨h | h, hzr⟩) hzqr
      · rw [h] at hzqr
        rcases hzqr with h' | h'
        · exact hpq h'
        · exact hpr h'
      · rcases hzqr with h' | h'
        · exact hzq h'
        · exact disjoint_left.1 hUV h (h' ▸ hrV)
      · rw [h] at hzqr
        rcases hzqr with h' | h'
        · exact hpq h'
        · exact hpr h'
      · rcases hzqr with h' | h'
        · exact disjoint_left.1 hUV (h' ▸ hqU) h
        · exact hzr h'
  apply hpair q r hqr
  rw [heq]
  exact IsPreconnected.union p ⟨mem_insert p U, hpq⟩ ⟨mem_insert p V, hpr⟩ h1 h2

section Pair

variable {a b : X} {U V : Set X}

omit [TopologicalSpace X] in
/-- The points of a side `U` of a separation of `X \ {a, b}` differ from `a` and from `b`. -/
theorem ne_and_ne_of_mem_of_union_eq_compl_pair (hcover : U ∪ V = ({a, b}ᶜ : Set X)) {z : X} (hz : z ∈ U) :
    z ≠ a ∧ z ≠ b := by
  have : z ∈ ({a, b}ᶜ : Set X) := hcover ▸ Or.inl hz
  exact ⟨fun h => this (Or.inl h), fun h => this (Or.inr h)⟩

omit [TopologicalSpace X] in
/-- For a separation `X \ {a, b} = U ∪ V`, the set `U ∪ {a, b}` is the complement of `V`. -/
theorem insert_insert_eq_compl_of_union_eq_compl_pair (hUV : Disjoint U V)
    (hcover : U ∪ V = ({a, b}ᶜ : Set X)) : insert a (insert b U) = Vᶜ := by
  ext z
  constructor
  · intro hz hzV
    have : z ∈ ({a, b}ᶜ : Set X) := hcover ▸ Or.inr hzV
    rcases hz with h | h | h
    · exact this (Or.inl h)
    · exact this (Or.inr h)
    · exact disjoint_left.1 hUV h hzV
  · intro hz
    by_cases hza : z = a
    · exact Or.inl hza
    by_cases hzb : z = b
    · exact Or.inr (Or.inl hzb)
    have hzab : z ∉ ({a, b} : Set X) := fun h => h.elim hza hzb
    have : z ∈ U ∪ V := hcover ▸ hzab
    exact Or.inr (Or.inr (this.resolve_right hz))

/-- **The closure of a side.** For a separation `X \ {a, b} = U ∪ V` into disjoint open sets,
`closure U ⊆ U ∪ {a, b}`. -/
theorem closure_subset_insert_insert_of_union_eq_compl_pair (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = ({a, b}ᶜ : Set X)) : closure U ⊆ insert a (insert b U) := by
  rw [insert_insert_eq_compl_of_union_eq_compl_pair hUV hcover]
  exact closure_minimal (fun z hz => disjoint_left.1 hUV hz) hV.isClosed_compl

/-- **Both separating points are limit points of each side.** If `X \ {b}` is connected and `X \ {a, b} = U ∪ V`
is a separation into disjoint open sets with `U` nonempty, then `a ∈ closure U`. -/
theorem mem_closure_of_union_eq_compl_pair (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = ({a, b}ᶜ : Set X)) (hU : IsOpen U) (hUne : U.Nonempty) (hab : a ≠ b)
    (hb : IsPreconnected ({b}ᶜ : Set X)) : a ∈ closure U := by
  by_contra ha
  have hcl := closure_subset_insert_insert_of_union_eq_compl_pair hV hUV hcover
  have hsub : ({b}ᶜ : Set X) ⊆ U ∪ (closure U)ᶜ := fun z hz => by
    by_cases hzc : z ∈ closure U
    · left
      rcases hcl hzc with h | h | h
      · exact absurd (h ▸ hzc) ha
      · exact absurd h hz
      · exact h
    · exact Or.inr hzc
  have hdisj : Disjoint U (closure U)ᶜ := disjoint_left.2 fun z hz hz' => hz' (subset_closure hz)
  rcases hb.subset_or_subset hU isClosed_closure.isOpen_compl hdisj hsub with h | h
  · exact (ne_and_ne_of_mem_of_union_eq_compl_pair hcover (h (mem_compl_singleton_iff.2 hab))).1 rfl
  · obtain ⟨u, hu⟩ := hUne
    exact h (mem_compl_singleton_iff.2 (ne_and_ne_of_mem_of_union_eq_compl_pair hcover hu).2) (subset_closure hu)

/-- **A side together with the two separating points is a continuum.** In a connected space in which `X \ {a}`
and `X \ {b}` are connected, if `X \ {a, b} = U ∪ V` is a separation into disjoint open sets with `U` nonempty,
then `U ∪ {a, b}` is connected (and closed, being the complement of `V`). -/
theorem isPreconnected_insert_insert_of_union_eq_compl_pair [PreconnectedSpace X] (hU : IsOpen U)
    (hV : IsOpen V) (hUV : Disjoint U V) (hcover : U ∪ V = ({a, b}ᶜ : Set X)) (hUne : U.Nonempty)
    (hab : a ≠ b) (ha : IsPreconnected ({a}ᶜ : Set X)) (hb : IsPreconnected ({b}ᶜ : Set X)) :
    IsPreconnected (insert a (insert b U)) := by
  have hA_closed : IsClosed (insert a (insert b U)) := by
    rw [insert_insert_eq_compl_of_union_eq_compl_pair hUV hcover]
    exact hV.isClosed_compl
  have hacl := mem_closure_of_union_eq_compl_pair hV hUV hcover hU hUne hab hb
  have key : ∀ u v : Set X, IsOpen u → IsOpen v → insert a (insert b U) ⊆ u ∪ v →
      insert a (insert b U) ∩ (u ∩ v) = ∅ → a ∈ u → (insert a (insert b U) ∩ v).Nonempty → False := by
    intro u v hu hv hsub hne hau hAv
    have hnot : ∀ y ∈ insert a (insert b U), y ∈ u → y ∉ v := fun y hy hyu hyv => by
      have : y ∈ insert a (insert b U) ∩ (u ∩ v) := ⟨hy, hyu, hyv⟩
      rw [hne] at this
      exact this
    have haA : a ∈ insert a (insert b U) := mem_insert a _
    have hbA : b ∈ insert a (insert b U) := mem_insert_of_mem a (mem_insert b U)
    have hUA : ∀ y ∈ U, y ∈ insert a (insert b U) := fun y hy => mem_insert_of_mem a (mem_insert_of_mem b hy)
    rcases hsub hbA with hbu | hbv
    · -- `b ∈ u`: the part of `U ∪ {a, b}` in `v` lies in `U`, and it is clopen in `X`
      have hopen : IsOpen (insert a (insert b U) ∩ v) := by
        have : insert a (insert b U) ∩ v = U ∩ v := by
          ext y
          constructor
          · rintro ⟨hy, hyv⟩
            rcases hy with h | h | h
            · rw [h] at hyv
              exact absurd hyv (hnot a haA hau)
            · rw [h] at hyv
              exact absurd hyv (hnot b hbA hbu)
            · exact ⟨h, hyv⟩
          · rintro ⟨hy, hyv⟩
            exact ⟨hUA y hy, hyv⟩
        rw [this]
        exact hU.inter hv
      have hclosed : IsClosed (insert a (insert b U) ∩ v) := by
        have : insert a (insert b U) ∩ v = insert a (insert b U) \ u := by
          ext y
          constructor
          · rintro ⟨hy, hyv⟩
            exact ⟨hy, fun hyu => hnot y hy hyu hyv⟩
          · rintro ⟨hy, hyu⟩
            exact ⟨hy, (hsub hy).resolve_left hyu⟩
        rw [this]
        exact hA_closed.sdiff hu
      rcases isClopen_iff.1 ⟨hclosed, hopen⟩ with h | h
      · obtain ⟨z, hz⟩ := hAv
        rw [h] at hz
        exact hz
      · have : a ∈ insert a (insert b U) ∩ v := h ▸ mem_univ a
        exact hnot a haA hau this.2
    · -- `b ∈ v`: the part of `U ∪ {a, b}` in `u`, minus `a`, is clopen in `X \ {a}`
      have hcov : ({a}ᶜ : Set X) ⊆ (U ∩ u) ∪ (insert a (insert b U) \ v)ᶜ := by
        intro y hy
        by_cases hyAv : y ∈ insert a (insert b U) \ v
        · left
          have hyu : y ∈ u := (hsub hyAv.1).resolve_right hyAv.2
          rcases hyAv.1 with h | h | h
          · exact absurd h hy
          · exact absurd (h ▸ hbv) hyAv.2
          · exact ⟨h, hyu⟩
        · exact Or.inr hyAv
      have hdisj : Disjoint (U ∩ u) (insert a (insert b U) \ v)ᶜ :=
        disjoint_left.2 fun y hy hy' => hy' ⟨hUA y hy.1, hnot y (hUA y hy.1) hy.2⟩
      rcases ha.subset_or_subset (hU.inter hu) (hA_closed.sdiff hv).isOpen_compl hdisj hcov with h | h
      · exact (ne_and_ne_of_mem_of_union_eq_compl_pair hcover (h (mem_compl_singleton_iff.2 hab.symm)).1).2 rfl
      · obtain ⟨w, hwu, hwU⟩ := mem_closure_iff.1 hacl u hu hau
        have hwa : w ≠ a := (ne_and_ne_of_mem_of_union_eq_compl_pair hcover hwU).1
        exact h (mem_compl_singleton_iff.2 hwa) ⟨hUA w hwU, hnot w (hUA w hwU) hwu⟩
  intro u v hu hv hsub hAu hAv
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  rcases hsub (mem_insert a _) with hau | hav
  · exact key u v hu hv hsub hne hau hAv
  · exact key v u hv hu (by rwa [union_comm]) (by rwa [inter_comm v u]) hav hAu

/-- **The separating points are non-cut points of a side.** If `X \ {a}` is connected and `X \ {a, b} = U ∪ V` is a
separation into disjoint open sets, then `(U ∪ {a, b}) \ {a} = U ∪ {b}` is connected. -/
theorem isPreconnected_insert_of_union_eq_compl_pair (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = ({a, b}ᶜ : Set X)) (hab : a ≠ b) (ha : IsPreconnected ({a}ᶜ : Set X)) :
    IsPreconnected (insert b U) := by
  have key : ∀ u v : Set X, IsOpen u → IsOpen v → insert b U ⊆ u ∪ v →
      insert b U ∩ (u ∩ v) = ∅ → b ∈ u → (insert b U ∩ v).Nonempty → False := by
    intro u v hu hv hsub hne hbu hSv
    have hnot : ∀ y ∈ insert b U, y ∈ u → y ∉ v := fun y hy hyu hyv => by
      have : y ∈ insert b U ∩ (u ∩ v) := ⟨hy, hyu, hyv⟩
      rw [hne] at this
      exact this
    have hcov : ({a}ᶜ : Set X) ⊆ (U ∩ v) ∪ (V ∪ u) := by
      intro y hy
      by_cases hyb : y = b
      · rw [hyb]
        exact Or.inr (Or.inr hbu)
      have hyab : y ∉ ({a, b} : Set X) := fun h => h.elim hy hyb
      have hyUV : y ∈ U ∪ V := hcover ▸ hyab
      rcases hyUV with hyU | hyV
      · rcases hsub (mem_insert_of_mem b hyU) with h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl ⟨hyU, h⟩
      · exact Or.inr (Or.inl hyV)
    have hdisj : Disjoint (U ∩ v) (V ∪ u) := disjoint_left.2 fun y hy hy' => by
      rcases hy' with h | h
      · exact disjoint_left.1 hUV hy.1 h
      · exact hnot y (mem_insert_of_mem b hy.1) h hy.2
    rcases ha.subset_or_subset (hU.inter hv) (hV.union hu) hdisj hcov with h | h
    · exact (ne_and_ne_of_mem_of_union_eq_compl_pair hcover (h (mem_compl_singleton_iff.2 hab.symm)).1).2 rfl
    · obtain ⟨w, hwS, hwv⟩ := hSv
      have hwb : w ≠ b := fun h' => hnot b (mem_insert b U) hbu (h' ▸ hwv)
      have hwU : w ∈ U := hwS.resolve_left hwb
      have hwa : w ≠ a := (ne_and_ne_of_mem_of_union_eq_compl_pair hcover hwU).1
      rcases h (mem_compl_singleton_iff.2 hwa) with h' | h'
      · exact disjoint_left.1 hUV hwU h'
      · exact hnot w hwS h' hwv
  intro u v hu hv hsub hSu hSv
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  rcases hsub (mem_insert b U) with hbu | hbv
  · exact key u v hu hv hsub hne hbu hSv
  · exact key v u hv hu (by rwa [union_comm]) (by rwa [inter_comm v u]) hbv hSu

/-- **A splitting of a side minus a point separates `a` from `b`.** In a `T₁` space, let `X \ {a, b} = U ∪ V` be a
separation into disjoint open sets and let `x ∈ U` be a non-cut point of `X`. If the open sets `u` and `v` cover
`(U ∪ {a, b}) \ {x}`, do not meet on it, and `a, b ∈ u`, then `(U ∪ {a, b}) \ {x}` does not meet `v`. -/
theorem diff_singleton_inter_eq_empty_of_union_eq_compl_pair [T1Space X] (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hcover : U ∪ V = ({a, b}ᶜ : Set X)) {x : X} (hxU : x ∈ U)
    (hx : IsPreconnected ({x}ᶜ : Set X)) {u v : Set X} (hu : IsOpen u) (hv : IsOpen v)
    (hsub : insert a (insert b U) \ {x} ⊆ u ∪ v) (hne : insert a (insert b U) \ {x} ∩ (u ∩ v) = ∅)
    (hau : a ∈ u) (hbu : b ∈ u) : insert a (insert b U) \ {x} ∩ v = ∅ := by
  have hnot : ∀ y ∈ insert a (insert b U) \ {x}, y ∈ u → y ∉ v := fun y hy hyu hyv => by
    have : y ∈ insert a (insert b U) \ {x} ∩ (u ∩ v) := ⟨hy, hyu, hyv⟩
    rw [hne] at this
    exact this
  have hxa : x ≠ a := (ne_and_ne_of_mem_of_union_eq_compl_pair hcover hxU).1
  have hmem : ∀ y ∈ U, y ≠ x → y ∈ insert a (insert b U) \ {x} := fun y hy hyx =>
    ⟨mem_insert_of_mem a (mem_insert_of_mem b hy), hyx⟩
  have hcov : ({x}ᶜ : Set X) ⊆ (U ∩ v ∩ {x}ᶜ) ∪ (V ∪ u) := by
    intro y hy
    have hyx : y ≠ x := hy
    by_cases hya : y = a
    · rw [hya]
      exact Or.inr (Or.inr hau)
    by_cases hyb : y = b
    · rw [hyb]
      exact Or.inr (Or.inr hbu)
    have hyab : y ∉ ({a, b} : Set X) := fun h => h.elim hya hyb
    have hyUV : y ∈ U ∪ V := hcover ▸ hyab
    rcases hyUV with hyU | hyV
    · rcases hsub (hmem y hyU hyx) with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl ⟨⟨hyU, h⟩, hy⟩
    · exact Or.inr (Or.inl hyV)
  have hdisj : Disjoint (U ∩ v ∩ {x}ᶜ) (V ∪ u) := disjoint_left.2 fun y hy hy' => by
    rcases hy' with h | h
    · exact disjoint_left.1 hUV hy.1.1 h
    · exact hnot y (hmem y hy.1.1 hy.2) h hy.1.2
  rcases hx.subset_or_subset ((hU.inter hv).inter isOpen_compl_singleton) (hV.union hu) hdisj hcov with h | h
  · exfalso
    exact (ne_and_ne_of_mem_of_union_eq_compl_pair hcover (h (mem_compl_singleton_iff.2 hxa.symm)).1.1).1 rfl
  · refine eq_empty_iff_forall_notMem.2 fun w hw => ?_
    obtain ⟨hwA, hwv⟩ := hw
    rcases hwA.1 with h' | h' | h'
    · exact hnot w hwA (by rw [h']; exact hau) hwv
    · exact hnot w hwA (by rw [h']; exact hbu) hwv
    · rcases h (mem_compl_singleton_iff.2 hwA.2) with h'' | h''
      · exact disjoint_left.1 hUV h' h''
      · exact hnot w hwA h'' hwv

/-- **Every point of a side is a cut point of the side.** In a `T₁` space without cut points in which
`X \ {x, y}` is disconnected for all `x ≠ y`, let `X \ {a, b} = U ∪ V` be a separation into disjoint open sets with
`V` nonempty. Then `(U ∪ {a, b}) \ {x}` is disconnected for every `x ∈ U`: otherwise, for `y ∈ V`,
`X \ {x, y} = ((U ∪ {a, b}) \ {x}) ∪ ((V ∪ {a, b}) \ {y})` would be connected, since a splitting of the second set
that keeps `a` and `b` on one side is trivial. -/
theorem not_isPreconnected_diff_singleton_of_union_eq_compl_pair [T1Space X]
    (hpair : ∀ x y : X, x ≠ y → ¬ IsPreconnected ({x, y}ᶜ : Set X))
    (hcut : ∀ p : X, IsPreconnected ({p}ᶜ : Set X)) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = ({a, b}ᶜ : Set X)) (hVne : V.Nonempty) {x : X} (hxU : x ∈ U) :
    ¬ IsPreconnected (insert a (insert b U) \ {x}) := by
  intro hA
  obtain ⟨y, hyV⟩ := hVne
  have hcover' : V ∪ U = ({a, b}ᶜ : Set X) := (union_comm V U).trans hcover
  have hxa : x ≠ a := (ne_and_ne_of_mem_of_union_eq_compl_pair hcover hxU).1
  have hxb : x ≠ b := (ne_and_ne_of_mem_of_union_eq_compl_pair hcover hxU).2
  have hya : y ≠ a := (ne_and_ne_of_mem_of_union_eq_compl_pair hcover' hyV).1
  have hyb : y ≠ b := (ne_and_ne_of_mem_of_union_eq_compl_pair hcover' hyV).2
  have hxy : x ≠ y := fun h => disjoint_left.1 hUV hxU (by rw [h]; exact hyV)
  have heq : ({x, y}ᶜ : Set X) = (insert a (insert b U) \ {x}) ∪ (insert a (insert b V) \ {y}) := by
    ext z
    constructor
    · intro hz
      have hzx : z ≠ x := fun h => hz (Or.inl h)
      have hzy : z ≠ y := fun h => hz (Or.inr h)
      by_cases hza : z = a
      · exact Or.inl ⟨Or.inl hza, hzx⟩
      by_cases hzb : z = b
      · exact Or.inl ⟨Or.inr (Or.inl hzb), hzx⟩
      have hzab : z ∉ ({a, b} : Set X) := fun h => h.elim hza hzb
      have hzUV : z ∈ U ∪ V := hcover ▸ hzab
      rcases hzUV with h | h
      · exact Or.inl ⟨Or.inr (Or.inr h), hzx⟩
      · exact Or.inr ⟨Or.inr (Or.inr h), hzy⟩
    · rintro (⟨hz, hzx⟩ | ⟨hz, hzy⟩) hzxy
      · rcases hzxy with h | h
        · exact hzx h
        · rcases hz with h' | h' | h'
          · exact hya (h.symm.trans h')
          · exact hyb (h.symm.trans h')
          · exact disjoint_left.1 hUV h' (by rw [h]; exact hyV)
      · rcases hzxy with h | h
        · rcases hz with h' | h' | h'
          · exact hxa (h.symm.trans h')
          · exact hxb (h.symm.trans h')
          · exact disjoint_left.1 hUV (by rw [h]; exact hxU) h'
        · exact hzy h
  apply hpair x y hxy
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsub hne
  rw [heq] at hsub hne ⊢
  have hsubA : insert a (insert b U) \ {x} ⊆ u ∪ v := fun z hz => hsub (Or.inl hz)
  have hsubB : insert a (insert b V) \ {y} ⊆ u ∪ v := fun z hz => hsub (Or.inr hz)
  have hneA : insert a (insert b U) \ {x} ∩ (u ∩ v) = ∅ :=
    subset_eq_empty (inter_subset_inter_left _ subset_union_left) hne
  have hneB : insert a (insert b V) \ {y} ∩ (u ∩ v) = ∅ :=
    subset_eq_empty (inter_subset_inter_left _ subset_union_right) hne
  have haA : a ∈ insert a (insert b U) \ {x} := ⟨mem_insert a _, hxa.symm⟩
  have hbA : b ∈ insert a (insert b U) \ {x} := ⟨mem_insert_of_mem a (mem_insert b U), hxb.symm⟩
  rcases (isPreconnected_iff_subset_of_disjoint.1 hA) u v hu hv hsubA hneA with h | h
  · have hB := diff_singleton_inter_eq_empty_of_union_eq_compl_pair hV hU hUV.symm hcover' hyV (hcut y) hu hv
      hsubB hneB (h haA) (h hbA)
    left
    rintro w (hw | hw)
    · exact h hw
    · refine (hsubB hw).resolve_right fun hwv => ?_
      have : w ∈ insert a (insert b V) \ {y} ∩ v := ⟨hw, hwv⟩
      rw [hB] at this
      exact this
  · have hB := diff_singleton_inter_eq_empty_of_union_eq_compl_pair hV hU hUV.symm hcover' hyV (hcut y) hv hu
      (by rwa [union_comm]) (by rwa [inter_comm v u]) (h haA) (h hbA)
    right
    rintro w (hw | hw)
    · exact h hw
    · refine (hsubB hw).resolve_left fun hwu => ?_
      have : w ∈ insert a (insert b V) \ {y} ∩ u := ⟨hw, hwu⟩
      rw [hB] at this
      exact this

end Pair

/-- In a subspace `A`, the complement of a point `x` is connected iff `A \ {x}` is connected in `X`. -/
theorem isPreconnected_compl_singleton_subtype_iff {A : Set X} (x : A) :
    IsPreconnected ({x}ᶜ : Set A) ↔ IsPreconnected (A \ {(x : X)}) := by
  have h : ((↑) : A → X) '' ({x}ᶜ : Set A) = A \ {(x : X)} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, fun h => hw (Subtype.ext h)⟩
    · rintro ⟨hz, hzx⟩
      exact ⟨⟨z, hz⟩, fun h => hzx (congrArg Subtype.val h), rfl⟩
  rw [← h, Topology.IsInducing.subtypeVal.isPreconnected_image]

/-- `0` is a non-cut point of the unit interval. -/
theorem isPreconnected_compl_zero_unitInterval : IsPreconnected ({0}ᶜ : Set unitInterval) := by
  have h : (unitInterval : Set ℝ) \ {((0 : unitInterval) : ℝ)} = Ioc 0 1 := by
    show Icc (0 : ℝ) 1 \ {0} = Ioc 0 1
    exact Icc_sdiff_left
  rw [isPreconnected_compl_singleton_subtype_iff, h]
  exact isPreconnected_Ioc

/-- `1` is a non-cut point of the unit interval. -/
theorem isPreconnected_compl_one_unitInterval : IsPreconnected ({1}ᶜ : Set unitInterval) := by
  have h : (unitInterval : Set ℝ) \ {((1 : unitInterval) : ℝ)} = Ico 0 1 := by
    show Icc (0 : ℝ) 1 \ {1} = Ico 0 1
    exact Icc_sdiff_right
  rw [isPreconnected_compl_singleton_subtype_iff, h]
  exact isPreconnected_Ico

/-- **Each side is an arc from `a` to `b`.** Let `X` be a compact connected second countable `T₁` space in which
`X \ {x, y}` is disconnected for all `x ≠ y`, and let `X \ {a, b} = U ∪ V` be a separation into disjoint nonempty
open sets. Then `U ∪ {a, b}` is the range of a continuous injective path from `a` to `b`: its only non-cut points
are `a` and `b`, so the characterisation of the arc applies. -/
theorem exists_arc_of_union_eq_compl_pair [T1Space X] [CompactSpace X] [ConnectedSpace X]
    [SecondCountableTopology X] (hpair : ∀ x y : X, x ≠ y → ¬ IsPreconnected ({x, y}ᶜ : Set X))
    {a b : X} {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = ({a, b}ᶜ : Set X)) (hUne : U.Nonempty) (hVne : V.Nonempty) (hab : a ≠ b) :
    ∃ f : unitInterval → X, Continuous f ∧ Function.Injective f ∧ f 0 = a ∧ f 1 = b ∧
      range f = insert a (insert b U) := by
  have hcut := isPreconnected_compl_singleton_of_forall_not_isPreconnected_compl_pair hpair
  have hcover' : U ∪ V = ({b, a}ᶜ : Set X) := by
    rw [pair_comm]
    exact hcover
  have hAcl : IsClosed (insert a (insert b U)) := by
    rw [insert_insert_eq_compl_of_union_eq_compl_pair hUV hcover]
    exact hV.isClosed_compl
  have hApre : IsPreconnected (insert a (insert b U)) :=
    isPreconnected_insert_insert_of_union_eq_compl_pair hU hV hUV hcover hUne hab (hcut a) (hcut b)
  have haA : a ∈ insert a (insert b U) := mem_insert a _
  have hbA : b ∈ insert a (insert b U) := mem_insert_of_mem a (mem_insert b U)
  have haU : a ∉ insert b U := fun h =>
    h.elim hab fun h' => (ne_and_ne_of_mem_of_union_eq_compl_pair hcover h').1 rfl
  have hbU : b ∉ insert a U := fun h =>
    h.elim hab.symm fun h' => (ne_and_ne_of_mem_of_union_eq_compl_pair hcover h').2 rfl
  set A : Set X := insert a (insert b U) with hAdef
  have : CompactSpace A := isCompact_iff_compactSpace.1 hAcl.isCompact
  have : ConnectedSpace A := Subtype.connectedSpace ⟨⟨a, haA⟩, hApre⟩
  have honly : ∀ x : A,
      IsPreconnected ({x}ᶜ : Set A) ↔ x = ⟨a, haA⟩ ∨ x = ⟨b, hbA⟩ := by
    rintro ⟨z, hz⟩
    rw [isPreconnected_compl_singleton_subtype_iff, Subtype.mk.injEq, Subtype.mk.injEq]
    constructor
    · intro h
      rcases hz with hza | hzb | hzU
      · exact Or.inl hza
      · exact Or.inr hzb
      · exact absurd h
          (not_isPreconnected_diff_singleton_of_union_eq_compl_pair hpair hcut hU hV hUV hcover hVne hzU)
    · rintro (hza | hzb)
      · have hsub : A \ {z} = insert b U := by
          rw [hza, hAdef]
          exact insert_sdiff_self_of_notMem haU
        rw [hsub]
        exact isPreconnected_insert_of_union_eq_compl_pair hU hV hUV hcover hab (hcut a)
      · have hsub : A \ {z} = insert a U := by
          rw [hzb, hAdef, insert_comm]
          exact insert_sdiff_self_of_notMem hbU
        rw [hsub]
        exact isPreconnected_insert_of_union_eq_compl_pair hU hV hUV hcover' hab.symm (hcut b)
  obtain ⟨e⟩ := nonempty_homeomorph_unitInterval_of_isPreconnected_compl_singleton_iff
    (fun h => hab (congrArg Subtype.val h)) honly
  have hcomp : ∀ t : unitInterval, IsPreconnected ({t}ᶜ : Set unitInterval) →
      IsPreconnected ({e.symm t}ᶜ : Set A) := fun t ht => by
    have := ht.image e.symm e.symm.continuous.continuousOn
    rwa [image_compl_eq e.symm.bijective, image_singleton] at this
  have key : ∀ φ : unitInterval → unitInterval, Continuous φ → Function.Bijective φ →
      ∃ f : unitInterval → X, Continuous f ∧ Function.Injective f ∧ f 0 = (e.symm (φ 0) : X) ∧
        f 1 = (e.symm (φ 1) : X) ∧ range f = insert a (insert b U) := fun φ hφc hφb => by
    refine ⟨fun t => (e.symm (φ t) : X), continuous_subtype_val.comp (e.symm.continuous.comp hφc),
      Subtype.val_injective.comp (e.symm.injective.comp hφb.1), rfl, rfl, ?_⟩
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (e.symm (φ t)).2
    · intro hx
      obtain ⟨t, ht⟩ := hφb.2 (e ⟨x, hx⟩)
      refine ⟨t, ?_⟩
      change ((e.symm (φ t) : A) : X) = x
      rw [ht, e.symm_apply_apply]
  have hne01 : e.symm 0 ≠ e.symm 1 := fun h =>
    absurd (congrArg Subtype.val (e.symm.injective h)) (by simp)
  rcases (honly (e.symm 0)).1 (hcomp 0 isPreconnected_compl_zero_unitInterval) with h0 | h0 <;>
    rcases (honly (e.symm 1)).1 (hcomp 1 isPreconnected_compl_one_unitInterval) with h1 | h1
  · exact absurd (h0.trans h1.symm) hne01
  · obtain ⟨f, hfc, hfi, hf0, hf1, hfr⟩ := key id continuous_id Function.bijective_id
    refine ⟨f, hfc, hfi, ?_, ?_, hfr⟩
    · rw [hf0, id, h0]
    · rw [hf1, id, h1]
  · obtain ⟨f, hfc, hfi, hf0, hf1, hfr⟩ :=
      key unitInterval.symm unitInterval.continuous_symm unitInterval.symm_involutive.bijective
    refine ⟨f, hfc, hfi, ?_, ?_, hfr⟩
    · rw [hf0, unitInterval.symm_zero, h1]
    · rw [hf1, unitInterval.symm_one, h0]
  · exact absurd (h0.trans h1.symm) hne01


/-- **R. L. Moore's characterisation of the simple closed curve.** A compact connected second countable Hausdorff
space with at least two points, in which `X \ {a, b}` is disconnected for all `a ≠ b`, is homeomorphic to the
circle: the two sides of a separation of `X \ {a, b}`, with `a` and `b` added, are arcs from `a` to `b` meeting only
at their endpoints. -/
theorem nonempty_homeomorph_circle_of_forall_not_isPreconnected_compl_pair [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [SecondCountableTopology X] [Nontrivial X]
    (hpair : ∀ x y : X, x ≠ y → ¬ IsPreconnected ({x, y}ᶜ : Set X)) : Nonempty (Circle ≃ₜ X) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  have hopen : IsOpen ({a, b}ᶜ : Set X) := (toFinite _).isClosed.isOpen_compl
  obtain ⟨U, V, hU, hV, hUV, hcover, hUne, hVne⟩ :=
    exists_separation_of_isOpen_of_not_isPreconnected hopen (hpair a b hab)
  have hcover' : V ∪ U = ({a, b}ᶜ : Set X) := (union_comm V U).trans hcover
  obtain ⟨f, hfc, hfi, hf0, hf1, hfr⟩ :=
    exists_arc_of_union_eq_compl_pair hpair hU hV hUV hcover hUne hVne hab
  obtain ⟨g, hgc, hgi, hg0, hg1, hgr⟩ :=
    exists_arc_of_union_eq_compl_pair hpair hV hU hUV.symm hcover' hVne hUne hab
  have hfg : range f ∩ range g ⊆ {a, b} := by
    rw [hfr, hgr]
    rintro z ⟨hzU, hzV⟩
    by_contra hz
    have hza : z ≠ a := fun h => hz (Or.inl h)
    have hzb : z ≠ b := fun h => hz (Or.inr h)
    exact disjoint_left.1 hUV ((hzU.resolve_left hza).resolve_left hzb) ((hzV.resolve_left hza).resolve_left hzb)
  obtain ⟨φ, hφc, hφi, hφr⟩ := exists_circle_injective_of_arcs hfc hgc hfi hgi hf0 hf1 hg0 hg1 hfg
  have hsurj : Function.Surjective φ := by
    rw [← range_eq_univ, hφr, hfr, hgr]
    refine eq_univ_of_forall fun z => ?_
    by_cases hza : z = a
    · exact Or.inl (Or.inl hza)
    by_cases hzb : z = b
    · exact Or.inl (Or.inr (Or.inl hzb))
    have hzab : z ∉ ({a, b} : Set X) := fun h => h.elim hza hzb
    have hzUV : z ∈ U ∪ V := hcover ▸ hzab
    rcases hzUV with h | h
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inr h))
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ ⟨hφi, hsurj⟩) hφc⟩

/-- **R. L. Moore's characterisation for plane sets.** A compact connected set `Γ ⊆ ℂ` with at least two points,
such that `Γ \ {a, b}` is disconnected for all distinct `a, b ∈ Γ`, is homeomorphic to the circle. -/
theorem nonempty_homeomorph_circle_of_forall_not_isPreconnected_diff_pair {Γ : Set ℂ} (hΓ : IsCompact Γ)
    (hΓc : IsConnected Γ) (hΓn : Γ.Nontrivial)
    (hpair : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ¬ IsPreconnected (Γ \ {a, b})) : Nonempty (Circle ≃ₜ Γ) := by
  have : CompactSpace Γ := isCompact_iff_compactSpace.1 hΓ
  have : ConnectedSpace Γ := Subtype.connectedSpace hΓc
  have : Nontrivial Γ := nontrivial_coe_sort.2 hΓn
  refine nonempty_homeomorph_circle_of_forall_not_isPreconnected_compl_pair fun x y hxy h => ?_
  apply hpair x x.2 y y.2 fun h' => hxy (Subtype.ext h')
  have himg : ((↑) : Γ → ℂ) '' ({x, y}ᶜ : Set Γ) = Γ \ {(x : ℂ), (y : ℂ)} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, ?_⟩
      rintro (h' | h')
      · exact hw (Or.inl (Subtype.ext h'))
      · exact hw (Or.inr (Subtype.ext h'))
    · rintro ⟨hz, hzxy⟩
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      rintro (h' | h')
      · exact hzxy (Or.inl (congrArg Subtype.val h'))
      · exact hzxy (Or.inr (congrArg Subtype.val h'))
  rw [← himg]
  exact h.image _ continuous_subtype_val.continuousOn

end LatticeProb.Topology
