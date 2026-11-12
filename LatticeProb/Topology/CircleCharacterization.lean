import LatticeProb.Topology.NonCutPoints

/-!
# Continua in which every pair of points separates

This file starts the proof of R. L. Moore's characterisation of the simple closed curve: a nondegenerate metric
continuum `X` such that `X \ {a, b}` is disconnected for all `a ≠ b` is homeomorphic to a circle (Kuratowski,
*Topology II*, §47-49; Nadler, *Continuum Theory*, Chapter IX). Here:

* `isPreconnected_compl_singleton_of_forall_not_isPreconnected_compl_pair`: such a continuum has no cut point. If
  `X \ {p} = U ∪ V` were a separation, pick non-cut points `q ∈ U` and `r ∈ V` of `X`; then
  `X \ {q, r} = ((U ∪ {p}) \ {q}) ∪ ((V ∪ {p}) \ {r})` is a union of two connected sets through `p`;
* for a separation `X \ {a, b} = U ∪ V` of such a continuum: `closure U ⊆ U ∪ {a, b}`
  (`closure_subset_insert_insert_of_union_eq_compl_pair`), `a ∈ closure U`
  (`mem_closure_of_union_eq_compl_pair`), and `U ∪ {a, b}` is a closed connected set
  (`isPreconnected_insert_insert_of_union_eq_compl_pair`).

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

end Pair

end LatticeProb.Topology
