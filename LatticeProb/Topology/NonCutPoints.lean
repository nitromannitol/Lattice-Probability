import Mathlib.Order.Zorn
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Basic

/-!
# Non-cut points of continua

A point `x` of a connected space `X` is a *non-cut point* when `X \ {x}` is still connected. This file proves the
classical existence theorem of continuum theory (R. L. Moore; see Willard, *General Topology*, §28, or Nadler,
*Continuum Theory*, Chapter VI), for compact connected `T₁` spaces:

* `isPreconnected_insert_of_union_eq_compl_singleton`: if `U` and `V` are disjoint open sets covering `X \ {p}`,
  then `U ∪ {p}` is connected;
* `exists_isPreconnected_compl_singleton_mem_of_union_eq_compl_singleton`: each side `U` of such a separation of
  `X \ {p}` contains a non-cut point of `X`. The proof takes, for every point `x ∈ U` that is a cut point, the side
  of a separation of `X \ {x}` away from `p`; together with `x` these sides form a family of nonempty closed sets
  in which every member contains a strictly smaller one, and Zorn's lemma together with compactness gives a
  contradiction;
* `exists_ne_isPreconnected_compl_singleton`: a compact connected `T₁` space with two points has two distinct
  non-cut points.

Separations are written as two disjoint open subsets of `X` covering `X \ {x}`; in a `T₁` space this is the same as a
separation of the open subspace `X \ {x}` (`exists_separation_of_not_isPreconnected_compl_singleton`).
-/

namespace LatticeProb.Topology

open Set

variable {X : Type*}

/-- If `U` and `V` are disjoint and cover `X \ {p}`, then `U ∪ {p}` is the complement of `V`. -/
theorem insert_eq_compl_of_union_eq_compl_singleton {p : X} {U V : Set X} (hUV : Disjoint U V)
    (hcover : U ∪ V = {p}ᶜ) : insert p U = Vᶜ := by
  have hmem : ∀ y, y ∈ U ∪ V ↔ y ≠ p := fun y => by rw [hcover, mem_compl_singleton_iff]
  ext x
  simp only [mem_insert_iff, mem_compl_iff]
  constructor
  · rintro (rfl | hx) hv
    · exact (hmem x).1 (Or.inr hv) rfl
    · exact hUV.ne_of_mem hx hv rfl
  · intro hv
    by_cases hx : x = p
    · exact Or.inl hx
    · exact Or.inr (((hmem x).2 hx).resolve_right hv)

variable [TopologicalSpace X]

/-- A point `x` of a `T₁` space for which `X \ {x}` is not connected gives two disjoint nonempty open sets covering
`X \ {x}`. -/
theorem exists_separation_of_not_isPreconnected_compl_singleton [T1Space X] {x : X}
    (h : ¬ IsPreconnected ({x}ᶜ : Set X)) :
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ Disjoint A B ∧ A ∪ B = {x}ᶜ ∧ A.Nonempty ∧ B.Nonempty := by
  simp only [IsPreconnected, not_forall, not_nonempty_iff_eq_empty] at h
  obtain ⟨u, v, hu, hv, hsuv, hsu, hsv, hne⟩ := h
  refine ⟨{x}ᶜ ∩ u, {x}ᶜ ∩ v, isOpen_compl_singleton.inter hu, isOpen_compl_singleton.inter hv, ?_, ?_,
    hsu, hsv⟩
  · refine Set.disjoint_left.2 fun y hy hy' => ?_
    have hy'' : y ∈ ({x}ᶜ ∩ (u ∩ v) : Set X) := ⟨hy.1, hy.2, hy'.2⟩
    rw [hne] at hy''
    exact hy''
  · rw [← inter_union_distrib_left]
    exact inter_eq_left.2 hsuv

/-- **The closure of a side of a cut point is connected.** In a preconnected space, if `U` and `V` are disjoint
open sets covering `X \ {p}`, then `U ∪ {p}` is preconnected. -/
theorem isPreconnected_insert_of_union_eq_compl_singleton [PreconnectedSpace X] {p : X} {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcover : U ∪ V = {p}ᶜ) :
    IsPreconnected (insert p U) := by
  have hs := insert_eq_compl_of_union_eq_compl_singleton hUV hcover
  have hclosed : IsClosed (insert p U) := by
    rw [hs]
    exact hV.isClosed_compl
  have key : ∀ t t' : Set X, IsClosed t → IsClosed t' → insert p U ⊆ t ∪ t' → p ∈ t →
      (insert p U ∩ t').Nonempty → (insert p U ∩ (t ∩ t')).Nonempty := by
    intro t t' ht ht' hst hpt hne'
    by_contra h0
    rw [not_nonempty_iff_eq_empty] at h0
    have heq : insert p U ∩ t' = U ∩ tᶜ := by
      ext y
      constructor
      · rintro ⟨hy, hyt'⟩
        have hyt : y ∉ t := fun hyt => by
          have hy3 : y ∈ insert p U ∩ (t ∩ t') := ⟨hy, hyt, hyt'⟩
          rw [h0] at hy3
          exact hy3
        rcases hy with hyp | hyU
        · rw [hyp] at hyt
          exact absurd hpt hyt
        · exact ⟨hyU, hyt⟩
      · rintro ⟨hyU, hyt⟩
        have hy : y ∈ insert p U := mem_insert_of_mem p hyU
        exact ⟨hy, (hst hy).resolve_left hyt⟩
    have hW : IsClopen (insert p U ∩ t') := by
      refine ⟨hclosed.inter ht', ?_⟩
      rw [heq]
      exact hU.inter ht.isOpen_compl
    rcases isClopen_iff.1 hW with hW0 | hW1
    · rw [hW0] at hne'
      exact not_nonempty_empty hne'
    · have hp : p ∈ insert p U ∩ t' := by
        rw [hW1]
        exact mem_univ p
      have hp3 : p ∈ insert p U ∩ (t ∩ t') := ⟨hp.1, hpt, hp.2⟩
      rw [h0] at hp3
      exact hp3
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hst hne hne'
  rcases hst (mem_insert p U) with hpt | hpt'
  · exact key t t' ht ht' hst hpt hne'
  · rw [inter_comm t t']
    exact key t' t ht' ht (by rw [union_comm]; exact hst) hpt' hne

/-- **Each side of a cut point contains a non-cut point.** In a compact connected `T₁` space, if `U` and `V` are
disjoint open sets covering `X \ {p}` and `U` is nonempty, then some `x ∈ U` is a non-cut point: `X \ {x}` is
connected. -/
theorem exists_isPreconnected_compl_singleton_mem_of_union_eq_compl_singleton
    [T1Space X] [CompactSpace X] [ConnectedSpace X] {p : X} {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcover : U ∪ V = {p}ᶜ) (hUne : U.Nonempty) :
    ∃ x ∈ U, IsPreconnected ({x}ᶜ : Set X) := by
  by_contra hcon
  push Not at hcon
  have hpU : p ∉ U := fun hp => by
    have hp' : p ∈ U ∪ V := Or.inl hp
    rw [hcover] at hp'
    exact hp' rfl
  -- for every `x ∈ U`, a separation `A x ∪ B x` of `X \ {x}` with `p ∈ B x`
  have hsep : ∀ x ∈ U, ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ Disjoint A B ∧ A ∪ B = {x}ᶜ ∧
      A.Nonempty ∧ p ∈ B := by
    intro x hx
    obtain ⟨A, B, hA, hB, hAB, hcov, hAne, hBne⟩ :=
      exists_separation_of_not_isPreconnected_compl_singleton (hcon x hx)
    have hpx : p ∈ A ∪ B := by
      rw [hcov]
      exact mem_compl_singleton_iff.2 fun h => hpU (by rw [h]; exact hx)
    rcases hpx with hpA | hpB
    · exact ⟨B, A, hB, hA, hAB.symm, by rw [union_comm]; exact hcov, hBne, hpA⟩
    · exact ⟨A, B, hA, hB, hAB, hcov, hAne, hpB⟩
  choose! A B hA hB hAB hcov hAne hpB using hsep
  have hF1 : ∀ x ∈ U, insert x (A x) = (B x)ᶜ := fun x hx =>
    insert_eq_compl_of_union_eq_compl_singleton (hAB x hx) (hcov x hx)
  have hxA : ∀ x ∈ U, x ∉ A x := fun x hx h => by
    have h' : x ∈ A x ∪ B x := Or.inl h
    rw [hcov x hx] at h'
    exact h' rfl
  -- the side away from `p`, with its cut point, stays in `U`
  have hF2 : ∀ x ∈ U, insert x (A x) ⊆ U := by
    intro x hx
    have hc := isPreconnected_insert_of_union_eq_compl_singleton (hA x hx) (hB x hx) (hAB x hx) (hcov x hx)
    have hsub : insert x (A x) ⊆ U ∪ V := by
      rw [hcover, hF1 x hx]
      exact compl_subset_compl.2 (singleton_subset_iff.2 (hpB x hx))
    rcases hc.subset_or_subset hU hV hUV hsub with h | h
    · exact h
    · exact (hUV.ne_of_mem hx (h (mem_insert x _)) rfl).elim
  -- the sets `insert x (A x)` are nested: a point `y ∈ A x` gives a set inside `A x`
  have hF3 : ∀ x ∈ U, ∀ y ∈ A x, insert y (A y) ⊆ A x := by
    intro x hx y hy
    have hyU : y ∈ U := hF2 x hx (mem_insert_of_mem x hy)
    have hc := isPreconnected_insert_of_union_eq_compl_singleton (hB x hx) (hA x hx) (hAB x hx).symm
      (by rw [union_comm]; exact hcov x hx)
    have hsub : insert x (B x) ⊆ A y ∪ B y := by
      rw [hcov y hyU]
      intro z hz
      rw [mem_compl_singleton_iff]
      intro hzy
      rw [hzy] at hz
      rcases hz with h | h
      · rw [h] at hy
        exact hxA x hx hy
      · exact (hAB x hx).ne_of_mem hy h rfl
    rcases hc.subset_or_subset (hA y hyU) (hB y hyU) (hAB y hyU) hsub with h | h
    · exact ((hAB y hyU).ne_of_mem (h (mem_insert_of_mem x (hpB x hx))) (hpB y hyU) rfl).elim
    · rw [hF1 y hyU]
      intro z hz
      have hz' : z ∉ insert x (B x) := fun h' => hz (h h')
      have hzx : z ≠ x := fun e => hz' (by rw [e]; exact mem_insert x _)
      have hzB : z ∉ B x := fun h' => hz' (mem_insert_of_mem x h')
      have hz3 : z ∈ A x ∪ B x := by
        rw [hcov x hx]
        exact mem_compl_singleton_iff.2 hzx
      exact hz3.resolve_right hzB
  have hSclosed : ∀ s ∈ (fun x => insert x (A x)) '' U, IsClosed s := by
    rintro s ⟨x, hx, rfl⟩
    show IsClosed (insert x (A x))
    rw [hF1 x hx]
    exact (hB x hx).isClosed_compl
  -- every nonempty chain has a lower bound, by compactness
  have hH : ∀ c ⊆ (fun x => insert x (A x)) '' U, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ lb ∈ (fun x => insert x (A x)) '' U, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hchain hcne
    have : Nonempty c := hcne.to_subtype
    have hdir : DirectedOn (· ⊇ ·) c := by
      intro a ha b hb
      rcases eq_or_ne a b with rfl | hab
      · exact ⟨a, ha, Subset.rfl, Subset.rfl⟩
      · rcases hchain ha hb hab with h | h
        · exact ⟨a, ha, Subset.rfl, h⟩
        · exact ⟨b, hb, h, Subset.rfl⟩
    have hint : (⋂₀ c).Nonempty := by
      refine IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed hdir ?_ ?_ ?_
      · intro s hs
        obtain ⟨x, -, rfl⟩ := hcS hs
        exact insert_nonempty _ _
      · intro s hs
        exact (hSclosed s (hcS hs)).isCompact
      · intro s hs
        exact hSclosed s (hcS hs)
    obtain ⟨z, hz⟩ := hint
    obtain ⟨s₀, hs₀⟩ := hcne
    have hzU : z ∈ U := by
      obtain ⟨x₀, hx₀, hs₀eq⟩ := hcS hs₀
      have hzs₀ : z ∈ s₀ := mem_sInter.1 hz s₀ hs₀
      rw [← hs₀eq] at hzs₀
      exact hF2 x₀ hx₀ hzs₀
    refine ⟨insert z (A z), mem_image_of_mem _ hzU, ?_⟩
    intro s hs
    obtain ⟨x, hx, rfl⟩ := hcS hs
    rcases mem_sInter.1 hz _ hs with hzx | hzA
    · subst hzx
      exact Subset.rfl
    · exact (hF3 x hx z hzA).trans (subset_insert x (A x))
  obtain ⟨x₀, hx₀⟩ := hUne
  obtain ⟨m, -, hmin⟩ := zorn_superset_nonempty _ hH _ (mem_image_of_mem _ hx₀)
  obtain ⟨x, hx, rfl⟩ := hmin.prop
  obtain ⟨y, hy⟩ := hAne x hx
  have h1 : insert y (A y) ⊆ A x := hF3 x hx y hy
  have hyU : y ∈ U := hF2 x hx (mem_insert_of_mem x hy)
  have h2 : insert x (A x) ⊆ insert y (A y) :=
    hmin.2 (mem_image_of_mem _ hyU) (h1.trans (subset_insert x (A x)))
  exact hxA x hx (h1 (h2 (mem_insert x (A x))))

/-- **A nondegenerate continuum has two non-cut points.** A compact connected `T₁` space with two points has two
distinct points `a`, `b` such that `X \ {a}` and `X \ {b}` are connected. -/
theorem exists_ne_isPreconnected_compl_singleton [T1Space X] [CompactSpace X] [ConnectedSpace X]
    [Nontrivial X] :
    ∃ a b : X, a ≠ b ∧ IsPreconnected ({a}ᶜ : Set X) ∧ IsPreconnected ({b}ᶜ : Set X) := by
  by_cases h : ∃ p : X, ¬ IsPreconnected ({p}ᶜ : Set X)
  · obtain ⟨p, hp⟩ := h
    obtain ⟨U, V, hU, hV, hUV, hcov, hUne, hVne⟩ := exists_separation_of_not_isPreconnected_compl_singleton hp
    obtain ⟨a, ha, hac⟩ :=
      exists_isPreconnected_compl_singleton_mem_of_union_eq_compl_singleton hU hV hUV hcov hUne
    obtain ⟨b, hb, hbc⟩ := exists_isPreconnected_compl_singleton_mem_of_union_eq_compl_singleton hV hU
      hUV.symm (by rw [union_comm]; exact hcov) hVne
    exact ⟨a, b, hUV.ne_of_mem ha hb, hac, hbc⟩
  · push Not at h
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    exact ⟨a, b, hab, h a, h b⟩

end LatticeProb.Topology
