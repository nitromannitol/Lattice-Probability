/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.ExplInv

open Finset List

namespace LatticeProb.Lattice.Planar

/-- The frame created at the visit of `z`, given its parent (`none` for the root). -/
def frameOf (f d : Site) (p : Option Site) (z : Site) : List (Site × Site) :=
  match p with
  | none => edgesFrom f d
  | some p => continuations p z

theorem frameOf_tail (f d : Site) (p : Option Site) (z : Site) :
    ∀ e ∈ frameOf f d p z, e.1 = (match p with | none => f | some _ => z) := by
  cases p with
  | none => exact edgesFrom_tail f d
  | some p => exact continuations_tail p z

/-- The depth-first structure without the normalization condition. -/
structure DFS0 (f d : Site) (s : ExplState) (xs : List Site) (Fs : List (List (Site × Site))) :
    Prop where
  len : Fs.length = xs.length
  root : xs.getLast? = some f
  root_mem : f ∈ s.visited
  nodup : xs.Nodup
  branch_visited : ∀ x ∈ xs, x ∈ s.visited
  active : s.active = Fs.flatten
  tree : ∀ i x p, xs[i]? = some x → xs[i + 1]? = some p → (p, x, true) ∈ s.tested
  frame_sub : ∀ i x F, xs[i]? = some x → Fs[i]? = some F → F <+ frameOf f d xs[i + 1]? x
  after_child : ∀ i x c F, xs[i + 1]? = some x → xs[i]? = some c → Fs[i + 1]? = some F →
    ∃ pre post, frameOf f d xs[i + 2]? x = pre ++ (x, c) :: post ∧ F <+ post ∧
      ∀ w o, (x, w, o) ∈ s.tested → (o = true ∧ w = c) ∨ (x, w) ∈ pre
  head : ∀ x F, xs[0]? = some x → Fs[0]? = some F →
    ∃ pre post, frameOf f d xs[1]? x = pre ++ post ∧ F <+ post ∧
      ∀ w o, (x, w, o) ∈ s.tested → (x, w) ∈ pre
  open_head : ∀ t ∈ s.tested, t.2.2 = true → t.2.1 ∈ s.visited
  open_unique : ∀ t ∈ s.tested, ∀ t' ∈ s.tested, t.2.2 = true → t'.2.2 = true →
    t.2.1 = t'.2.1 → t = t'
  visited_parent : ∀ z ∈ s.visited, z ≠ f → ∃ p, (p, z, true) ∈ s.tested
  head_ne_root : ∀ t ∈ s.tested, t.2.2 = true → t.2.1 ≠ f
  tail_earlier : ∀ k (hk : k < s.tested.length), s.tested[k].2.2 = true →
    s.tested[k].1 = f ∨ ∃ k' < k, ∃ (hk' : k' < s.tested.length),
      s.tested[k'].2.1 = s.tested[k].1 ∧ s.tested[k'].2.2 = true

/-- The depth-first structure, normalized: the head frame is nonempty. -/
structure DFS (f d : Site) (s : ExplState) (xs : List Site) (Fs : List (List (Site × Site))) :
    Prop extends DFS0 f d s xs Fs where
  head_ne : s.active ≠ [] → ∃ F, Fs[0]? = some F ∧ F ≠ []

theorem dfs0_init (f d : Site) :
    DFS0 f d (explInit f d) [f] [edgesFrom f d] where
  len := rfl
  root := rfl
  root_mem := by simp [explInit]
  nodup := List.nodup_singleton f
  branch_visited := by simp [explInit]
  active := by simp [explInit]
  tree := by
    intro i x p hx hp
    rcases i with _ | i <;> simp at hp
  frame_sub := by
    intro i x F hx hF
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hF
      subst x F
      exact List.Sublist.refl _
    · simp at hx
  after_child := by
    intro i x c F hx
    rcases i with _ | i <;> simp at hx
  head := by
    intro x F hx hF
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hF
    subst x F
    exact ⟨[], edgesFrom f d, rfl, List.Sublist.refl _, by simp [explInit]⟩
  open_head := by simp [explInit]
  open_unique := by simp [explInit]
  visited_parent := by simp [explInit]
  head_ne_root := by simp [explInit]
  tail_earlier := by simp [explInit]

theorem dfs_init (f d : Site) : DFS f d (explInit f d) [f] [edgesFrom f d] where
  toDFS0 := dfs0_init f d
  head_ne := fun _ => ⟨edgesFrom f d, rfl, by simp [edgesFrom]⟩

/-- Splitting a sublist at its head. -/
theorem sublist_cons_split {α : Type*} {a : α} {l l' : List α} (h : a :: l <+ l') :
    ∃ q r, l' = q ++ a :: r ∧ l <+ r := by
  obtain ⟨r₁, r₂, rfl, ha, hl⟩ := List.cons_sublist_iff.1 h
  obtain ⟨q, q', rfl⟩ := List.append_of_mem ha
  exact ⟨q, q' ++ r₂, by simp, hl.trans (List.sublist_append_right _ _)⟩

theorem tested_append_any {T : List (Site × Site × Bool)} {a b : Site} {o : Bool}
    {x w : Site} {o' : Bool} (h : (x, w, o') ∈ T ++ [(a, b, o)]) :
    (x, w, o') ∈ T ∨ (x = a ∧ w = b ∧ o' = o) := by
  rcases List.mem_append.1 h with h | h
  · exact Or.inl h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    exact Or.inr ⟨h.1, h.2.1, h.2.2⟩

/-- `tail_earlier` is preserved by appending a test whose tail is visited. -/
theorem tail_earlier_append {f : Site} {T : List (Site × Site × Bool)}
    (h : ∀ k (hk : k < T.length), T[k].2.2 = true →
      T[k].1 = f ∨ ∃ k' < k, ∃ (hk' : k' < T.length), T[k'].2.1 = T[k].1 ∧ T[k'].2.2 = true)
    (a b : Site) (o : Bool) (ha : o = true → a = f ∨ ∃ p, (p, a, true) ∈ T) :
    ∀ k (hk : k < (T ++ [(a, b, o)]).length), (T ++ [(a, b, o)])[k].2.2 = true →
      (T ++ [(a, b, o)])[k].1 = f ∨ ∃ k' < k, ∃ (hk' : k' < (T ++ [(a, b, o)]).length),
        (T ++ [(a, b, o)])[k'].2.1 = (T ++ [(a, b, o)])[k].1 ∧ (T ++ [(a, b, o)])[k'].2.2 = true := by
  intro k hk hopen
  rw [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_or_ge k T.length with hkT | hkT
  · rw [List.getElem_append_left hkT] at hopen ⊢
    rcases h k hkT hopen with h1 | ⟨k', hk'k, hk', h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr ⟨k', hk'k, by rw [List.length_append]; omega, ?_, ?_⟩
      · simpa [List.getElem_append_left hk', List.getElem_append_left hkT] using h1
      · simpa [List.getElem_append_left hk'] using h2
  · have hkeq : k = T.length := by omega
    subst hkeq
    rw [List.getElem_append_right (le_refl _)] at hopen ⊢
    simp only [Nat.sub_self, List.getElem_cons_zero] at hopen ⊢
    rcases ha hopen with h1 | ⟨p, hp⟩
    · exact Or.inl h1
    · obtain ⟨k', hk', hpk⟩ := List.mem_iff_getElem.1 hp
      refine Or.inr ⟨k', hk', by rw [List.length_append]; omega, ?_, ?_⟩
      · rw [List.getElem_append_left hk', hpk]
      · rw [List.getElem_append_left hk', hpk]

/-- A closed test. -/
theorem dfs0_closed {f d : Site} {s : ExplState} {x : Site} {xs' : List Site}
    {e : Site × Site} {F₁ : List (Site × Site)} {Fs' : List (List (Site × Site))}
    (h : DFS0 f d s (x :: xs') ((e :: F₁) :: Fs')) (hex : e.1 = x) (fr : ℕ)
    (P : Site × Site → Bool) :
    DFS0 f d ⟨s.visited, (F₁ ++ Fs'.flatten).filter P, s.tested ++ [(e.1, e.2, false)], fr⟩
      (x :: xs') (F₁.filter P :: Fs'.map (List.filter P)) where
  len := by have := h.len; simp only [List.length_cons, List.length_map] at this ⊢; exact this
  root := h.root
  root_mem := h.root_mem
  nodup := h.nodup
  branch_visited := h.branch_visited
  active := by simp [List.filter_append, List.filter_flatten]
  tree := fun i x' p hx hp => List.mem_append_left _ (h.tree i x' p hx hp)
  frame_sub := by
    intro i x' F hx hF
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hF
      subst x' F
      have := h.frame_sub 0 x (e :: F₁) rfl rfl
      exact List.filter_sublist.trans ((List.sublist_cons_self _ _).trans this)
    · simp only [List.getElem?_cons_succ, List.getElem?_map] at hF
      rcases hG : Fs'[i]? with _ | G
      · rw [hG] at hF; simp at hF
      · rw [hG] at hF
        simp only [Option.map_some, Option.some.injEq] at hF
        subst F
        have := h.frame_sub (i + 1) x' G hx (by simpa using hG)
        exact List.filter_sublist.trans this
  after_child := by
    intro i x' c F hx hc hF
    simp only [List.getElem?_cons_succ, List.getElem?_map] at hF
    rcases hG : Fs'[i]? with _ | G
    · rw [hG] at hF; simp at hF
    · rw [hG] at hF
      simp only [Option.map_some, Option.some.injEq] at hF
      subst F
      obtain ⟨pre, post, hfr, hsub, hopen⟩ := h.after_child i x' c G hx hc (by simpa using hG)
      refine ⟨pre, post, hfr, List.filter_sublist.trans hsub, fun w o hw => ?_⟩
      rcases tested_append_any hw with hw | ⟨hxe, -, -⟩
      · exact hopen w o hw
      · -- the tested edge has tail `x`, not a deeper branch vertex
        exfalso
        have hx' : x' ∈ xs' := List.mem_of_getElem? hx
        have hnd := List.nodup_cons.1 h.nodup
        rw [hxe, hex] at hx'
        exact hnd.1 hx'
  head := by
    intro x' F hx hF
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hF
    subst x' F
    obtain ⟨pre₀, post₀, hfr, hsub, hopen⟩ := h.head x (e :: F₁) rfl rfl
    obtain ⟨q, post, hpost, hsub'⟩ := sublist_cons_split hsub
    have he : e = (x, e.2) := by rw [← hex]
    refine ⟨pre₀ ++ q ++ [e], post, ?_, List.filter_sublist.trans hsub', fun w o hw => ?_⟩
    · rw [hfr, hpost]; simp
    · rcases tested_append_any hw with hw | ⟨-, hw, -⟩
      · exact List.mem_append_left _ (List.mem_append_left _ (hopen w o hw))
      · rw [hw, ← he]
        exact List.mem_append_right _ (List.mem_singleton_self _)
  open_head := by
    intro t ht ho
    rcases List.mem_append.1 ht with ht | ht
    · exact h.open_head t ht ho
    · simp only [List.mem_singleton] at ht
      subst ht
      simp at ho
  open_unique := by
    intro t ht t' ht' ho ho' heq
    rcases List.mem_append.1 ht with ht | ht
    · rcases List.mem_append.1 ht' with ht' | ht'
      · exact h.open_unique t ht t' ht' ho ho' heq
      · simp only [List.mem_singleton] at ht'; subst ht'; simp at ho'
    · simp only [List.mem_singleton] at ht; subst ht; simp at ho
  visited_parent := fun z hz hzf =>
    let ⟨p, hp⟩ := h.visited_parent z hz hzf
    ⟨p, List.mem_append_left _ hp⟩
  head_ne_root := by
    intro t ht ho
    rcases List.mem_append.1 ht with ht | ht
    · exact h.head_ne_root t ht ho
    · simp only [List.mem_singleton] at ht; subst ht; simp at ho
  tail_earlier := tail_earlier_append h.tail_earlier e.1 e.2 false (fun h => by simp at h)

/-- An open test. -/
theorem dfs0_open {f d : Site} {s : ExplState} (hinv : ExplInv s) {x : Site} {xs' : List Site}
    {e : Site × Site} {F₁ : List (Site × Site)} {Fs' : List (List (Site × Site))}
    (h : DFS0 f d s (x :: xs') ((e :: F₁) :: Fs')) (hex : e.1 = x) (he2 : e.2 ∉ s.visited)
    (hadj : squareGraph.Adj e.1 e.2) (fr : ℕ) (P : Site × Site → Bool) :
    DFS0 f d ⟨insert e.2 s.visited, (continuations e.1 e.2 ++ (F₁ ++ Fs'.flatten)).filter P,
        s.tested ++ [(e.1, e.2, true)], fr⟩
      (e.2 :: x :: xs')
      ((continuations e.1 e.2).filter P :: F₁.filter P :: Fs'.map (List.filter P)) where
  len := by have := h.len; simp only [List.length_cons, List.length_map] at this ⊢; omega
  root := by rw [List.getLast?_cons_cons]; exact h.root
  root_mem := Finset.mem_insert_of_mem h.root_mem
  nodup := List.nodup_cons.2 ⟨fun hm => he2 (h.branch_visited _ hm), h.nodup⟩
  branch_visited := by
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (h.branch_visited z hz)
  active := by simp [List.filter_append, List.filter_flatten]
  tree := by
    intro i x' p hx hp
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hx hp
      subst x' p
      apply List.mem_append_right
      simp [hex]
    · simp only [List.getElem?_cons_succ] at hx hp
      exact List.mem_append_left _ (h.tree i x' p hx hp)
  frame_sub := by
    intro i x' F hx hF
    rcases i with _ | _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hF
      subst x' F
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, frameOf, hex]
      exact List.filter_sublist
    · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hx hF
      subst x' F
      have := h.frame_sub 0 x (e :: F₁) rfl rfl
      simp only [List.getElem?_cons_succ]
      exact List.filter_sublist.trans ((List.sublist_cons_self _ _).trans this)
    · simp only [List.getElem?_cons_succ, List.getElem?_map] at hx hF ⊢
      rcases hG : Fs'[i]? with _ | G
      · rw [hG] at hF; simp at hF
      · rw [hG] at hF
        simp only [Option.map_some, Option.some.injEq] at hF
        subst F
        have := h.frame_sub (i + 1) x' G hx (by simpa using hG)
        exact List.filter_sublist.trans this
  after_child := by
    intro i x' c F hx hc hF
    rcases i with _ | i
    · -- the old head `x` with the new child `e.2`
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hx hc hF
      subst x' c F
      obtain ⟨pre₀, post₀, hfr, hsub, hopen⟩ := h.head x (e :: F₁) rfl rfl
      obtain ⟨q, post, hpost, hsub'⟩ := sublist_cons_split hsub
      have he : e = (x, e.2) := by rw [← hex]
      refine ⟨pre₀ ++ q, post, ?_, List.filter_sublist.trans hsub', fun w o hw => ?_⟩
      · simp only [List.getElem?_cons_succ] at hfr ⊢
        rw [hfr, hpost, he]
        simp
      · rcases tested_append_any hw with hw | ⟨-, hw, ho⟩
        · exact Or.inr (List.mem_append_left _ (hopen w o hw))
        · exact Or.inl ⟨ho, hw⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_map] at hx hc hF ⊢
      rcases hG : Fs'[i]? with _ | G
      · rw [hG] at hF; simp at hF
      · rw [hG] at hF
        simp only [Option.map_some, Option.some.injEq] at hF
        subst F
        obtain ⟨pre, post, hfr, hsub, hopen⟩ := h.after_child i x' c G hx hc (by simpa using hG)
        refine ⟨pre, post, hfr, List.filter_sublist.trans hsub, fun w o hw => ?_⟩
        rcases tested_append_any hw with hw | ⟨hxe, -, -⟩
        · exact hopen w o hw
        · -- the new tested edge has tail `x`, which is not deeper in the branch
          exfalso
          have hx' : x' ∈ xs' := List.mem_of_getElem? hx
          have hnd := List.nodup_cons.1 h.nodup
          rw [hxe, hex] at hx'
          exact hnd.1 hx'
  head := by
    intro x' F hx hF
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hF
    subst x' F
    refine ⟨[], continuations e.1 e.2, by simp [frameOf, hex], List.filter_sublist,
      fun w o hw => ?_⟩
    exfalso
    rcases tested_append_any hw with hw | ⟨hw, -, -⟩
    · exact he2 (hinv.tested_tail _ hw)
    · exact hadj.ne hw.symm
  open_head := by
    intro t ht ho
    rcases List.mem_append.1 ht with ht | ht
    · exact Finset.mem_insert_of_mem (h.open_head t ht ho)
    · simp only [List.mem_singleton] at ht
      subst ht
      exact Finset.mem_insert_self _ _
  open_unique := by
    intro t ht t' ht' ho ho' heq
    rcases List.mem_append.1 ht with ht | ht <;> rcases List.mem_append.1 ht' with ht' | ht'
    · exact h.open_unique t ht t' ht' ho ho' heq
    · simp only [List.mem_singleton] at ht'
      subst ht'
      have := h.open_head t ht ho
      simp only at heq
      rw [heq] at this
      exact absurd this he2
    · simp only [List.mem_singleton] at ht
      subst ht
      have := h.open_head t' ht' ho'
      simp only at heq
      rw [← heq] at this
      exact absurd this he2
    · simp only [List.mem_singleton] at ht ht'
      rw [ht, ht']
  visited_parent := by
    intro z hz hzf
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨e.1, List.mem_append_right _ (List.mem_singleton_self _)⟩
    · obtain ⟨p, hp⟩ := h.visited_parent z hz hzf
      exact ⟨p, List.mem_append_left _ hp⟩
  head_ne_root := by
    intro t ht ho
    rcases List.mem_append.1 ht with ht | ht
    · exact h.head_ne_root t ht ho
    · simp only [List.mem_singleton] at ht
      subst ht
      intro hf
      simp only at hf
      apply he2
      rw [hf]
      exact h.root_mem
  tail_earlier := tail_earlier_append h.tail_earlier e.1 e.2 true (fun _ => by
    rw [hex]
    by_cases hxf : x = f
    · exact Or.inl hxf
    · exact Or.inr (h.visited_parent x (h.branch_visited x List.mem_cons_self) hxf))

/-- The step of the exploration preserves the depth-first structure (before normalization). -/
theorem dfs0_step {f d : Site} {s : ExplState} (hinv : ExplInv s) {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS f d s xs Fs) (ρ : Config squareGraph) :
    ∃ xs' Fs', DFS0 f d (explStep ρ s) xs' Fs' := by
  classical
  rcases hact : s.active with _ | ⟨e, rest⟩
  · exact ⟨xs, Fs, by rw [explStep_nil ρ hact]; exact h.toDFS0⟩
  obtain ⟨F, hF0, hFne⟩ := h.head_ne (by rw [hact]; exact List.cons_ne_nil _ _)
  obtain ⟨x, xs', rfl⟩ : ∃ x xs', xs = x :: xs' := by
    rcases xs with _ | ⟨x, xs'⟩
    · have := h.len
      simp only [List.length_nil, List.length_eq_zero_iff] at this
      subst this
      simp at hF0
    · exact ⟨x, xs', rfl⟩
  obtain ⟨F', Fs', rfl⟩ : ∃ F' Fs', Fs = F' :: Fs' := by
    rcases Fs with _ | ⟨F', Fs'⟩
    · simp at hF0
    · exact ⟨F', Fs', rfl⟩
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hF0
  subst F'
  obtain ⟨F₁, rfl⟩ : ∃ F₁, F = e :: F₁ := by
    rcases F with _ | ⟨e', F₁⟩
    · exact absurd rfl hFne
    · have := h.active
      rw [hact] at this
      simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at this
      exact ⟨F₁, by rw [this.1]⟩
  have hrest : rest = F₁ ++ Fs'.flatten := by
    have := h.active
    rw [hact] at this
    simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at this
    exact this.2
  have hex : e.1 = x := by
    have hsub := h.frame_sub 0 x (e :: F₁) rfl rfl
    have hmem : e ∈ frameOf f d (x :: xs')[0 + 1]? x := hsub.subset List.mem_cons_self
    have := frameOf_tail f d _ x e hmem
    rcases hp : (x :: xs')[0 + 1]? with _ | p
    · rw [hp] at this
      have hxf : x = f := by
        have hroot := h.root
        rcases xs' with _ | ⟨p', xs''⟩
        · simpa using hroot
        · simp at hp
      dsimp only at this
      rw [this, hxf]
    · rw [hp] at this; exact this
  have he_active : e ∈ s.active := by rw [hact]; exact List.mem_cons_self
  have he2 : e.2 ∉ s.visited := hinv.active_head e he_active
  have hadj : squareGraph.Adj e.1 e.2 := hinv.active_adj e he_active
  rw [explStep_cons ρ hact, explStepWith_cons hact]
  rcases ho : decide (DualOpen ρ e.1 e.2) with _ | _
  · -- closed test
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rw [hrest]
    exact ⟨_, _, dfs0_closed h.toDFS0 hex _ _⟩
  · -- open test
    simp only [↓reduceIte]
    rw [hrest]
    exact ⟨_, _, dfs0_open hinv h.toDFS0 hex he2 hadj _ _⟩

/-- Dropping a leading empty frame. -/
theorem dfs0_drop {f d : Site} {s : ExplState} {x : Site} {xs' : List Site}
    {Fs' : List (List (Site × Site))} (h : DFS0 f d s (x :: xs') ([] :: Fs')) (hne : xs' ≠ []) :
    DFS0 f d s xs' Fs' where
  len := by have := h.len; simp only [List.length_cons] at this; omega
  root := by
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
    have := h.root
    rwa [List.getLast?_cons_cons] at this
  root_mem := h.root_mem
  nodup := (List.nodup_cons.1 h.nodup).2
  branch_visited := fun z hz => h.branch_visited z (List.mem_cons_of_mem _ hz)
  active := by have := h.active; simpa using this
  tree := fun i x' p hx hp => h.tree (i + 1) x' p (by simpa using hx) (by simpa using hp)
  frame_sub := fun i x' F hx hF => by
    have := h.frame_sub (i + 1) x' F (by simpa using hx) (by simpa using hF)
    simpa using this
  after_child := fun i x' c F hx hc hF => by
    have := h.after_child (i + 1) x' c F (by simpa using hx) (by simpa using hc) (by simpa using hF)
    simpa using this
  head := by
    intro x' F hx hF
    obtain ⟨pre, post, hfr, hsub, hopen⟩ := h.after_child 0 x' x F (by simpa using hx) rfl
      (by simpa using hF)
    refine ⟨pre ++ [(x', x)], post, ?_, hsub, fun w o hw => ?_⟩
    · simpa using hfr
    · rcases hopen w o hw with ⟨-, rfl⟩ | hw'
      · exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact List.mem_append_left _ hw'
  open_head := h.open_head
  open_unique := h.open_unique
  visited_parent := h.visited_parent
  head_ne_root := h.head_ne_root
  tail_earlier := h.tail_earlier

/-- Every depth-first structure normalizes. -/
theorem dfs_of_dfs0 {f d : Site} {s : ExplState} : ∀ (xs : List Site) (Fs : List (List (Site × Site))),
    DFS0 f d s xs Fs → ∃ xs' Fs', DFS f d s xs' Fs' := by
  intro xs
  induction xs with
  | nil => intro Fs h; have := h.root; simp at this
  | cons x xs' ih =>
    intro Fs h
    by_cases hact : s.active = []
    · exact ⟨x :: xs', Fs, ⟨h, fun h' => absurd hact h'⟩⟩
    rcases Fs with _ | ⟨F, Fs'⟩
    · have := h.len; simp at this
    rcases F with _ | ⟨e, F₁⟩
    · -- an empty head frame: drop it
      rcases xs' with _ | ⟨y, ys⟩
      · have := h.len
        simp only [List.length_cons, List.length_nil, add_left_inj, List.length_eq_zero_iff] at this
        subst this
        have := h.active
        simp at this
        exact absurd this hact
      · exact ih Fs' (dfs0_drop h (List.cons_ne_nil _ _))
    · exact ⟨x :: xs', (e :: F₁) :: Fs', ⟨h, fun _ => ⟨e :: F₁, rfl, List.cons_ne_nil _ _⟩⟩⟩

theorem dfs_step {f d : Site} {s : ExplState} (hinv : ExplInv s) {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS f d s xs Fs) (ρ : Config squareGraph) :
    ∃ xs' Fs', DFS f d (explStep ρ s) xs' Fs' := by
  obtain ⟨xs', Fs', h'⟩ := dfs0_step hinv h ρ
  exact dfs_of_dfs0 xs' Fs' h'

/-- Every state of the exploration carries a depth-first structure. -/
theorem dfs_explore (ρ : Config squareGraph) (f : Site) {d : Site} (hd : IsUnit d) :
    ∀ n : ℕ, ∃ xs Fs, DFS f d (explore ρ f d n) xs Fs
  | 0 => ⟨[f], [edgesFrom f d], dfs_init f d⟩
  | n + 1 => by
    obtain ⟨xs, Fs, h⟩ := dfs_explore ρ f hd n
    rw [explore_succ]
    exact dfs_step (explInv_explore ρ f hd n) h ρ

end LatticeProb.Lattice.Planar
