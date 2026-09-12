/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.ExplChain

open Finset List Fin.NatCast

namespace LatticeProb.Lattice.Planar

theorem dfs_head_shape {f d : Site} {s : ExplState} {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS f d s xs Fs) {e : Site × Site}
    {rest : List (Site × Site)} (hact : s.active = e :: rest) :
    ∃ x xs' F₁ Fs', xs = x :: xs' ∧ Fs = (e :: F₁) :: Fs' ∧ rest = F₁ ++ Fs'.flatten ∧ e.1 = x := by
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
  exact ⟨x, xs', F₁, Fs', rfl, rfl, hrest, hex⟩

/-- Distinct tests have distinct bonds. -/
theorem tested_eq_of_bond_eq {s : ExplState} (hinv : ExplInv s) {t t' : Site × Site × Bool}
    (ht : t ∈ s.tested) (ht' : t' ∈ s.tested) (hb : bond (t.1, t.2.1) = bond (t'.1, t'.2.1)) :
    t = t' :=
  List.inj_on_of_nodup_map hinv.tested_nodup ht ht' hb

/-- A bond tested closed is not tested open in either direction. -/
theorem not_open_of_closed {s : ExplState} (hinv : ExplInv s) {a b : Site}
    (h : (a, b, false) ∈ s.tested) : (a, b, true) ∉ s.tested ∧ (b, a, true) ∉ s.tested := by
  constructor
  · intro h'
    have := tested_eq_of_bond_eq hinv h h' rfl
    simp at this
  · intro h'
    have := tested_eq_of_bond_eq hinv h h' (by simp [bond, Sym2.eq_swap])
    simp at this

theorem branch_adj {f d : Site} {s : ExplState} (hinv : ExplInv s) {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s xs Fs) :
    xs.IsChain (fun a b => IsUnit (b - a)) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have := h.tree i xs[i] xs[i + 1] (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _)
  have hadj := hinv.tested_adj _ this
  simp only at hadj
  have := isUnit_of_adj hadj
  have e : xs[i + 1] - xs[i] = -(xs[i] - xs[i + 1]) := by abel
  rw [e]
  rcases this with h | h | h | h <;> rw [h] <;> simp [IsUnit]

theorem chain_adj {s : ExplState} (hinv : ExplInv s) {xs : List Site} {z : Site} {l : List Site}
    (hl : ChainTo s xs z l) : l.IsChain (fun a b => IsUnit (b - a)) := by
  refine hl.chain.imp (fun {a b} hab => ?_)
  have hadj := hinv.tested_adj _ hab
  simp only at hadj
  have := isUnit_of_adj hadj
  have e : b - a = -(a - b) := by abel
  rw [e]
  rcases this with h | h | h | h <;> rw [h] <;> simp [IsUnit]

theorem chain_subset_visited {s : ExplState} {xs : List Site} {z : Site} {l : List Site}
    (hl : ChainTo s xs z l) : ∀ y ∈ l, y ∈ s.visited := hl.visited

/-- The chain from `SW` up to the branch vertex `xs[k]`, the branch down to the current face
`xs[0]`, and the bond back to `SW`. -/
def curveS (l xs : List Site) (k : ℕ) (SW : Site) : List Site :=
  l ++ ((xs.take k).reverse ++ [SW])

theorem isUnit_neg {u : Site} (hu : IsUnit u) : IsUnit (-u) := by
  rcases hu with rfl | rfl | rfl | rfl <;> simp [IsUnit]

theorem isUnit_sub_comm {a b : Site} (h : IsUnit (b - a)) : IsUnit (a - b) := by
  have : a - b = -(b - a) := by abel
  rw [this]; exact isUnit_neg h

theorem chain_ne_nil {s : ExplState} {xs : List Site} {z : Site} {l : List Site}
    (hl : ChainTo s xs z l) : l ≠ [] := by
  intro h; have := hl.head; rw [h] at this; simp at this

theorem take_reverse_head? {xs : List Site} {k : ℕ} (hk : k < xs.length) (hk0 : 0 < k) :
    ((xs.take k).reverse).head? = some xs[k - 1] := by
  rw [List.head?_reverse, List.getLast?_eq_getElem?, List.length_take, min_eq_left hk.le]
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem (by omega)]

theorem take_reverse_getLast? {x : Site} {xs' : List Site} {k : ℕ} (hk0 : 0 < k) :
    (((x :: xs').take k).reverse).getLast? = some x := by
  rw [List.getLast?_reverse]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp

theorem take_reverse_isChain {f d : Site} {s : ExplState} (hinv : ExplInv s) {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s xs Fs) (k : ℕ) :
    ((xs.take k).reverse).IsChain (fun a b => IsUnit (b - a)) := by
  rw [List.isChain_reverse]
  exact ((branch_adj hinv h).take k).imp (fun {a b} hab => isUnit_sub_comm hab)

/-- The curve is a closed walk. -/
theorem curveS_closed {f d : Site} {s : ExplState} (hinv : ExplInv s) {x : Site} {xs' : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s (x :: xs') Fs) {SW : Site} {l : List Site}
    (hl : ChainTo s (x :: xs') SW l) {k : ℕ} (hk : k < (x :: xs').length)
    (hlast : l.getLast? = some (x :: xs')[k]) (hadj : squareGraph.Adj x SW) :
    IsClosedWalk (curveS l (x :: xs') k SW) where
  ne_nil := by
    unfold curveS
    simp [chain_ne_nil hl]
  closed := by
    unfold curveS
    rw [List.head?_append_of_ne_nil _ (chain_ne_nil hl), hl.head,
      List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_append_of_ne_nil _ (by simp)]
    simp
  unit := by
    unfold curveS
    rw [List.isChain_append]
    refine ⟨chain_adj hinv hl, ?_, ?_⟩
    · rw [List.isChain_append]
      refine ⟨take_reverse_isChain hinv h k, List.isChain_singleton _, ?_⟩
      intro a ha b hb
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simp at ha
      · rw [take_reverse_getLast? hk0] at ha
        simp only [Option.mem_def, Option.some.injEq] at ha
        subst ha
        exact isUnit_of_adj hadj
    · intro a ha b hb
      rw [hlast] at ha
      simp only [Option.mem_def, Option.some.injEq] at ha
      subst ha
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        simp only [List.take_zero, List.reverse_nil, List.nil_append, List.head?_cons,
          Option.mem_def, Option.some.injEq] at hb
        subst hb
        exact isUnit_of_adj hadj
      · rw [List.head?_append_of_ne_nil _ (by
            intro h0; have := take_reverse_head? hk hk0; rw [h0] at this; simp at this),
          take_reverse_head? hk hk0] at hb
        simp only [Option.mem_def, Option.some.injEq] at hb
        subst hb
        have := h.tree (k - 1) _ _ (List.getElem?_eq_getElem (by omega))
          (by rw [show k - 1 + 1 = k by omega]; exact List.getElem?_eq_getElem hk)
        have hadj' := hinv.tested_adj _ this
        simp only at hadj'
        exact isUnit_of_adj hadj'

/-- The curve is simple. -/
theorem curveS_tail_nodup {f d : Site} {s : ExplState} {x : Site} {xs' : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s (x :: xs') Fs) {SW : Site} {l : List Site}
    (hl : ChainTo s (x :: xs') SW l) {k : ℕ} (hk : k < (x :: xs').length)
    (hlast : l.getLast? = some (x :: xs')[k]) :
    (curveS l (x :: xs') k SW).tail.Nodup := by
  obtain ⟨l', rfl⟩ : ∃ l', l = SW :: l' := by
    rcases l with _ | ⟨a, l'⟩
    · exact absurd rfl (chain_ne_nil hl)
    · have := hl.head; simp only [List.head?_cons, Option.some.injEq] at this; subst a
      exact ⟨l', rfl⟩
  unfold curveS
  rw [List.cons_append, List.tail_cons]
  have hnd := hl.nodup
  rw [List.nodup_cons] at hnd
  have hxs := h.nodup
  have hseg_nodup : (((x :: xs').take k).reverse).Nodup :=
    List.nodup_reverse.2 (hxs.sublist (List.take_sublist _ _))
  have hmem_seg : ∀ y, y ∈ ((x :: xs').take k).reverse → ∃ i, i < k ∧ (x :: xs')[i]? = some y := by
    intro y hy
    rw [List.mem_reverse, List.mem_iff_getElem] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    simp only [List.length_take, lt_min_iff] at hi
    refine ⟨i, hi.1, ?_⟩
    rw [List.getElem_take]
    exact List.getElem?_eq_getElem _
  have hl_branch : ∀ y ∈ SW :: l', y ∈ x :: xs' → y = (x :: xs')[k] := by
    intro y hy hyx
    have hsplit := List.dropLast_append_getLast (chain_ne_nil hl)
    rw [← hsplit] at hy
    rcases List.mem_append.1 hy with hy | hy
    · exact absurd hyx (hl.dropLast_notMem y hy)
    · simp only [List.mem_singleton] at hy
      subst hy
      rw [List.getLast?_eq_some_getLast (chain_ne_nil hl)] at hlast
      simpa using hlast
  have hk_notMem : (x :: xs')[k] ∉ ((x :: xs').take k).reverse := by
    intro hmem
    obtain ⟨i, hi, hiy⟩ := hmem_seg _ hmem
    have hik : i = k := (List.Nodup.getElem_inj_iff hxs).1 (by
      rw [List.getElem?_eq_getElem (by omega : i < (x :: xs').length)] at hiy
      simpa using hiy)
    exact absurd hik (by omega)
  refine List.nodup_append.2 ⟨hnd.2, List.nodup_append.2 ⟨hseg_nodup, List.nodup_singleton _, ?_⟩, ?_⟩
  · intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst b
    subst a
    obtain ⟨i, hi, hiy⟩ := hmem_seg _ ha
    have hSWx : SW ∈ x :: xs' := List.mem_of_getElem? hiy
    have := hl_branch SW List.mem_cons_self hSWx
    rw [this] at ha
    exact hk_notMem ha
  · intro a ha b hb hab
    subst hab
    rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨i, hi, hiy⟩ := hmem_seg _ hb
      have := hl_branch a (List.mem_cons_of_mem _ ha) (List.mem_of_getElem? hiy)
      rw [this] at hb
      exact hk_notMem hb
    · simp only [List.mem_singleton] at hb
      subst hb
      exact hnd.1 ha

/-- The curve has at least three distinct vertices. -/
theorem curveS_three {f d : Site} {s : ExplState} {x : Site} {xs' : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s (x :: xs') Fs) {SW : Site} {l : List Site}
    (hl : ChainTo s (x :: xs') SW l) {k : ℕ} (hk : k < (x :: xs').length)
    (hlast : l.getLast? = some (x :: xs')[k]) (hne : SW ≠ x)
    (hnt1 : (SW, x, true) ∉ s.tested) (hnt2 : (x, SW, true) ∉ s.tested) :
    3 ≤ (curveS l (x :: xs') k SW).tail.length := by
  obtain ⟨l', rfl⟩ : ∃ l', l = SW :: l' := by
    rcases l with _ | ⟨a, l'⟩
    · exact absurd rfl (chain_ne_nil hl)
    · have := hl.head; simp only [List.head?_cons, Option.some.injEq] at this; subst a
      exact ⟨l', rfl⟩
  unfold curveS
  simp only [List.cons_append, List.tail_cons, List.length_append, List.length_reverse,
    List.length_take, List.length_singleton]
  have hmin : min k (x :: xs').length = k := min_eq_left hk.le
  rw [hmin]
  rcases l' with _ | ⟨b, l2⟩
  · -- `l = [SW]`: then `SW = xs[k]` is on the branch, so `k ≥ 2`
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    rcases k with _ | _ | k
    · simp at hlast; exact absurd hlast hne
    · exfalso
      have h0 : 0 < xs'.length := by simp only [List.length_cons] at hk; omega
      simp only [List.getElem_cons_succ] at hlast
      have := h.tree 0 x xs'[0] rfl (List.getElem?_eq_getElem (by simp only [List.length_cons]; omega))
      rw [← hlast] at this
      exact hnt1 this
    · simp only [List.length_nil]; omega
  · rcases l2 with _ | ⟨c, l3⟩
    · -- `l = [SW, b]`: if `k = 0` then `b = x` and `x → SW` would be a tree edge
      rcases k with _ | k
      · exfalso
        simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq,
          List.getElem_cons_zero] at hlast
        subst hlast
        have := hl.chain
        rw [List.isChain_cons_cons] at this
        exact hnt2 this.1
      · simp only [List.length_cons, List.length_nil]; omega
    · simp only [List.length_cons]; omega

theorem mem_steps_iff {w : List Site} {a b : Site} :
    (a, b) ∈ steps w ↔ ∃ i : ℕ, (w[i]? = some a ∧ w[i + 1]? = some b) := by
  unfold steps
  constructor
  · intro h
    obtain ⟨i, hi, hi'⟩ := List.mem_iff_getElem.1 h
    rw [List.getElem_zip, Prod.mk.injEq] at hi'
    simp only [List.length_zip, List.length_tail, lt_min_iff] at hi
    refine ⟨i, ?_, ?_⟩
    · rw [List.getElem?_eq_getElem hi.1, hi'.1]
    · rw [List.getElem?_eq_getElem (by omega), ← hi'.2, List.getElem_tail]
  · rintro ⟨i, ha, hb⟩
    rw [List.mem_iff_getElem]
    have hi : i + 1 < w.length := (List.getElem?_eq_some_iff.1 hb).1
    refine ⟨i, by simp only [List.length_zip, List.length_tail, lt_min_iff]; omega, ?_⟩
    rw [List.getElem_zip, List.getElem_tail]
    rw [List.getElem?_eq_getElem (by omega)] at ha
    rw [List.getElem?_eq_getElem hi] at hb
    simp only [Option.some.injEq] at ha hb
    rw [ha, hb]

theorem steps_append_singleton {w : List Site} {a : Site} (hc : w.getLast? = some a) (b : Site) :
    (a, b) ∈ steps (w ++ [b]) := by
  have hne : w ≠ [] := by intro h; rw [h] at hc; simp at hc
  have hpos := List.length_pos_of_ne_nil hne
  rw [mem_steps_iff]
  refine ⟨w.length - 1, ?_, ?_⟩
  · rw [List.getElem?_append_left (by omega), ← hc, List.getLast?_eq_getElem?]
  · rw [show w.length - 1 + 1 = w.length by omega, List.getElem?_append_right le_rfl]
    simp

theorem steps_of_steps_prefix {w₁ w₂ : List Site} {a b : Site} (h : (a, b) ∈ steps w₁) :
    (a, b) ∈ steps (w₁ ++ w₂) := by
  rw [mem_steps_iff] at h ⊢
  obtain ⟨i, ha, hb⟩ := h
  have hi : i + 1 < w₁.length := (List.getElem?_eq_some_iff.1 hb).1
  exact ⟨i, by rw [List.getElem?_append_left (by omega)]; exact ha,
    by rw [List.getElem?_append_left hi]; exact hb⟩

theorem steps_of_steps_suffix {w₁ w₂ : List Site} {a b : Site} (h : (a, b) ∈ steps w₂) :
    (a, b) ∈ steps (w₁ ++ w₂) := by
  rw [mem_steps_iff] at h ⊢
  obtain ⟨i, ha, hb⟩ := h
  refine ⟨w₁.length + i, ?_, ?_⟩
  · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact ha
  · rw [List.getElem?_append_right (by omega), show w₁.length + i + 1 - w₁.length = i + 1 by omega]
    exact hb

/-- The vertex before the closing step. -/
theorem curveS_pre_getLast? {x : Site} {xs' : List Site} {l : List Site} {k : ℕ}
    (hk : k < (x :: xs').length) (hlast : l.getLast? = some (x :: xs')[k]) :
    (l ++ ((x :: xs').take k).reverse).getLast? = some x := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    simpa using hlast
  · rw [List.getLast?_append_of_ne_nil _ (by
      intro h0; have := take_reverse_getLast? (x := x) (xs' := xs') hk0; rw [h0] at this; simp at this)]
    exact take_reverse_getLast? hk0

/-- The last step of the curve is `x → SW`. -/
theorem curveS_last_step {x : Site} {xs' : List Site} {SW : Site} {l : List Site} {k : ℕ}
    (hk : k < (x :: xs').length) (hlast : l.getLast? = some (x :: xs')[k]) :
    (x, SW) ∈ steps (curveS l (x :: xs') k SW) := by
  unfold curveS
  rw [← List.append_assoc]
  exact steps_append_singleton (curveS_pre_getLast? hk hlast) SW

theorem curveS_getElem?_chain {l xs : List Site} {k : ℕ} {SW : Site} {i : ℕ} (hi : i < l.length) :
    (curveS l xs k SW)[i]? = l[i]? := by
  unfold curveS
  rw [List.getElem?_append_left hi]

theorem curveS_getElem?_seg {l xs : List Site} {k : ℕ} {SW : Site} (hk : k ≤ xs.length) {i : ℕ}
    (hi : i < k) : (curveS l xs k SW)[l.length + i]? = xs[k - 1 - i]? := by
  unfold curveS
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simp only [List.length_reverse, List.length_take]; omega),
    List.getElem?_reverse (by simp only [List.length_take]; omega)]
  simp only [List.length_take, min_eq_left hk]
  rw [List.getElem?_take_of_lt (by omega)]

theorem curveS_getElem?_last {l xs : List Site} {k : ℕ} {SW : Site} (hk : k ≤ xs.length) :
    (curveS l xs k SW)[l.length + k]? = some SW := by
  unfold curveS
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_right (by simp only [List.length_reverse, List.length_take]; omega)]
  simp [List.length_take, min_eq_left hk]

theorem curveS_length {l xs : List Site} {k : ℕ} {SW : Site} (hk : k ≤ xs.length) :
    (curveS l xs k SW).length = l.length + k + 1 := by
  unfold curveS
  simp only [List.length_append, List.length_reverse, List.length_take, List.length_singleton,
    min_eq_left hk]
  omega

/-- The steps along the branch part: `xs[j+1] → xs[j]` for `j + 1 < k`. -/
theorem curveS_step_seg {l xs : List Site} {k : ℕ} {SW : Site} (hk : k ≤ xs.length) {j : ℕ}
    (hj : j + 1 < k) : ((xs[j + 1]'(by omega)), (xs[j]'(by omega))) ∈ steps (curveS l xs k SW) := by
  rw [mem_steps_iff]
  refine ⟨l.length + (k - 2 - j), ?_, ?_⟩
  · rw [curveS_getElem?_seg hk (by omega), show k - 1 - (k - 2 - j) = j + 1 by omega]
    exact List.getElem?_eq_getElem _
  · rw [show l.length + (k - 2 - j) + 1 = l.length + (k - 1 - j) by omega,
      curveS_getElem?_seg hk (by omega), show k - 1 - (k - 1 - j) = j by omega]
    exact List.getElem?_eq_getElem _

/-- The step from the junction `xs[k]` down to `xs[k-1]`. -/
theorem curveS_step_junction {l xs : List Site} {k : ℕ} {SW : Site} (hk : k < xs.length)
    (hk0 : 0 < k) (hlast : l.getLast? = some xs[k]) :
    (xs[k], xs[k - 1]'(by omega)) ∈ steps (curveS l xs k SW) := by
  rw [mem_steps_iff]
  have hne : l ≠ [] := by intro h; rw [h] at hlast; simp at hlast
  have hpos := List.length_pos_of_ne_nil hne
  refine ⟨l.length - 1, ?_, ?_⟩
  · rw [curveS_getElem?_chain (by omega), ← hlast, List.getLast?_eq_getElem?]
  · rw [show l.length - 1 + 1 = l.length + 0 by omega, curveS_getElem?_seg hk.le hk0,
      show k - 1 - 0 = k - 1 by omega]
    exact List.getElem?_eq_getElem _

/-- The steps inside the chain. -/
theorem curveS_step_chain {l xs : List Site} {k : ℕ} {SW : Site} {i : ℕ} (hi : i + 1 < l.length) :
    (l[i], l[i + 1]) ∈ steps (curveS l xs k SW) := by
  rw [mem_steps_iff]
  exact ⟨i, by rw [curveS_getElem?_chain (by omega)]; exact List.getElem?_eq_getElem _,
    by rw [curveS_getElem?_chain hi]; exact List.getElem?_eq_getElem _⟩

/-- Membership in the curve. -/
theorem mem_curveS {l xs : List Site} {k : ℕ} {SW y : Site} :
    y ∈ curveS l xs k SW ↔ y ∈ l ∨ y ∈ xs.take k ∨ y = SW := by
  unfold curveS
  simp [List.mem_append, List.mem_reverse]

theorem chain_mem_branch {s : ExplState} {xs : List Site} {SW : Site} {l : List Site}
    (hl : ChainTo s xs SW l) {k : ℕ} (hk : k < xs.length) (hlast : l.getLast? = some xs[k]) :
    ∀ y ∈ l, y ∈ xs → y = xs[k] := by
  intro y hy hyx
  have hne := chain_ne_nil hl
  have hsplit := List.dropLast_append_getLast hne
  rw [← hsplit] at hy
  rcases List.mem_append.1 hy with hy | hy
  · exact absurd hyx (hl.dropLast_notMem y hy)
  · simp only [List.mem_singleton] at hy
    subst hy
    rw [List.getLast?_eq_some_getLast hne] at hlast
    simpa using hlast

/-- Branch vertices above the junction are not on the curve. -/
theorem branch_notMem_curveS {f d : Site} {s : ExplState} {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s xs Fs) {SW : Site} {l : List Site}
    (hl : ChainTo s xs SW l) {k : ℕ} (hk : k < xs.length) (hlast : l.getLast? = some xs[k])
    {j : ℕ} (hj : j < xs.length) (hjk : k < j) : xs[j] ∉ curveS l xs k SW := by
  intro hmem
  have hnd := h.nodup
  rcases mem_curveS.1 hmem with hy | hy | hy
  · have := chain_mem_branch hl hk hlast _ hy (List.getElem_mem _)
    have := (List.Nodup.getElem_inj_iff hnd).1 this
    omega
  · rw [List.mem_iff_getElem] at hy
    obtain ⟨i, hi, hi'⟩ := hy
    simp only [List.length_take, lt_min_iff] at hi
    rw [List.getElem_take] at hi'
    have := (List.Nodup.getElem_inj_iff hnd).1 hi'
    omega
  · have hSW : SW ∈ l := List.mem_of_mem_head? hl.head
    have := chain_mem_branch hl hk hlast SW hSW (hy ▸ List.getElem_mem _)
    rw [← hy] at this
    have := (List.Nodup.getElem_inj_iff hnd).1 this
    omega

theorem curveS_subset_visited {s : ExplState} {xs : List Site} {SW : Site} {l : List Site}
    (hl : ChainTo s xs SW l) (hxs : ∀ y ∈ xs, y ∈ s.visited) (hSW : SW ∈ s.visited) {k : ℕ} :
    ∀ y ∈ curveS l xs k SW, y ∈ s.visited := by
  intro y hy
  rcases mem_curveS.1 hy with hy | hy | rfl
  · exact hl.visited y hy
  · exact hxs y (List.mem_of_mem_take hy)
  · exact hSW

/-- The step of the curve into the current face `x`: from the parent `xs[1]` when `k ≥ 1`, and
from a child of `x` on the chain when `k = 0`. -/
theorem curveS_pred {s : ExplState} {x : Site} {xs' : List Site} {SW : Site} {l : List Site}
    (hl : ChainTo s (x :: xs') SW l) {k : ℕ} (hk : k < (x :: xs').length)
    (hlast : l.getLast? = some (x :: xs')[k]) (hne : SW ≠ x) :
    ∃ p, (p, x) ∈ steps (curveS l (x :: xs') k SW) ∧
      ((1 ≤ k ∧ (x :: xs')[1]? = some p) ∨ (k = 0 ∧ (x, p, true) ∈ s.tested)) := by
  rcases k with _ | _ | k
  · -- `k = 0`: the chain ends at `x`
    have hne_l := chain_ne_nil hl
    have hlen : 2 ≤ l.length := by
      rcases l with _ | ⟨a, _ | ⟨b, l'⟩⟩
      · exact absurd rfl hne_l
      · have h1 := hl.head; have h2 := hlast
        simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton,
          List.getElem_cons_zero] at h1 h2
        exact absurd (h1.symm.trans h2) hne
      · simp
    have hx : l[l.length - 2 + 1]'(by omega) = x := by
      have h1 : l[l.length - 2 + 1]? = some x := by
        rw [show l.length - 2 + 1 = l.length - 1 by omega, ← List.getLast?_eq_getElem?, hlast]
        rfl
      rw [List.getElem?_eq_getElem (by omega)] at h1
      simpa using h1
    refine ⟨l[l.length - 2], ?_, Or.inr ⟨rfl, ?_⟩⟩
    · have := curveS_step_chain (l := l) (xs := x :: xs') (k := 0) (SW := SW)
        (i := l.length - 2) (by omega)
      rw [hx] at this
      exact this
    · have := List.isChain_iff_getElem.1 hl.chain (l.length - 2) (by omega)
      rw [hx] at this
      exact this
  · -- `k = 1`: the chain ends at the parent `xs[1]`
    refine ⟨(x :: xs')[1], ?_, Or.inl ⟨le_rfl, List.getElem?_eq_getElem _⟩⟩
    have := curveS_step_junction (l := l) (xs := x :: xs') (k := 1) (SW := SW) hk (by omega) hlast
    simpa using this
  · -- `k ≥ 2`: the branch step `xs[1] → xs[0]`
    refine ⟨(x :: xs')[1], ?_, Or.inl ⟨by omega, List.getElem?_eq_getElem _⟩⟩
    have := curveS_step_seg (l := l) (xs := x :: xs') (k := k + 2) (SW := SW) hk.le (j := 0)
      (by omega)
    simpa using this

theorem chain_pred_notMem_branch {s : ExplState} {xs : List Site} {SW : Site} {l : List Site}
    (hl : ChainTo s xs SW l) (hlen : 2 ≤ l.length) : l[l.length - 2] ∉ xs := by
  apply hl.dropLast_notMem
  rw [List.mem_iff_getElem]
  refine ⟨l.length - 2, by simp only [List.length_dropLast]; omega, ?_⟩
  rw [List.getElem_dropLast]

/-- The step of the curve into the junction `xs[k]`: from a child of it on the chain, or, when
the chain is trivial (`xs[k] = SW`), the closing step from `x`. -/
theorem curveS_junction_pred {s : ExplState} {x : Site} {xs' : List Site} {SW : Site}
    {l : List Site} (hl : ChainTo s (x :: xs') SW l) {k : ℕ} (hk : k < (x :: xs').length)
    (hlast : l.getLast? = some (x :: xs')[k]) :
    ∃ c₀, (c₀, (x :: xs')[k]) ∈ steps (curveS l (x :: xs') k SW) ∧
      ((((x :: xs')[k], c₀, true) ∈ s.tested ∧ c₀ ∉ x :: xs') ∨ (c₀ = x ∧ (x :: xs')[k] = SW)) := by
  have hne_l := chain_ne_nil hl
  rcases l with _ | ⟨a, _ | ⟨b, l'⟩⟩
  · exact absurd rfl hne_l
  · -- the trivial chain `[SW]`
    have h1 := hl.head; have h2 := hlast
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at h1 h2
    subst h1
    refine ⟨x, ?_, Or.inr ⟨rfl, h2.symm⟩⟩
    rw [← h2]
    exact curveS_last_step hk hlast
  · set l := a :: b :: l' with hl_def
    have hlen : 2 ≤ l.length := by simp [hl_def]
    have hx : l[l.length - 2 + 1]'(by omega) = (x :: xs')[k] := by
      have h1 : l[l.length - 2 + 1]? = some (x :: xs')[k] := by
        rw [show l.length - 2 + 1 = l.length - 1 by omega, ← List.getLast?_eq_getElem?, hlast]
      rw [List.getElem?_eq_getElem (by omega)] at h1
      simpa using h1
    refine ⟨l[l.length - 2], ?_, Or.inl ⟨?_, chain_pred_notMem_branch hl hlen⟩⟩
    · have := curveS_step_chain (l := l) (xs := x :: xs') (k := k) (SW := SW)
        (i := l.length - 2) (by omega)
      rw [hx] at this
      exact this
    · have := List.isChain_iff_getElem.1 hl.chain (l.length - 2) (by omega)
      rw [hx] at this
      exact this

theorem mem_of_double_mem_dbl' {c : List Site} (hc : c.IsChain (fun a b => IsUnit (b - a)))
    {p : Site} (h : p + p ∈ dbl c) : p ∈ c := by
  rcases mem_dbl.1 h with ⟨a, ha, hpa⟩ | ⟨s, hs, hab⟩
  · have : p = a := by
      obtain ⟨p1, p2⟩ := p; obtain ⟨a1, a2⟩ := a
      simp only [Prod.mk_add_mk, Prod.mk.injEq] at hpa
      ext <;> simp <;> omega
    rw [this]; exact ha
  · exfalso
    have hu := steps_unit' hc hs
    obtain ⟨p1, p2⟩ := p; obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := s
    rw [isUnit_iff'] at hu
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at hab
    omega

theorem mid_mem_dbl_iff' {c : List Site} (hc : c.IsChain (fun a b => IsUnit (b - a))) {z v : Site}
    (hv : IsUnit v) : z + z + v ∈ dbl c ↔ (z, z + v) ∈ steps c ∨ (z + v, z) ∈ steps c := by
  constructor
  · intro h
    rcases mem_dbl.1 h with ⟨a, -, ha⟩ | ⟨s, hs, hab⟩
    · exfalso
      obtain ⟨z1, z2⟩ := z; obtain ⟨a1, a2⟩ := a
      rcases hv with rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff] at ha <;> omega
    · have hu := steps_unit' hc hs
      have hzv : IsUnit (z + v - z) := by rw [add_sub_cancel_left]; exact hv
      have hm : z + (z + v) = s.1 + s.2 := by rw [← hab]; abel
      rcases bond_eq_of_mid_eq hzv hu hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        have : (z, z + v) = s := Prod.ext h1 h2
        rw [this]; exact hs
      · right
        have : (z + v, z) = s := Prod.ext h2 h1
        rw [this]; exact hs
  · rintro (h | h)
    · exact mem_dbl.2 (Or.inr ⟨_, h, by simp; abel⟩)
    · exact mem_dbl.2 (Or.inr ⟨_, h, by simp; abel⟩)

theorem mem_dbl_even' {c : List Site} (hc : c.IsChain (fun a b => IsUnit (b - a))) {q : Site}
    (hq : q ∈ dbl c) : Even q.1 ∨ Even q.2 := by
  rcases mem_dbl.1 hq with ⟨a, -, rfl⟩ | ⟨s, hs, rfl⟩
  · exact Or.inl ⟨a.1, rfl⟩
  · have hu := steps_unit' hc hs
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := s
    rw [isUnit_iff'] at hu
    simp only [Prod.fst_add, Prod.snd_add]
    rcases hu with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inr ⟨a2, by omega⟩
    · exact Or.inr ⟨a2, by omega⟩
    · exact Or.inl ⟨a1, by omega⟩
    · exact Or.inl ⟨a1, by omega⟩

theorem oddodd_notMem_dbl' {c : List Site} (hc : c.IsChain (fun a b => IsUnit (b - a))) {q : Site}
    (h1 : Odd q.1) (h2 : Odd q.2) : q ∉ dbl c := by
  intro hq
  rcases mem_dbl_even' hc hq with h | h
  · exact (Int.not_even_iff_odd.2 h1) h
  · exact (Int.not_even_iff_odd.2 h2) h

theorem dbl_isChain {c : List Site} (hc : c.IsChain (fun a b => IsUnit (b - a))) :
    (dbl c).IsChain (fun a b => IsUnit (b - a)) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hs : ((dbl c)[i], (dbl c)[i + 1]) ∈ steps (dbl c) := by
    unfold steps
    rw [List.mem_iff_getElem]
    refine ⟨i, by simp [List.length_zip]; omega, ?_⟩
    rw [List.getElem_zip, List.getElem_tail]
  obtain ⟨t, ht, h⟩ := mem_steps_dbl.1 hs
  have hu := steps_unit' hc ht
  rcases h with h | h <;> rw [Prod.mk.injEq] at h <;> obtain ⟨h1, h2⟩ := h <;> rw [h1, h2]
  · convert hu using 1; abel
  · convert hu using 1; abel

/-- The chain from the tail of `σ` up to the junction, then the branch down to `x`. -/
def pathP (l xs : List Site) (k : ℕ) : List Site := l ++ (xs.take k).reverse

theorem curveS_eq_pathP (l xs : List Site) (k : ℕ) (SW : Site) :
    curveS l xs k SW = pathP l xs k ++ [SW] := by
  unfold curveS pathP; rw [List.append_assoc]

theorem pathP_ne_nil {s : ExplState} {xs : List Site} {z : Site} {l : List Site}
    (hl : ChainTo s xs z l) (k : ℕ) : pathP l xs k ≠ [] := by
  unfold pathP; simp [chain_ne_nil hl]

theorem pathP_head? {s : ExplState} {xs : List Site} {z : Site} {l : List Site}
    (hl : ChainTo s xs z l) (k : ℕ) : (pathP l xs k).head? = some z := by
  unfold pathP; rw [List.head?_append_of_ne_nil _ (chain_ne_nil hl), hl.head]

theorem pathP_getLast? {x : Site} {xs' : List Site} {l : List Site} {k : ℕ}
    (hk : k < (x :: xs').length) (hlast : l.getLast? = some (x :: xs')[k]) :
    (pathP l (x :: xs') k).getLast? = some x := curveS_pre_getLast? hk hlast

theorem pathP_length {l xs : List Site} {k : ℕ} (hk : k ≤ xs.length) :
    (pathP l xs k).length = l.length + k := by
  unfold pathP; simp [List.length_take, min_eq_left hk]

theorem mem_pathP {l xs : List Site} {k : ℕ} {y : Site} :
    y ∈ pathP l xs k ↔ y ∈ l ∨ y ∈ xs.take k := by
  unfold pathP; simp

theorem mem_curveS_of_mem_pathP {l xs : List Site} {k : ℕ} {SW y : Site} (h : y ∈ pathP l xs k) :
    y ∈ curveS l xs k SW := by
  rw [curveS_eq_pathP]; exact List.mem_append_left _ h

theorem steps_curveS_of_steps_pathP {l xs : List Site} {k : ℕ} {SW a b : Site}
    (h : (a, b) ∈ steps (pathP l xs k)) : (a, b) ∈ steps (curveS l xs k SW) := by
  rw [curveS_eq_pathP]; exact steps_of_steps_prefix h

theorem steps_append_singleton_cases {w : List Site} {t a b : Site}
    (h : (a, b) ∈ steps (w ++ [t])) : (a, b) ∈ steps w ∨ (w.getLast? = some a ∧ b = t) := by
  rw [mem_steps_iff] at h
  obtain ⟨i, ha, hb⟩ := h
  have hi := (List.getElem?_eq_some_iff.1 hb).1
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge (i + 1) w.length with hlt | hge
  · left
    rw [mem_steps_iff]
    refine ⟨i, ?_, ?_⟩
    · rw [← ha, List.getElem?_append_left (by omega)]
    · rw [← hb, List.getElem?_append_left hlt]
  · right
    have hi' : i + 1 = w.length := by omega
    constructor
    · rw [List.getElem?_append_left (by omega)] at ha
      rw [List.getLast?_eq_getElem?, show w.length - 1 = i by omega]
      exact ha
    · rw [List.getElem?_append_right (by omega), hi', Nat.sub_self] at hb
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      exact hb.symm

theorem mem_steps_append_of_getLast?_head? {w₁ w₂ : List Site} {a b : Site}
    (h1 : w₁.getLast? = some a) (h2 : w₂.head? = some b) : (a, b) ∈ steps (w₁ ++ w₂) := by
  rcases w₂ with _ | ⟨b', w₂'⟩
  · simp at h2
  · simp only [List.head?_cons, Option.some.injEq] at h2
    subst h2
    rw [show w₁ ++ b' :: w₂' = (w₁ ++ [b']) ++ w₂' by simp]
    exact steps_of_steps_prefix (steps_append_singleton h1 b')

theorem mem_steps_append {w₁ w₂ : List Site} {a b : Site} (h : (a, b) ∈ steps (w₁ ++ w₂)) :
    (a, b) ∈ steps w₁ ∨ (a, b) ∈ steps w₂ ∨ (w₁.getLast? = some a ∧ w₂.head? = some b) := by
  rw [mem_steps_iff] at h
  obtain ⟨i, ha, hb⟩ := h
  rcases Nat.lt_or_ge (i + 1) w₁.length with h1 | h1
  · left
    rw [mem_steps_iff]
    exact ⟨i, by rw [← ha, List.getElem?_append_left (by omega)],
      by rw [← hb, List.getElem?_append_left h1]⟩
  · rcases Nat.lt_or_ge i w₁.length with h2 | h2
    · right; right
      have hi : i + 1 = w₁.length := by omega
      constructor
      · rw [List.getElem?_append_left h2] at ha
        rw [List.getLast?_eq_getElem?, show w₁.length - 1 = i by omega]
        exact ha
      · rw [List.getElem?_append_right (by omega), hi, Nat.sub_self] at hb
        rw [List.head?_eq_getElem?]
        exact hb
    · right; left
      rw [mem_steps_iff]
      refine ⟨i - w₁.length, ?_, ?_⟩
      · rw [← ha, List.getElem?_append_right h2]
      · rw [← hb, List.getElem?_append_right (by omega),
          show i + 1 - w₁.length = i - w₁.length + 1 by omega]

theorem steps_of_isChain {R : Site → Site → Prop} {w : List Site} (h : w.IsChain R) {a b : Site}
    (hs : (a, b) ∈ steps w) : R a b := by
  rw [mem_steps_iff] at hs
  obtain ⟨i, ha, hb⟩ := hs
  rw [List.isChain_iff_getElem] at h
  have hi := (List.getElem?_eq_some_iff.1 hb).1
  have := h i hi
  rw [List.getElem?_eq_getElem (by omega)] at ha
  rw [List.getElem?_eq_getElem hi] at hb
  simp only [Option.some.injEq] at ha hb
  rw [← ha, ← hb]; exact this

theorem steps_reverse_take {xs : List Site} {k : ℕ} (hk : k ≤ xs.length) {a b : Site}
    (h : (a, b) ∈ steps ((xs.take k).reverse)) :
    ∃ j, ∃ (hj : j + 1 < k), a = xs[j + 1]'(by omega) ∧ b = xs[j]'(by omega) := by
  rw [mem_steps_iff] at h
  obtain ⟨i, ha, hb⟩ := h
  have hi := (List.getElem?_eq_some_iff.1 hb).1
  simp only [List.length_reverse, List.length_take, min_eq_left hk] at hi
  rw [List.getElem?_reverse (by simp only [List.length_take, min_eq_left hk]; omega)] at ha hb
  simp only [List.length_take, min_eq_left hk] at ha hb
  rw [List.getElem?_take_of_lt (by omega)] at ha hb
  obtain ⟨j, hj⟩ : ∃ j, k - 1 - i = j + 1 := ⟨k - 2 - i, by omega⟩
  rw [hj] at ha
  rw [show k - 1 - (i + 1) = j by omega] at hb
  refine ⟨j, by omega, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem (by omega)] at ha
    simp only [Option.some.injEq] at ha
    exact ha.symm
  · rw [List.getElem?_eq_getElem (by omega)] at hb
    simp only [Option.some.injEq] at hb
    exact hb.symm

theorem pathP_getElem?_chain {l xs : List Site} {k : ℕ} {i : ℕ} (hi : i < l.length) :
    (pathP l xs k)[i]? = l[i]? := by
  unfold pathP; rw [List.getElem?_append_left hi]

theorem pathP_getElem?_seg {l xs : List Site} {k : ℕ} (hk : k ≤ xs.length) {i : ℕ} (hi : i < k) :
    (pathP l xs k)[l.length + i]? = xs[k - 1 - i]? := by
  have := curveS_getElem?_seg (l := l) (SW := (0, 0)) hk hi
  rw [curveS_eq_pathP, List.getElem?_append_left (by rw [pathP_length hk]; omega)] at this
  exact this

theorem pathP_step_seg {l xs : List Site} {k : ℕ} (hk : k ≤ xs.length) {j : ℕ} (hj : j + 1 < k) :
    ((xs[j + 1]'(by omega)), (xs[j]'(by omega))) ∈ steps (pathP l xs k) := by
  rw [mem_steps_iff]
  refine ⟨l.length + (k - 2 - j), ?_, ?_⟩
  · rw [pathP_getElem?_seg hk (by omega), show k - 1 - (k - 2 - j) = j + 1 by omega]
    exact List.getElem?_eq_getElem _
  · rw [show l.length + (k - 2 - j) + 1 = l.length + (k - 1 - j) by omega,
      pathP_getElem?_seg hk (by omega), show k - 1 - (k - 1 - j) = j by omega]
    exact List.getElem?_eq_getElem _

theorem pathP_step_junction {l xs : List Site} {k : ℕ} (hk : k < xs.length) (hk0 : 0 < k)
    (hlast : l.getLast? = some xs[k]) : (xs[k], xs[k - 1]'(by omega)) ∈ steps (pathP l xs k) := by
  rw [mem_steps_iff]
  have hne : l ≠ [] := by intro h; rw [h] at hlast; simp at hlast
  have hpos := List.length_pos_of_ne_nil hne
  refine ⟨l.length - 1, ?_, ?_⟩
  · rw [pathP_getElem?_chain (by omega), ← hlast, List.getLast?_eq_getElem?]
  · rw [show l.length - 1 + 1 = l.length + 0 by omega, pathP_getElem?_seg hk.le hk0,
      show k - 1 - 0 = k - 1 by omega]
    exact List.getElem?_eq_getElem _

theorem pathP_pred {s : ExplState} {x : Site} {xs' : List Site} {τ : Site} {l : List Site}
    (hl : ChainTo s (x :: xs') τ l) {k : ℕ} (hk : k < (x :: xs').length)
    (hlast : l.getLast? = some (x :: xs')[k]) (hne : τ ≠ x) :
    ∃ p, (p, x) ∈ steps (pathP l (x :: xs') k) ∧
      ((1 ≤ k ∧ (x :: xs')[1]? = some p) ∨ (k = 0 ∧ (x, p, true) ∈ s.tested)) := by
  obtain ⟨p, hin, hp⟩ := curveS_pred hl hk hlast hne
  rw [curveS_eq_pathP] at hin
  rcases steps_append_singleton_cases hin with h | ⟨-, h⟩
  · exact ⟨p, h, hp⟩
  · exact absurd h.symm hne

theorem pathP_junction_pred {s : ExplState} {x : Site} {xs' : List Site} {τ : Site}
    {l : List Site} (hl : ChainTo s (x :: xs') τ l) {k : ℕ} (hk : k < (x :: xs').length)
    (hlast : l.getLast? = some (x :: xs')[k]) :
    (∃ c₀, (c₀, (x :: xs')[k]) ∈ steps (pathP l (x :: xs') k) ∧
      ((x :: xs')[k], c₀, true) ∈ s.tested ∧ c₀ ∉ x :: xs') ∨ (x :: xs')[k] = τ := by
  obtain ⟨c₀, hin, hc₀⟩ := curveS_junction_pred hl hk hlast
  rcases hc₀ with ⟨ht, hc₀x⟩ | ⟨-, hτ⟩
  · rw [curveS_eq_pathP] at hin
    rcases steps_append_singleton_cases hin with h | ⟨hl', -⟩
    · exact Or.inl ⟨c₀, h, ht, hc₀x⟩
    · rw [pathP_getLast? hk hlast] at hl'
      simp only [Option.some.injEq] at hl'
      exact absurd (hl' ▸ List.mem_cons_self) hc₀x
  · exact Or.inr hτ

theorem branch_notMem_pathP {f d : Site} {s : ExplState} {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s xs Fs) {τ : Site} {l : List Site}
    (hl : ChainTo s xs τ l) {k : ℕ} (hk : k < xs.length) (hlast : l.getLast? = some xs[k])
    {j : ℕ} (hj : j < xs.length) (hjk : k < j) : xs[j] ∉ pathP l xs k :=
  fun hm => branch_notMem_curveS h hl hk hlast hj hjk (mem_curveS_of_mem_pathP (SW := τ) hm)

theorem branch_mem_pathP {l xs : List Site} {k j : ℕ} (hj : j < k) (hjl : j < xs.length) :
    xs[j] ∈ pathP l xs k := by
  unfold pathP
  apply List.mem_append_right
  rw [List.mem_reverse]
  exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact List.getElem?_eq_getElem hjl)

theorem pathP_isChain {f d : Site} {s : ExplState} (hinv : ExplInv s) {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s xs Fs) {τ : Site} {l : List Site}
    (hl : ChainTo s xs τ l) {k : ℕ} (hk : k < xs.length) (hlast : l.getLast? = some xs[k]) :
    (pathP l xs k).IsChain (fun a b => IsUnit (b - a)) := by
  unfold pathP
  rw [List.isChain_append]
  refine ⟨chain_adj hinv hl, take_reverse_isChain hinv h k, ?_⟩
  intro a ha b hb
  rw [hlast] at ha
  simp only [Option.mem_def, Option.some.injEq] at ha
  subst ha
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp at hb
  · rw [take_reverse_head? hk hk0] at hb
    simp only [Option.mem_def, Option.some.injEq] at hb
    subst hb
    have := h.tree (k - 1) _ _ (List.getElem?_eq_getElem (by omega))
      (by rw [show k - 1 + 1 = k by omega]; exact List.getElem?_eq_getElem hk)
    have hadj' := hinv.tested_adj _ this
    simp only at hadj'
    exact isUnit_of_adj hadj'

theorem pathP_nodup {f d : Site} {s : ExplState} {x : Site} {xs' : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s (x :: xs') Fs) {τ : Site} {l : List Site}
    (hl : ChainTo s (x :: xs') τ l) {k : ℕ} (hk : k < (x :: xs').length)
    (hlast : l.getLast? = some (x :: xs')[k]) : (pathP l (x :: xs') k).Nodup := by
  have h1 := curveS_tail_nodup h hl hk hlast
  rw [curveS_eq_pathP, List.tail_append_of_ne_nil (pathP_ne_nil hl k), List.nodup_append] at h1
  obtain ⟨hnd, -, hdisj⟩ := h1
  have hcons : τ :: (pathP l (x :: xs') k).tail = pathP l (x :: xs') k :=
    List.cons_head?_tail (pathP_head? hl k)
  rw [← hcons, List.nodup_cons]
  exact ⟨fun hτ => hdisj τ hτ τ (List.mem_singleton_self _) rfl, hnd⟩

theorem pathP_step_tested {f d : Site} {s : ExplState} {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s xs Fs) {τ : Site} {l : List Site}
    (hl : ChainTo s xs τ l) {k : ℕ} (hk : k < xs.length) (hlast : l.getLast? = some xs[k])
    {a b : Site} (hs : (a, b) ∈ steps (pathP l xs k)) :
    (a, b, true) ∈ s.tested ∨ (b, a, true) ∈ s.tested := by
  unfold pathP at hs
  rcases mem_steps_append hs with h1 | h1 | ⟨h1, h2⟩
  · exact Or.inr (steps_of_isChain hl.chain h1)
  · obtain ⟨j, hj, rfl, rfl⟩ := steps_reverse_take hk.le h1
    exact Or.inl (h.tree j _ _ (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _))
  · rw [hlast] at h1
    simp only [Option.some.injEq] at h1
    subst h1
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp at h2
    · rw [take_reverse_head? hk hk0] at h2
      simp only [Option.some.injEq] at h2
      subst h2
      exact Or.inl (h.tree (k - 1) _ _ (List.getElem?_eq_getElem (by omega))
        (by rw [show k - 1 + 1 = k by omega]; exact List.getElem?_eq_getElem hk))

end LatticeProb.Lattice.Planar
