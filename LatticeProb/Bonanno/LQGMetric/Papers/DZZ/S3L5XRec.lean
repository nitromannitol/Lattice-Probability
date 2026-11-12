/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5XRec at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XNest

/-!
# DZZ Lemma 3.5: the `i_r` recursion on the square grid (P2-DEC84, D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1071–1079): "let
`i_1 = max {i : ℂ_i encloses u}`, and define recursively `i_r = max {i > i_{r-1} : ℂ_i
intersects ℂ_{i_{r-1}}}` till `r_0` such that one can not define `i_{r_0+1}`, then `A_δ` is
connected to `ℂ_start ∪ ℂ_{i_1}` and respectively `B_δ` to `ℂ_end ∪ ℂ_{i_{r_0}}`."

On the level-`N` grid (decision D84, DEC-84 §4), with rings `Ring i` of squares around the cells
`C i` (`i < d`) and a 4-path `p 0, …, p M` of squares through `C 0, …, C (d-1)` in order:

* `Tch X Y`: two sets of squares share a square or contain 4-adjacent squares.
* **`l35_recursion`**: DZZ's chain `i_1 < … < i_{r_0}` of touching rings exists, `p 0` is
  enclosed by (or on) `Ring i_1` and `p M` by (or on) `Ring i_{r_0}`. The last claim (DZZ: "then
  `B_δ` is connected to `ℂ_{i_{r_0}}`") is proved by contradiction with the nesting `not_esc_nest`.

Own argument (DZZ's sketch made rigorous); DEVIATIONS DV-D84.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- Two sets of squares share a square or contain 4-adjacent squares. -/
def Tch (X Y : Set DyBox) : Prop := ∃ x ∈ X, ∃ y ∈ Y, x = y ∨ SqAdj x y

lemma Tch.symm {X Y : Set DyBox} (h : Tch X Y) : Tch Y X := by
  obtain ⟨x, hx, y, hy, h⟩ := h
  exact ⟨y, hy, x, hx, h.elim (fun e => Or.inl e.symm) fun e => Or.inr e.symm⟩

lemma esc_mono {X Y : Set DyBox} {Λ : Set ℂ} {s : DyBox} (hXY : X ⊆ Y) (h : Esc Y Λ s) :
    Esc X Λ s := by
  obtain ⟨hs, t, hst, ht⟩ := h
  refine ⟨fun hx => hs (hXY hx), t, ?_, ht⟩
  clear ht
  induction hst with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail ⟨hbc.1, fun hx => hbc.2 (hXY hx)⟩

/-- Squares joined inside `Y`. -/
def ConnIn (Y : Set DyBox) (x y : DyBox) : Prop :=
  x ∈ Y ∧ Relation.ReflTransGen (fun a b => SqAdj a b ∧ b ∈ Y) x y

lemma ConnIn.trans {Y : Set DyBox} {x y z : DyBox} (h1 : ConnIn Y x y) (h2 : ConnIn Y y z) :
    ConnIn Y x z := ⟨h1.1, h1.2.trans h2.2⟩

lemma ConnIn.symm {Y : Set DyBox} {x y : DyBox} (h : ConnIn Y x y) : ConnIn Y y x := by
  obtain ⟨hx, h⟩ := h
  have key : ∀ z, Relation.ReflTransGen (fun a b => SqAdj a b ∧ b ∈ Y) x z →
      z ∈ Y ∧ Relation.ReflTransGen (fun a b => SqAdj a b ∧ b ∈ Y) z x := by
    intro z hz
    induction hz with
    | refl => exact ⟨hx, .refl⟩
    | tail _ hbc ih =>
      rename_i b c _
      exact ⟨hbc.2, Relation.ReflTransGen.head ⟨hbc.1.symm, ih.1⟩ ih.2⟩
  exact key y h

lemma ConnIn.mono {Y Z : Set DyBox} (hYZ : Y ⊆ Z) {x y : DyBox} (h : ConnIn Y x y) :
    ConnIn Z x y := by
  obtain ⟨hx, h⟩ := h
  refine ⟨hYZ hx, ?_⟩
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail ⟨hbc.1, hYZ hbc.2⟩

/-- The union of a touching chain of 4-connected rings is 4-connected. -/
lemma connIn_chain {Ring : ℕ → Set DyBox} {g : ℕ → ℕ} {r : ℕ}
    (hconn : ∀ q ≤ r, ∀ x ∈ Ring (g q), ∀ y ∈ Ring (g q), ConnIn (Ring (g q)) x y)
    (htch : ∀ q < r, Tch (Ring (g q)) (Ring (g (q + 1)))) :
    ∀ q ≤ r, ∀ x ∈ {z | ∃ q' ≤ q, z ∈ Ring (g q')}, ∀ y ∈ {z | ∃ q' ≤ q, z ∈ Ring (g q')},
      ConnIn {z | ∃ q' ≤ r, z ∈ Ring (g q')} x y := by
  set Y := {z | ∃ q' ≤ r, z ∈ Ring (g q')}
  have sub : ∀ q ≤ r, Ring (g q) ⊆ Y := fun q hq z hz => ⟨q, hq, hz⟩
  intro q
  induction q with
  | zero =>
    rintro - x ⟨q', hq', hx⟩ y ⟨q'', hq'', hy⟩
    obtain rfl : q' = 0 := by omega
    obtain rfl : q'' = 0 := by omega
    exact (hconn 0 (by omega) x hx y hy).mono (sub 0 (by omega))
  | succ q ih =>
    intro hq
    obtain ⟨x0, hx0, y0, hy0, hxy⟩ := htch q (by omega)
    have link : ConnIn Y x0 y0 := by
      rcases hxy with rfl | h
      · exact ⟨sub q (by omega) hx0, .refl⟩
      · exact ⟨sub q (by omega) hx0, .single ⟨h, sub (q + 1) hq hy0⟩⟩
    -- every point of the union up to `q + 1` is joined to `x0`
    have hto : ∀ x ∈ {z | ∃ q' ≤ q + 1, z ∈ Ring (g q')}, ConnIn Y x0 x := by
      rintro x ⟨q', hq', hx⟩
      rcases Nat.lt_or_ge q' (q + 1) with h | h
      · exact ih (by omega) x0 ⟨q, le_rfl, hx0⟩ x ⟨q', by omega, hx⟩
      · obtain rfl : q' = q + 1 := by omega
        exact link.trans ((hconn (q + 1) hq y0 hy0 x hx).mono (sub (q + 1) hq))
    intro x hx y hy
    exact (hto x hx).symm.trans (hto y hy)

open Classical in
/-- Greedy construction of DZZ's chain: from `g 0`, repeatedly the largest later index related to
the current one, until none is left. -/
lemma exists_max_chain (Rel : ℕ → ℕ → Prop) (d : ℕ) :
    ∀ n r (g : ℕ → ℕ), (∀ q ≤ r, g q < d) →
      (∀ q < r, g q < g (q + 1) ∧ Rel (g (q + 1)) (g q) ∧
        ∀ j, g (q + 1) < j → j < d → ¬ Rel j (g q)) → d - g r ≤ n →
      ∃ r' : ℕ, ∃ g' : ℕ → ℕ, g' 0 = g 0 ∧ (∀ q ≤ r', g' q < d) ∧
        (∀ q < r', g' q < g' (q + 1) ∧ Rel (g' (q + 1)) (g' q) ∧
          ∀ j, g' (q + 1) < j → j < d → ¬ Rel j (g' q)) ∧
        ∀ j, g' r' < j → j < d → ¬ Rel j (g' r') := by
  intro n
  induction n with
  | zero =>
    intro r g hgd _ hn
    have := hgd r le_rfl
    omega
  | succ n ih =>
    intro r g hgd hgs hn
    by_cases hterm : ∀ j, g r < j → j < d → ¬ Rel j (g r)
    · exact ⟨r, g, rfl, hgd, hgs, hterm⟩
    push_neg at hterm
    obtain ⟨j, hj1, hj2, hj3⟩ := hterm
    set P : ℕ → Prop := fun j => g r < j ∧ Rel j (g r) with hP
    set js := Nat.findGreatest P (d - 1) with hjs
    have hPs : P js := Nat.findGreatest_spec (m := j) (by omega) ⟨hj1, hj3⟩
    have hjsd : js ≤ d - 1 := Nat.findGreatest_le _
    have hmax : ∀ k, js < k → k ≤ d - 1 → ¬ P k := fun k h1 h2 =>
      Nat.findGreatest_is_greatest h1 h2
    set g' : ℕ → ℕ := fun q => if q ≤ r then g q else js with hg'
    have e1 : ∀ q ≤ r, g' q = g q := fun q hq => by simp only [hg', if_pos hq]
    have e2 : g' (r + 1) = js := by simp only [hg']; rw [if_neg (by omega)]
    obtain ⟨r', g'', h0, h1, h2, h3⟩ := ih (r + 1) g' (fun q hq => by
        rcases Nat.lt_or_ge q (r + 1) with h | h
        · rw [e1 q (by omega)]; exact hgd q (by omega)
        · obtain rfl : q = r + 1 := by omega
          rw [e2]; omega)
      (fun q hq => by
        rcases Nat.lt_or_ge q r with h | h
        · rw [e1 q h.le, e1 (q + 1) h]; exact hgs q h
        · obtain rfl : q = r := by omega
          rw [e1 q le_rfl, e2]
          exact ⟨hPs.1, hPs.2, fun k hk1 hk2 hR => hmax k hk1 (by omega) ⟨by omega, hR⟩⟩)
      (by rw [e2]; omega)
    exact ⟨r', g'', by rw [h0, e1 0 (Nat.zero_le _)], h1, h2, h3⟩

lemma chain_mono {g : ℕ → ℕ} {r : ℕ} (h : ∀ q < r, g q < g (q + 1)) :
    ∀ k q, q + k ≤ r → g q ≤ g (q + k) := by
  intro k
  induction k with
  | zero => intro q _; exact le_rfl
  | succ k ih =>
    intro q hq
    exact (ih q (by omega)).trans ((h (q + k) (by omega)).le)

/-- **DZZ's `i_r` recursion** (l. 1071–1079) on the level-`N` grid. Rings `Ring i` enclose the
squares of the cells `C i` (`i < d`, F1), are 4-connected, and `p 0, …, p M` is a path of squares
(equal or 4-adjacent consecutive ones) through `C 0, …, C (d - 1)` in order. Then there is a
chain `g 0 < … < g r` of touching rings with `p 0` enclosed by `Ring (g 0)` and `p M` enclosed by
`Ring (g r)` (in `C_large`; squares on a ring count as enclosed). -/
theorem l35_recursion {N d M : ℕ} (C : ℕ → DyBox) (Ring : ℕ → Set DyBox) (p : ℕ → DyBox)
    (lab : ℕ → ℕ) (hC1 : ∀ i < d, 1 ≤ (C i).n) (hCN : ∀ i < d, (C i).n + 1 ≤ N)
    (hF1 : ∀ i < d, ∀ s : DyBox, s.n = N → s.closedBox ⊆ (C i).closedBox →
      s ∉ Ring i ∧ ¬ Esc (Ring i) (C i).largeBox s)
    (hconn : ∀ i < d, ∀ x ∈ Ring i, ∀ y ∈ Ring i, ConnIn (Ring i) x y)
    (hpn : ∀ t ≤ M, (p t).n = N) (hstep : ∀ t < M, p t = p (t + 1) ∨ SqAdj (p t) (p (t + 1)))
    (hlab : ∀ t ≤ M, lab t < d ∧ (p t).closedBox ⊆ (C (lab t)).closedBox)
    (hmono : ∀ t < M, lab t ≤ lab (t + 1) ∧ lab (t + 1) ≤ lab t + 1)
    (h0 : lab 0 = 0) (hM : lab M + 1 = d) :
    ∃ r : ℕ, ∃ g : ℕ → ℕ, (∀ q ≤ r, g q < d) ∧
      (∀ q < r, g q < g (q + 1) ∧ Tch (Ring (g q)) (Ring (g (q + 1)))) ∧
      ¬ Esc (Ring (g 0)) (C (g 0)).largeBox (p 0) ∧ ¬ Esc (Ring (g r)) (C (g r)).largeBox (p M) := by
  classical
  have hd : 0 < d := by omega
  have hE0 : ¬ Esc (Ring 0) (C 0).largeBox (p 0) := (hF1 0 hd (p 0) (hpn 0 (by omega))
    (by have := (hlab 0 (by omega)).2; rwa [h0] at this)).2
  set i1 := Nat.findGreatest (fun i => ¬ Esc (Ring i) (C i).largeBox (p 0)) (d - 1) with hi1def
  have hi1 : ¬ Esc (Ring i1) (C i1).largeBox (p 0) :=
    Nat.findGreatest_spec (P := fun i => ¬ Esc (Ring i) (C i).largeBox (p 0)) (m := 0) (by omega) hE0
  have hi1d : i1 < d := by
    have := Nat.findGreatest_le (P := fun i => ¬ Esc (Ring i) (C i).largeBox (p 0)) (d - 1)
    omega
  have hi1max : ∀ j, i1 < j → j < d → Esc (Ring j) (C j).largeBox (p 0) := fun j h1 h2 => by
    have := Nat.findGreatest_is_greatest (P := fun i => ¬ Esc (Ring i) (C i).largeBox (p 0)) h1
      (by omega)
    exact not_not.1 this
  obtain ⟨r, g, hg0, hgd, hgs, hterm⟩ := exists_max_chain (fun j i => Tch (Ring j) (Ring i)) d
    (d - (fun _ => i1) 0) 0 (fun _ => i1) (fun _ _ => hi1d) (fun q hq => absurd hq (by omega)) le_rfl

  refine ⟨r, g, hgd, fun q hq => ⟨(hgs q hq).1, (hgs q hq).2.1.symm⟩, hg0 ▸ hi1, ?_⟩
  intro hEsc
  have hJd : g r < d := hgd r le_rfl
  have hgmono : ∀ q ≤ r, g q ≤ g r := fun q hq => by
    have := chain_mono (fun q hq => (hgs q hq).1) (r - q) q (by omega)
    rwa [show q + (r - q) = r by omega] at this
  -- the last time `t0` the path is in a cell of index `≤ g r`
  set t0 := Nat.findGreatest (fun t => lab t ≤ g r) M with ht0def
  have ht0 : lab t0 ≤ g r := Nat.findGreatest_spec (P := fun t => lab t ≤ g r) (m := 0)
    (Nat.zero_le _) (by show lab 0 ≤ g r; rw [h0]; omega)
  have ht0M : t0 ≤ M := Nat.findGreatest_le M
  have ht0g : ∀ t, t0 < t → t ≤ M → g r < lab t := fun t h1 h2 => by
    have := Nat.findGreatest_is_greatest (P := fun t => lab t ≤ g r) h1 h2
    omega
  have hlt0 : lab t0 = g r := by
    rcases Nat.lt_or_ge t0 M with h | h
    · have := ht0g (t0 + 1) (by omega) (by omega)
      have := (hmono t0 h).2
      omega
    · have e : t0 = M := by omega
      rw [e] at ht0 ⊢
      omega
  have hpt0 := hF1 (g r) hJd (p t0) (hpn t0 ht0M)
    (by have := (hlab t0 ht0M).2; rwa [hlt0] at this)
  -- after `t0` the path meets `Ring (g r)`
  have hreach : ∀ k, t0 + k ≤ M → (∀ t', t0 < t' → t' ≤ t0 + k → p t' ∉ Ring (g r)) →
      Relation.ReflTransGen (StepAv (Ring (g r))) (p t0) (p (t0 + k)) := by
    intro k
    induction k with
    | zero => intros; exact .refl
    | succ k ih =>
      intro hk hav
      have h1 := ih (by omega) (fun t' a b => hav t' a (by omega))
      rcases hstep (t0 + k) (by omega) with he | ha
      · rw [show t0 + (k + 1) = t0 + k + 1 by ring, ← he]; exact h1
      · exact h1.tail ⟨ha, hav _ (by omega) le_rfl⟩
  obtain ⟨t1, ht1a, ht1b, ht1R⟩ : ∃ t1, t0 < t1 ∧ t1 ≤ M ∧ p t1 ∈ Ring (g r) := by
    by_contra hno
    push Not at hno
    have := hreach (M - t0) (by omega) (fun t' a b => hno t' a (by omega))
    rw [show t0 + (M - t0) = M by omega] at this
    exact not_esc_of_reach this hpt0.1 hpt0.2 hEsc
  have hjJ : g r < lab t1 := ht0g t1 ht1a ht1b
  have hjd : lab t1 < d := (hlab t1 ht1b).1
  have hy := hF1 (lab t1) hjd (p t1) (hpn t1 ht1b) (hlab t1 ht1b).2
  -- `Ring (lab t1)` touches no ring of the chain
  have hnot : ∀ q ≤ r, ¬ Tch (Ring (lab t1)) (Ring (g q)) := by
    intro q hq
    rcases Nat.lt_or_ge q r with h | h
    · exact (hgs q h).2.2 (lab t1) (lt_of_le_of_lt (hgmono (q + 1) h) hjJ) hjd
    · obtain rfl : q = r := by omega
      exact hterm (lab t1) hjJ hjd
  set Y := {z | ∃ q' ≤ r, z ∈ Ring (g q')} with hYdef
  have hYj : ∀ x ∈ Y, x ∉ Ring (lab t1) := by
    rintro x ⟨q, hq, hx⟩ hxj
    exact hnot q hq ⟨x, hxj, x, hx, Or.inl rfl⟩
  have hYc := connIn_chain (Ring := Ring) (g := g) (r := r) (fun q hq => hconn (g q) (hgd q hq))
    (fun q hq => (hgs q hq).2.1.symm) r le_rfl
  have hyY : p t1 ∈ Y := ⟨r, le_rfl, ht1R⟩
  have hYE : ∀ x ∈ Y, x ∉ Ring (lab t1) ∧ ¬ Esc (Ring (lab t1)) (C (lab t1)).largeBox x := by
    intro x hx
    refine ⟨hYj x hx, ?_⟩
    obtain ⟨-, hpath⟩ := hYc (p t1) hyY x hx
    have : Relation.ReflTransGen (StepAv (Ring (lab t1))) (p t1) x := by
      clear hYc hx
      induction hpath with
      | refl => exact .refl
      | tail _ hbc ih => exact ih.tail ⟨hbc.1, hYj _ hbc.2⟩
    exact not_esc_of_reach this hy.1 hy.2
  -- nesting: `p 0` is enclosed by `Ring (lab t1)`, contradicting the choice of `i_1`
  have hp0j : ¬ Esc (Ring (lab t1)) (C (lab t1)).largeBox (p 0) := by
    by_cases hpj : p 0 ∈ Ring (lab t1)
    · exact fun h => h.1 hpj
    · refine not_esc_nest (C₁ := C (g 0)) (hC1 _ (hgd 0 (by omega)))
        (hCN _ (hgd 0 (by omega))) (hCN _ hjd) hYE (hpn 0 (by omega)) hpj ?_
      intro h
      have h' := esc_mono (fun z hz => (⟨0, Nat.zero_le _, hz⟩ : z ∈ Y)) h
      rw [hg0] at h'
      exact hi1 h'
  exact hp0j (hi1max (lab t1) (by have := hgmono 0 (Nat.zero_le _); rw [hg0] at this; omega) hjd)

end DZZ
end LQGMetric
