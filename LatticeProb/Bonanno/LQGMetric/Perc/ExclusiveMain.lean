/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.ExclusiveMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.Exclusive

/-!
# Exclusivity of the two crossings, and crossings that must meet

See `LQGMetric.Perc.Exclusive` for the proof outline (crossing parity).

* `perc_not_goodLR_and_badTB`: not both a left–right `4`-crossing of good sites and a
  top–bottom `*`-crossing of bad sites;
* `percGoodLR_iff_not_percBadTB`: exactly one of them (with `percGoodLR_or_percBadTB`);
* `percGoodLR_meets_percBadTB`: a left–right `4`-crossing of sites of `A` and a top–bottom
  `*`-crossing of sites of `C` share a grid site of `A ∩ C`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

namespace PercExcl

variable {K L : ℤ} {u0 : ℤ × ℤ} {t : List (ℤ × ℤ)}

/-- The parity function: steps crossing the line right of `x`, below `x`. -/
def piX (p : List (ℤ × ℤ)) (x : ℤ × ℤ) : ℕ := percStepSum (wH x.1 x.2) p

section Neighbours

variable (hc : (u0 :: t).IsChain (RowStep L)) (h0 : u0.1 = K)
  (hl : ((u0 :: t).getLast (List.cons_ne_nil _ _)).1 = 0)
include hc h0 hl

lemma nb_right {x y : ℤ × ℤ} (hx : x ∉ u0 :: t) (hy : y ∉ u0 :: t) (hx0 : 0 ≤ x.1)
    (hyK : y.1 < K) (h1 : y.1 = x.1 + 1)
    (h2 : y.2 = x.2 ∨ y.2 = x.2 + 1 ∨ x.2 = y.2 + 1) :
    (Even (piX (u0 :: t) x) ↔ Even (piX (u0 :: t) y)) := by
  unfold piX
  rw [h1]
  rcases h2 with h2 | h2 | h2
  · have e := half hc h0 hl x.1 x.2 hx0 (by omega)
    rw [V_zero (x := y) hy ⟨h1, Or.inl h2⟩, add_zero, Nat.even_add] at e
    rw [h2]; exact e
  · have e := half hc h0 hl x.1 (x.2 + 1) hx0 (by omega)
    rw [V_zero (x := y) hy ⟨h1, Or.inl h2⟩, add_zero, Nat.even_add,
      split hc x.1 x.2 (x.2 + 1) rfl, Hrow_zero (x := x) hx ⟨Or.inl rfl, rfl⟩,
      add_zero] at e
    rw [h2]; exact e
  · have e := half hc h0 hl x.1 y.2 hx0 (by omega)
    rw [V_zero (x := y) hy ⟨h1, Or.inl rfl⟩, add_zero, Nat.even_add] at e
    rw [split hc x.1 y.2 x.2 h2, Hrow_zero (x := y) hy ⟨Or.inr h1, rfl⟩, add_zero]
    exact e

omit h0 hl in
lemma nb_up {x y : ℤ × ℤ} (hx : x ∉ u0 :: t) (h1 : y.1 = x.1) (h2 : y.2 = x.2 + 1) :
    (Even (piX (u0 :: t) x) ↔ Even (piX (u0 :: t) y)) := by
  unfold piX
  rw [h1, split hc x.1 x.2 y.2 h2, Hrow_zero (x := x) hx ⟨Or.inl rfl, rfl⟩, add_zero]

lemma nb {x y : ℤ × ℤ} (hx : x ∉ u0 :: t) (hy : y ∉ u0 :: t) (hx0 : 0 ≤ x.1) (hxK : x.1 < K)
    (hy0 : 0 ≤ y.1) (hyK : y.1 < K) (hxy : PercAdjK x y) :
    (Even (piX (u0 :: t) x) ↔ Even (piX (u0 :: t) y)) := by
  simp only [PercAdjK] at hxy
  by_cases e1 : y.1 = x.1
  · by_cases e2 : y.2 = x.2 + 1
    · exact nb_up hc hx e1 e2
    · exact (nb_up hc hy e1.symm (by omega)).symm
  · by_cases e3 : y.1 = x.1 + 1
    · exact nb_right hc h0 hl hx hy hx0 hyK e3 (by omega)
    · exact (nb_right hc h0 hl hy hx hy0 hxK (by omega) (by omega)).symm

lemma top {x : ℤ × ℤ} (hx : x ∉ u0 :: t) (hx0 : 0 ≤ x.1) (hxK : x.1 < K) (hxL : x.2 = L - 1) :
    ¬ Even (piX (u0 :: t) x) := by
  have e := line hc h0 hl x.1 hx0 hxK
  rw [split hc x.1 x.2 L (by omega), Hrow_zero (x := x) hx ⟨Or.inl rfl, rfl⟩, add_zero] at e
  exact e

end Neighbours

lemma goodStep_symm {K L : ℤ} {good : ℤ × ℤ → Prop} {x y : ℤ × ℤ}
    (h : PercGoodStep K L good x y) : PercGoodStep K L good y x := by
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨c, d, a, b, ?_⟩
  simp only [PercAdj4] at e ⊢; omega

lemma goodStep_rtg_symm {K L : ℤ} {good : ℤ × ℤ → Prop} {a b : ℤ × ℤ}
    (h : Relation.ReflTransGen (PercGoodStep K L good) a b) :
    Relation.ReflTransGen (PercGoodStep K L good) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact Relation.ReflTransGen.head (goodStep_symm hs) ih

lemma goodStep_end {K L : ℤ} {good : ℤ × ℤ → Prop} {a b : ℤ × ℤ}
    (h : Relation.ReflTransGen (PercGoodStep K L good) a b) (ha : percInGrid K L a ∧ good a) :
    percInGrid K L b ∧ good b := by
  induction h with
  | refl => exact ha
  | tail _ hs _ => exact ⟨hs.2.2.1, hs.2.2.2.1⟩

lemma chain_mem {K L : ℤ} {good : ℤ × ℤ → Prop} :
    ∀ (b : ℤ × ℤ) (l : List (ℤ × ℤ)), (b :: l).IsChain (PercGoodStep K L good) →
      percInGrid K L b ∧ good b → ∀ z ∈ b :: l, percInGrid K L z ∧ good z
  | b, [], _, hb, z, hz => by simp at hz; exact hz ▸ hb
  | b, c :: l, hc, hb, z, hz => by
    rw [List.isChain_cons_cons] at hc
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hb
    · exact chain_mem c l hc.2 ⟨hc.1.2.2.1, hc.1.2.2.2.1⟩ z (by simpa using hz)

end PercExcl

open PercExcl in
/-- **Exclusivity**: a left–right `4`-crossing of good sites and a top–bottom `*`-crossing of
bad sites of the same rectangle cannot both exist. -/
theorem perc_not_goodLR_and_badTB {K L : ℤ} {good : ℤ × ℤ → Prop} :
    ¬ (PercGoodLR K L good ∧ PercBadTB K L good) := by
  rintro ⟨⟨a, b, ha, hb, hagrid, hagood, hab⟩, ⟨a', b', ha', hb', ha'grid, ha'bad, hQ⟩⟩
  have hbg := goodStep_end hab ⟨hagrid, hagood⟩
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen
    (goodStep_rtg_symm hab)
  have hlp : ((((K, b.2) :: b :: l : List (ℤ × ℤ))).getLast (List.cons_ne_nil _ _)).1 = 0 := by
    rw [List.getLast_cons_cons, hlast, ha]
  set p := ((K, b.2) :: b :: l : List (ℤ × ℤ)) with hp
  have hmem := chain_mem b l hl hbg
  have hc : p.IsChain (RowStep L) := by
    rw [hp, List.isChain_cons_cons]
    refine ⟨?_, hl.imp fun x y h => ⟨h.2.2.2.2, h.1.2.2.1, h.1.2.2.2, h.2.2.1.2.2.1,
      h.2.2.1.2.2.2⟩⟩
    obtain ⟨-, -, h3, h4⟩ := hbg.1
    exact ⟨Or.inr ⟨rfl, Or.inl (by simp; omega)⟩, h3, h4, h3, h4⟩
  have hoff : ∀ x, percInGrid K L x → ¬ good x → x ∉ p := by
    intro x hx hxb hxp
    rw [hp, List.mem_cons] at hxp
    rcases hxp with rfl | hxp
    · exact absurd hx.2.1 (by simp)
    · exact hxb (hmem x hxp).2
  have hpar : ∀ z, Relation.ReflTransGen (PercBadStep K L good) a' z →
      (Even (piX p a') ↔ Even (piX p z)) := by
    intro z hz
    induction hz with
    | refl => exact Iff.rfl
    | @tail c z _ hs ih =>
      obtain ⟨hc1, hc2, hz1, hz2, hadj⟩ := hs
      exact ih.trans (nb hc rfl hlp (hoff c hc1 hc2) (hoff z hz1 hz2) hc1.1 hc1.2.1 hz1.1
        hz1.2.1 hadj)
  have h1 := top hc rfl hlp (hoff a' ha'grid ha'bad) ha'grid.1 ha'grid.2.1 ha'
  have h2 : Even (piX p b') := by
    unfold piX; rw [hb', bottom hc]; exact ⟨0, rfl⟩
  exact h1 ((hpar b' hQ).mpr h2)

/-- A left–right `4`-crossing of sites of `A` and a top–bottom `*`-crossing of sites of `C` of
the same rectangle share a grid site. (For a top–bottom `4`-crossing apply it with
`PercAdj4 → PercAdjK`.) -/
theorem percGoodLR_meets_percBadTB {K L : ℤ} (A C : Set (ℤ × ℤ))
    (hA : PercGoodLR K L (· ∈ A)) (hC : PercBadTB K L (· ∉ C)) :
    ∃ z, percInGrid K L z ∧ z ∈ A ∧ z ∈ C := by
  by_contra hno
  push Not at hno
  apply perc_not_goodLR_and_badTB (good := (· ∉ C))
  refine ⟨?_, hC⟩
  obtain ⟨a, b, ha, hb, hag, haA, hab⟩ := hA
  refine ⟨a, b, ha, hb, hag, hno a hag haA, ?_⟩
  refine Relation.ReflTransGen.mono (r := PercGoodStep K L (· ∈ A))
    (fun x y (h : PercGoodStep K L (· ∈ A) x y) => (?_ : PercGoodStep K L (· ∉ C) x y)) a b hab
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, hno x h1 h2, h3, hno y h3 h4, h5⟩

end LQGMetric
