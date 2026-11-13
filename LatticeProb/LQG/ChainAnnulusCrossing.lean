import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.Basic

/-!
# A chain of connected sets that leaves an annulus meets one of its two circles

Deterministic topology behind the "first hitting of the two boundary circles" step in the planar
arguments for random walks on mated-CRT maps (Berestycki–Gwynne, arXiv:2003.10320, proof of Lemma 3.9 and
Lemma 3.10; Gwynne–Miller–Sheffield, arXiv:1807.07511, Section 3).

Let `J : ι → Set X` be a family of preconnected sets and `ξ : ℕ → ι` a sequence whose consecutive members
`J (ξ i)`, `J (ξ (i + 1))` meet (the cells of the successive vertices of a walk).

Main results:
* `exists_le_mem_eq_of_chain` and `exists_le_mem_eq_of_chain_down`: if the chain starts at a set with a
  point of `f ≤ r` and ends at a set with a point of `r ≤ f` (or the reverse), for a continuous
  `f : X → ℝ`, some set `J (ξ i)`, `i ≤ n`, meets the level set `{f = r}`.
* `exists_le_index_meets_circle_of_notMem_annulusCells`: a chain that starts in the open annulus
  `a < ‖· - c‖ < b` and ends at a set not contained in it has a member, with index `≤ n`, meeting the circle
  of radius `a` or of radius `b` around `c`.
* `exists_lt_index_meets_circle_of_mem`: if the chain ends in a set `I` of members lying inside the disc of
  radius `a` or outside the disc of radius `b`, the index can be taken `< n`.
-/

set_option autoImplicit false

open Set

namespace LatticeProb.LQG

section Level

variable {X ι : Type*} [TopologicalSpace X] {J : ι → Set X} {f : X → ℝ}

/-- **Crossing of a level by a chain of connected sets (upward).** -/
theorem exists_le_mem_eq_of_chain (hf : Continuous f) (hJ : ∀ k, IsPreconnected (J k)) :
    ∀ (n : ℕ) (ξ : ℕ → ι), (∀ i, (J (ξ i) ∩ J (ξ (i + 1))).Nonempty) → ∀ {r : ℝ},
      (∃ x ∈ J (ξ 0), f x ≤ r) → (∃ x ∈ J (ξ n), r ≤ f x) → ∃ i ≤ n, ∃ x ∈ J (ξ i), f x = r := by
  intro n
  induction n with
  | zero =>
    intro ξ _ r h₁ h₂
    obtain ⟨x₁, hx₁, hx₁'⟩ := h₁
    obtain ⟨x₂, hx₂, hx₂'⟩ := h₂
    obtain ⟨w, hw, hwr⟩ :=
      (hJ (ξ 0)).intermediate_value hx₁ hx₂ hf.continuousOn ⟨hx₁', hx₂'⟩
    exact ⟨0, le_rfl, w, hw, hwr⟩
  | succ n ih =>
    intro ξ hξ r h₁ h₂
    by_cases hbig : ∃ x ∈ J (ξ 0), r ≤ f x
    · obtain ⟨x₁, hx₁, hx₁'⟩ := h₁
      obtain ⟨x₂, hx₂, hx₂'⟩ := hbig
      obtain ⟨w, hw, hwr⟩ :=
        (hJ (ξ 0)).intermediate_value hx₁ hx₂ hf.continuousOn ⟨hx₁', hx₂'⟩
      exact ⟨0, Nat.zero_le _, w, hw, hwr⟩
    · push Not at hbig
      obtain ⟨x, hx1, hx2⟩ := hξ 0
      obtain ⟨i, hi, hx⟩ := ih (fun j => ξ (j + 1)) (fun j => hξ (j + 1))
        ⟨x, hx2, (hbig x hx1).le⟩ h₂
      exact ⟨i + 1, Nat.succ_le_succ hi, hx⟩

/-- **Crossing of a level by a chain of connected sets (downward).** -/
theorem exists_le_mem_eq_of_chain_down (hf : Continuous f) (hJ : ∀ k, IsPreconnected (J k))
    (n : ℕ) (ξ : ℕ → ι) (hξ : ∀ i, (J (ξ i) ∩ J (ξ (i + 1))).Nonempty) {r : ℝ}
    (h₁ : ∃ x ∈ J (ξ 0), r ≤ f x) (h₂ : ∃ x ∈ J (ξ n), f x ≤ r) :
    ∃ i ≤ n, ∃ x ∈ J (ξ i), f x = r := by
  obtain ⟨x₁, hx₁, hx₁'⟩ := h₁
  obtain ⟨x₂, hx₂, hx₂'⟩ := h₂
  obtain ⟨i, hi, x, hx, hxr⟩ := exists_le_mem_eq_of_chain (f := fun x => -f x) hf.neg hJ n ξ hξ
    (r := -r) ⟨x₁, hx₁, neg_le_neg hx₁'⟩ ⟨x₂, hx₂, neg_le_neg hx₂'⟩
  exact ⟨i, hi, x, hx, neg_inj.mp hxr⟩

end Level

section Annulus

variable {ι : Type*} {J : ι → Set ℂ}

/-- The members of the family lying in the open annulus `a < ‖· - c‖ < b`. -/
def annulusCells (J : ι → Set ℂ) (c : ℂ) (a b : ℝ) : Set ι :=
  {k | ∀ x ∈ J k, a < dist x c ∧ dist x c < b}

theorem notMem_annulusCells_iff {c : ℂ} {a b : ℝ} {k : ι} :
    k ∉ annulusCells J c a b ↔ ∃ x ∈ J k, dist x c ≤ a ∨ b ≤ dist x c := by
  simp only [annulusCells, mem_ofPred_eq, not_forall]
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, ?_⟩
    by_contra hcon
    push Not at hcon
    exact h ⟨hcon.1, hcon.2⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun h' => ?_⟩
    rcases h with h | h
    · exact absurd h'.1 (not_lt.mpr h)
    · exact absurd h'.2 (not_lt.mpr h)

/-- **A chain leaving an annulus meets one of its two circles.** If `J (ξ 0)` lies in the open annulus
`a < ‖· - c‖ < b` and is nonempty, and `J (ξ n)` meets its complement, some `J (ξ i)`, `i ≤ n`, meets the circle
of radius `a` or of radius `b` around `c`. -/
theorem exists_le_index_meets_circle_of_notMem_annulusCells (hJ : ∀ k, IsPreconnected (J k))
    {ξ : ℕ → ι} (hξ : ∀ i, (J (ξ i) ∩ J (ξ (i + 1))).Nonempty) {c : ℂ} {a b : ℝ} {n : ℕ}
    (h0 : ξ 0 ∈ annulusCells J c a b) (hne : (J (ξ 0)).Nonempty)
    (hn : ξ n ∉ annulusCells J c a b) :
    ∃ i ≤ n, ∃ x ∈ J (ξ i), dist x c = a ∨ dist x c = b := by
  have hf : Continuous fun x : ℂ => dist x c := continuous_id.dist continuous_const
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨y, hy, hy'⟩ := notMem_annulusCells_iff.mp hn
  rcases hy' with hya | hyb
  · obtain ⟨i, hi, x, hx, hxd⟩ := exists_le_mem_eq_of_chain_down (f := fun x : ℂ => dist x c) hf hJ n ξ
      hξ (r := a) ⟨x₀, hx₀, (h0 x₀ hx₀).1.le⟩ ⟨y, hy, hya⟩
    exact ⟨i, hi, x, hx, Or.inl hxd⟩
  · obtain ⟨i, hi, x, hx, hxd⟩ := exists_le_mem_eq_of_chain (f := fun x : ℂ => dist x c) hf hJ n ξ
      hξ (r := b) ⟨x₀, hx₀, (h0 x₀ hx₀).2.le⟩ ⟨y, hy, hyb⟩
    exact ⟨i, hi, x, hx, Or.inr hxd⟩

/-- **The circle is met strictly before a set `I` lying off both circles.** In addition to the hypotheses of
`exists_le_index_meets_circle_of_notMem_annulusCells`, suppose every member of `I` has a set inside the open
disc of radius `a` or outside the closed disc of radius `b`, and all sets are nonempty. If `ξ n ∈ I`, then some
`J (ξ i)` with `i < n` meets the circle of radius `a` or `b`. -/
theorem exists_lt_index_meets_circle_of_mem (hJ : ∀ k, IsPreconnected (J k)) (hne : ∀ k, (J k).Nonempty)
    {ξ : ℕ → ι} (hξ : ∀ i, (J (ξ i) ∩ J (ξ (i + 1))).Nonempty) {c : ℂ} {a b : ℝ} {n : ℕ}
    (h0 : ξ 0 ∈ annulusCells J c a b) {I : Set ι}
    (hI : ∀ k ∈ I, (∀ x ∈ J k, dist x c < a) ∨ (∀ x ∈ J k, b < dist x c)) (hn : ξ n ∈ I) :
    ∃ i < n, ∃ x ∈ J (ξ i), dist x c = a ∨ dist x c = b := by
  obtain ⟨x₀, hx₀⟩ := hne (ξ 0)
  obtain ⟨y, hy⟩ := hne (ξ n)
  have hnot : ξ n ∉ annulusCells J c a b := by
    refine notMem_annulusCells_iff.mpr ⟨y, hy, ?_⟩
    rcases hI _ hn with h | h
    · exact Or.inl (h y hy).le
    · exact Or.inr (h y hy).le
  obtain ⟨i, hi, x, hx, hxd⟩ := exists_le_index_meets_circle_of_notMem_annulusCells hJ hξ h0 ⟨x₀, hx₀⟩ hnot
  refine ⟨i, ?_, x, hx, hxd⟩
  rcases lt_or_eq_of_le hi with h | h
  · exact h
  · exfalso
    subst h
    have hab : a < b := (h0 x₀ hx₀).1.trans (h0 x₀ hx₀).2
    rcases hI _ hn with hh | hh
    · have := hh x hx
      rcases hxd with e | e
      · exact lt_irrefl _ (e ▸ this)
      · exact absurd (e ▸ this) (not_lt.mpr hab.le)
    · have := hh x hx
      rcases hxd with e | e
      · exact absurd (e ▸ this) (not_lt.mpr hab.le)
      · exact lt_irrefl _ (e ▸ this)

end Annulus

end LatticeProb.LQG
