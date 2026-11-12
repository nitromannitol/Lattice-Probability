/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperWalk at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36Graph

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Straight walks in the 8-neighbour graph `εℤ²` (DFGPS (eq:graph), T:1606)

Deterministic combinatorics for the upper half of DFGPS Lemma 3.6 (decision D52): the straight
8-neighbour walk between two grid points (`gridWalk`), and the concatenation of a chain of such
walks (`exists_chain_walks`). Own elementary arguments (DEVIATIONS DV-DFC2-2).
-/

noncomputable section

open Set

namespace LQGMetric.DFGPS.L36

/-- the grid point `δ (k₁, k₂)` -/
def gpt (δ : ℝ) (k : ℤ × ℤ) : ℂ := ⟨k.1 * δ, k.2 * δ⟩

/-- `sign d · min(j, |d|)`: the `j`-th coordinate step towards `d` -/
def cstep (d : ℤ) (j : ℕ) : ℤ := d.sign * min (j : ℤ) |d|

/-- number of steps of the straight walk from `k` to `k'` -/
def wlen (k k' : ℤ × ℤ) : ℕ := max (k'.1 - k.1).natAbs (k'.2 - k.2).natAbs

/-- the `j`-th vertex of the straight walk -/
def wpt (δ : ℝ) (k k' : ℤ × ℤ) (j : ℕ) : ℂ :=
  gpt δ (k.1 + cstep (k'.1 - k.1) j, k.2 + cstep (k'.2 - k.2) j)

/-- the straight 8-neighbour walk from `δk` to `δk'` -/
def gridWalk (δ : ℝ) (k k' : ℤ × ℤ) : List ℂ :=
  (List.range (wlen k k' + 1)).map (wpt δ k k')

lemma cstep_zero (d : ℤ) : cstep d 0 = 0 := by
  simp [cstep, abs_nonneg]

lemma cstep_of_le {d : ℤ} {j : ℕ} (h : |d| ≤ j) : cstep d j = d := by
  unfold cstep
  rw [min_eq_right h, Int.sign_mul_abs]

lemma cstep_between (d : ℤ) (j : ℕ) : min 0 d ≤ cstep d j ∧ cstep d j ≤ max 0 d := by
  unfold cstep
  rcases lt_trichotomy d 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg h]
    constructor <;> [skip; skip] <;> simp [min_def, max_def] <;> split_ifs <;> omega
  · subst h; simp
  · rw [Int.sign_eq_one_of_pos h, abs_of_pos h]
    constructor <;> simp [min_def, max_def] <;> split_ifs <;> omega

lemma cstep_succ (d : ℤ) (j : ℕ) :
    |cstep d (j+1) - cstep d j| ≤ 1 ∧ ((j : ℤ) < |d| → cstep d (j+1) - cstep d j ≠ 0) := by
  unfold cstep
  rcases lt_trichotomy d 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg h]
    push_cast
    constructor
    · simp only [min_def]; split_ifs <;> rw [abs_le] <;> constructor <;> omega
    · intro hj; simp only [min_def]; split_ifs <;> omega
  · subst h; simp
  · rw [Int.sign_eq_one_of_pos h, abs_of_pos h]
    push_cast
    constructor
    · simp only [min_def]; split_ifs <;> rw [abs_le] <;> constructor <;> omega
    · intro hj; simp only [min_def]; split_ifs <;> omega

/-- a unit or diagonal step has length `δ` or `√2 δ` -/
lemma norm_step {δ : ℝ} (hδ : 0 < δ) (e₁ e₂ : ℤ) (h₁ : |e₁| ≤ 1) (h₂ : |e₂| ≤ 1)
    (h : e₁ ≠ 0 ∨ e₂ ≠ 0) :
    ‖(⟨e₁ * δ, e₂ * δ⟩ : ℂ)‖ = δ ∨ ‖(⟨e₁ * δ, e₂ * δ⟩ : ℂ)‖ = Real.sqrt 2 * δ := by
  have key : ‖(⟨e₁ * δ, e₂ * δ⟩ : ℂ)‖ ^ 2 = ((e₁ ^ 2 + e₂ ^ 2 : ℤ) : ℝ) * δ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; push_cast; ring
  have hs : e₁ ^ 2 + e₂ ^ 2 = 1 ∨ e₁ ^ 2 + e₂ ^ 2 = 2 := by
    rw [abs_le] at h₁ h₂
    have : e₁ = -1 ∨ e₁ = 0 ∨ e₁ = 1 := by omega
    have : e₂ = -1 ∨ e₂ = 0 ∨ e₂ = 1 := by omega
    rcases h with h | h <;> rcases ‹e₁ = -1 ∨ e₁ = 0 ∨ e₁ = 1› with h1 | h1 | h1 <;>
      rcases ‹e₂ = -1 ∨ e₂ = 0 ∨ e₂ = 1› with h2 | h2 | h2 <;> subst h1 h2 <;> simp_all
  rw [← Real.sqrt_sq (norm_nonneg _), key]
  rcases hs with hs | hs
  · left; rw [hs]; push_cast; rw [one_mul, Real.sqrt_sq hδ.le]
  · right; rw [hs]; push_cast; rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hδ.le]

lemma gridWalk_head (δ : ℝ) (k k' : ℤ × ℤ) : (gridWalk δ k k').head? = some (gpt δ k) := by
  rw [gridWalk, List.range_succ_eq_map]
  simp [wpt, cstep_zero]

lemma gridWalk_last (δ : ℝ) (k k' : ℤ × ℤ) : (gridWalk δ k k').getLast? = some (gpt δ k') := by
  rw [gridWalk, List.getLast?_map, List.getLast?_range]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
    Option.map_some]
  unfold wpt
  rw [cstep_of_le, cstep_of_le]
  · simp
  · have : (k'.2 - k.2).natAbs ≤ wlen k k' := le_max_right _ _
    rw [Int.abs_eq_natAbs]; exact_mod_cast this
  · have : (k'.1 - k.1).natAbs ≤ wlen k k' := le_max_left _ _
    rw [Int.abs_eq_natAbs]; exact_mod_cast this

lemma gridWalk_ne_nil (δ : ℝ) (k k' : ℤ × ℤ) : gridWalk δ k k' ≠ [] := by
  simp [gridWalk]

/-- every vertex of the walk is a grid point in the coordinate box spanned by `k`, `k'` -/
lemma mem_gridWalk {δ : ℝ} {k k' : ℤ × ℤ} {x : ℂ} (hx : x ∈ gridWalk δ k k') :
    ∃ c : ℤ × ℤ, x = gpt δ c ∧ min k.1 k'.1 ≤ c.1 ∧ c.1 ≤ max k.1 k'.1 ∧
      min k.2 k'.2 ≤ c.2 ∧ c.2 ≤ max k.2 k'.2 := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  refine ⟨_, rfl, ?_⟩
  have h1 := cstep_between (k'.1 - k.1) j
  have h2 := cstep_between (k'.2 - k.2) j
  simp only [min_def, max_def] at h1 h2 ⊢
  split_ifs at h1 h2 ⊢ <;> omega

lemma gridWalk_chain {δ : ℝ} (hδ : 0 < δ) (k k' : ℤ × ℤ) :
    (gridWalk δ k k').IsChain fun x y => ‖x - y‖ = δ ∨ ‖x - y‖ = Real.sqrt 2 * δ := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [gridWalk, List.length_map, List.length_range] at hi
  simp only [gridWalk, List.getElem_map, List.getElem_range]
  have hi' : (i : ℤ) < max |k'.1 - k.1| |k'.2 - k.2| := by
    have : i < wlen k k' := by omega
    unfold wlen at this
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    rcases le_total (k'.1 - k.1).natAbs (k'.2 - k.2).natAbs with h | h
    · rw [max_eq_right h] at this; rw [max_eq_right (by exact_mod_cast h)]; exact_mod_cast this
    · rw [max_eq_left h] at this; rw [max_eq_left (by exact_mod_cast h)]; exact_mod_cast this
  obtain ⟨a1, a2⟩ := cstep_succ (k'.1 - k.1) i
  obtain ⟨b1, b2⟩ := cstep_succ (k'.2 - k.2) i
  have hne : cstep (k'.1 - k.1) (i+1) - cstep (k'.1 - k.1) i ≠ 0 ∨
      cstep (k'.2 - k.2) (i+1) - cstep (k'.2 - k.2) i ≠ 0 := by
    rcases lt_max_iff.1 hi' with h | h
    · exact Or.inl (a2 h)
    · exact Or.inr (b2 h)
  have e : wpt δ k k' i - wpt δ k k' (i+1) =
      ⟨((-(cstep (k'.1 - k.1) (i+1) - cstep (k'.1 - k.1) i) : ℤ) : ℝ) * δ,
        ((-(cstep (k'.2 - k.2) (i+1) - cstep (k'.2 - k.2) i) : ℤ) : ℝ) * δ⟩ := by
    apply Complex.ext <;> simp [wpt, gpt] <;> ring
  rw [e]
  exact norm_step hδ _ _ (by rw [abs_neg]; exact a1) (by rw [abs_neg]; exact b1)
    (by rcases hne with h | h
        · exact Or.inl (neg_ne_zero.2 h)
        · exact Or.inr (neg_ne_zero.2 h))

/-- the walk minus its first vertex has `wlen` vertices -/
lemma gridWalk_eq_cons (δ : ℝ) (k k' : ℤ × ℤ) :
    gridWalk δ k k' = gpt δ k :: (gridWalk δ k k').tail := by
  have h := gridWalk_head δ k k'
  cases hw : gridWalk δ k k' with
  | nil => exact absurd hw (gridWalk_ne_nil δ k k')
  | cons a l => rw [hw] at h; simp only [List.head?_cons, Option.some.injEq] at h; rw [h]; rfl

lemma length_gridWalk_tail (δ : ℝ) (k k' : ℤ × ℤ) :
    (gridWalk δ k k').tail.length = wlen k k' := by
  simp [gridWalk]

/-- **Chain of straight walks.** Concatenating the walks `δU_i → δU_{i+1}` (`i < n`) gives a
path from `δU_0` to `δU_n` whose vertices lie on the walks, with `Σ f ≤ f(δU_0) + 3 Σ_i B_i`
when the steps have sup-length `≤ 3` and `f ≤ B_i` on the `i`-th walk. -/
theorem exists_chain_walks {δ : ℝ} (hδ : 0 < δ) (U : ℕ → ℤ × ℤ) (f : ℂ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (B : ℕ → ℝ) : ∀ n : ℕ,
    (∀ i < n, wlen (U i) (U (i+1)) ≤ 3) →
    (∀ i < n, ∀ x ∈ gridWalk δ (U i) (U (i+1)), f x ≤ B i) →
    ∃ L : List ℂ, L ≠ [] ∧ L.head? = some (gpt δ (U 0)) ∧ L.getLast? = some (gpt δ (U n)) ∧
      (L.IsChain fun x y => ‖x - y‖ = δ ∨ ‖x - y‖ = Real.sqrt 2 * δ) ∧
      (∀ x ∈ L, x = gpt δ (U 0) ∨ ∃ i < n, x ∈ gridWalk δ (U i) (U (i+1))) ∧
      (L.map f).sum ≤ f (gpt δ (U 0)) + 3 * ∑ i ∈ Finset.range n, B i
  | 0, _, _ => ⟨[gpt δ (U 0)], by simp, rfl, rfl, List.isChain_singleton _,
      fun x hx => Or.inl (List.mem_singleton.1 hx), by simp⟩
  | n + 1, hlen, hB => by
    obtain ⟨L, hL0, hLh, hLl, hLc, hLm, hLs⟩ := exists_chain_walks hδ U f hf B n
      (fun i hi => hlen i (by omega)) (fun i hi => hB i (by omega))
    set W := gridWalk δ (U n) (U (n+1)) with hW
    have hWc := gridWalk_chain hδ (U n) (U (n+1))
    have hWe := gridWalk_eq_cons δ (U n) (U (n+1))
    rw [← hW] at hWc hWe
    have hmem : gpt δ (U n) ∈ W := by rw [hWe]; exact List.mem_cons_self
    have hBn : 0 ≤ B n := (hf _).trans (hB n (by omega) _ hmem)
    refine ⟨L ++ W.tail, by simp [hL0], ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.head?_append, hLh]; rfl
    · rcases ht : W.tail with _ | ⟨a, l⟩
      · rw [List.append_nil, hLl]
        have hl := gridWalk_last δ (U n) (U (n+1))
        rw [← hW, hWe, ht] at hl
        simpa using hl
      · rw [List.getLast?_append, ← ht]
        have hl := gridWalk_last δ (U n) (U (n+1))
        rw [← hW, hWe] at hl
        rw [List.getLast?_cons, ht] at hl
        rw [ht]
        simp only [List.getLast?_cons, Option.some_or] at hl ⊢
        exact hl
    · rw [List.isChain_append]
      refine ⟨hLc, ?_, ?_⟩
      · rw [hWe] at hWc; exact hWc.tail
      · intro x hx y hy
        rw [hLl, Option.mem_def, Option.some.injEq] at hx
        subst hx
        rw [hWe] at hWc
        rcases ht : W.tail with _ | ⟨a, l⟩
        · rw [ht] at hy; simp at hy
        · rw [ht] at hy hWc
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy
          exact (List.isChain_cons_cons.1 hWc).1
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rcases hLm x hx with h | ⟨i, hi, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨i, by omega, h⟩
      · exact Or.inr ⟨n, by omega, List.mem_of_mem_tail hx⟩
    · rw [List.map_append, List.sum_append, Finset.sum_range_succ]
      have h1 : (W.tail.map f).sum ≤ (W.tail.map f).length • B n :=
        List.sum_le_length_nsmul _ _ fun y hy => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
          exact hB n (by omega) x (List.mem_of_mem_tail hx)
      rw [List.length_map, hW, length_gridWalk_tail, nsmul_eq_mul] at h1
      have h3 : (wlen (U n) (U (n+1)) : ℝ) ≤ 3 := by exact_mod_cast hlen n (by omega)
      nlinarith

end LQGMetric.DFGPS.L36
