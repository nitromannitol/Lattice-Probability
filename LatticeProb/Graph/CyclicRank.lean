/-
Moved from nitromannitol/rotor-23, `Rotor/Support/CyclicRank.lean`, Apache-2.0;
copyright 2026 Ahmed Bou-Rabee and Yuval Peres.  There the file is described
as "pure lemmas on the rank function of a cyclic permutation"
(`rotor.tex:1295-1310`), behind `eq:mean-continuations`; every declaration is
stated for a bare transitive `Equiv.Perm α` on a finite type, with no
reference to the rotor mechanism (the file's own `import Rotor.Model` is used
only for an unrelated notation convenience, not for any type in a
declaration below, confirmed by reading every signature), so it is moved
here unchanged, with only the namespace renamed.
-/
import Mathlib

/-!
# The cyclic rank of a transitively-acting permutation

For a permutation `σ` of a finite type acting transitively (`h : ∀ a b, ∃ k,
σ^k a = b`), `cycRank σ h x w` is the least `k ≥ 1` with `σ^k x = w`: the
position of `w` in the cyclic order that `σ` induces starting just after `x`.
The file develops its basic algebra (`cycRank_pos`, `cycRank_le`,
`cycRank_eq_of`, injectivity in each argument, `cycRank_self`) and its
counting consequences: `image_cycRank_{right,left}` show `cycRank σ h x`
bijects onto `Icc 1 (Fintype.card α)`, and `two_mul_sum_card_filter_lt` counts,
over all starting points `x`, how often one fixed point `c` precedes another
fixed point `a` in the cyclic order from `x`.
-/

open Finset

namespace LatticeProb.Graph

section Cyclic

variable {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)

omit [Fintype α] [DecidableEq α] in
/-- Transitivity gives a positive power carrying `x` to `w`. -/
theorem exists_pos_pow_eq (h : ∀ a b : α, ∃ k : ℕ, (σ ^ k) a = b) (x w : α) :
    ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = w := by
  obtain ⟨d, hd⟩ := h (σ x) w
  exact ⟨d + 1, Nat.succ_pos d, by simpa only [pow_succ, Equiv.Perm.mul_apply] using hd⟩

/-- The least `k ≥ 1` with `σ^k x = w`: the position of `w` in the cyclic
order starting just after `x`. -/
noncomputable def cycRank (h : ∀ a b : α, ∃ k : ℕ, (σ ^ k) a = b) (x w : α) : ℕ :=
  Nat.find (exists_pos_pow_eq σ h x w)

variable (h : ∀ a b : α, ∃ k : ℕ, (σ ^ k) a = b)

include h

omit [DecidableEq α] in
/-- A transitively-acting permutation is a single cycle on the whole type. -/
theorem isCycleOn_univ : σ.IsCycleOn ↑(univ : Finset α) := by
  refine ⟨?_, ?_⟩
  · simp
  · intro x _ y _
    obtain ⟨k, hk⟩ := h x y
    exact ⟨k, by simpa using hk⟩

omit [DecidableEq α] in
/-- A power fixes every point iff its exponent is a multiple of the
cardinality. -/
theorem pow_apply_eq_self_iff (x : α) (n : ℕ) : (σ ^ n) x = x ↔ Fintype.card α ∣ n := by
  have := (isCycleOn_univ σ h).pow_apply_eq (mem_univ x) (n := n)
  rwa [card_univ] at this

omit [DecidableEq α] in
/-- The `Fintype.card α`-th power is the identity. -/
theorem pow_card_apply (x : α) : (σ ^ Fintype.card α) x = x :=
  (pow_apply_eq_self_iff σ h x _).2 dvd_rfl

omit [Fintype α] in
/-- The cyclic rank is always positive. -/
theorem cycRank_pos (x w : α) : 0 < cycRank σ h x w :=
  (Nat.find_spec (exists_pos_pow_eq σ h x w)).1

omit [Fintype α] in
/-- The defining property of the cyclic rank. -/
theorem pow_cycRank (x w : α) : (σ ^ cycRank σ h x w) x = w :=
  (Nat.find_spec (exists_pos_pow_eq σ h x w)).2

/-- The cyclic rank never exceeds the cardinality of the type. -/
theorem cycRank_le (x w : α) : cycRank σ h x w ≤ Fintype.card α := by
  obtain ⟨k, hk, hkw⟩ := (isCycleOn_univ σ h).exists_pow_eq (mem_univ x) (mem_univ w)
  rw [card_univ] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hkw
    subst hkw
    exact Nat.find_min' _ ⟨Fintype.card_pos_iff.2 ⟨x⟩, pow_card_apply σ h x⟩
  · exact (Nat.find_min' _ ⟨hk0, hkw⟩).trans hk.le

/-- The cyclic rank is characterised by any positive exponent at most the
cardinality realising it. -/
theorem cycRank_eq_of {x w : α} {k : ℕ} (hk0 : 0 < k) (hkd : k ≤ Fintype.card α)
    (hkw : (σ ^ k) x = w) : cycRank σ h x w = k := by
  rw [cycRank, Nat.find_eq_iff]
  refine ⟨⟨hk0, hkw⟩, fun j hj hj' => ?_⟩
  obtain ⟨hj0, hjw⟩ := hj'
  have hw : (σ ^ (k - j)) w = w := by
    calc (σ ^ (k - j)) w = (σ ^ (k - j)) ((σ ^ j) x) := by rw [hjw]
      _ = (σ ^ (k - j + j)) x := by rw [pow_add, Equiv.Perm.mul_apply]
      _ = w := by rw [Nat.sub_add_cancel hj.le, hkw]
  rw [pow_apply_eq_self_iff σ h] at hw
  have := Nat.le_of_dvd (by omega) hw
  omega

omit [Fintype α] in
/-- The cyclic rank from a fixed starting point is injective in the target. -/
theorem cycRank_right_injective (x : α) : Function.Injective (cycRank σ h x) := by
  intro w w' he
  rw [← pow_cycRank σ h x w, ← pow_cycRank σ h x w', he]

omit [Fintype α] in
/-- The cyclic rank to a fixed target is injective in the starting point. -/
theorem cycRank_left_injective (w : α) : Function.Injective (fun x => cycRank σ h x w) := by
  intro x x' he
  have h1 := pow_cycRank σ h x w
  have h2 := pow_cycRank σ h x' w
  simp only at he
  rw [he] at h1
  exact (σ ^ cycRank σ h x' w).injective (h1.trans h2.symm)

/-- The cyclic rank of a point from itself is the cardinality of the type. -/
theorem cycRank_self (a : α) : cycRank σ h a a = Fintype.card α :=
  cycRank_eq_of σ h (Fintype.card_pos_iff.2 ⟨a⟩) le_rfl (pow_card_apply σ h a)

/-- The cyclic rank to any other point is strictly less than the
cardinality. -/
theorem cycRank_lt_card {a c : α} (hne : c ≠ a) : cycRank σ h a c < Fintype.card α := by
  refine lt_of_le_of_ne (cycRank_le σ h a c) fun he => hne ?_
  rw [← pow_cycRank σ h a c, he, pow_card_apply σ h]

/-- The cyclic rank from a fixed starting point bijects onto
`Icc 1 (Fintype.card α)`. -/
theorem image_cycRank_right (x : α) :
    (univ : Finset α).image (cycRank σ h x) = Icc 1 (Fintype.card α) := by
  apply eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨c, -, rfl⟩ := mem_image.1 hk
    exact mem_Icc.2 ⟨cycRank_pos σ h x c, cycRank_le σ h x c⟩
  · rw [Nat.card_Icc, card_image_of_injective _ (cycRank_right_injective σ h x), card_univ]
    omega

/-- The cyclic rank to a fixed target bijects onto `Icc 1 (Fintype.card α)`. -/
theorem image_cycRank_left (a : α) :
    (univ : Finset α).image (fun x => cycRank σ h x a) = Icc 1 (Fintype.card α) := by
  apply eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨x, -, rfl⟩ := mem_image.1 hk
    exact mem_Icc.2 ⟨cycRank_pos σ h x a, cycRank_le σ h x a⟩
  · rw [Nat.card_Icc, card_image_of_injective _ (cycRank_left_injective σ h a), card_univ]
    omega

/-- The number of points ranked before `a` from `x` is `cycRank σ h x a - 1`. -/
theorem card_filter_cycRank_lt (x a : α) :
    (univ.filter (fun c => cycRank σ h x c < cycRank σ h x a)).card = cycRank σ h x a - 1 := by
  have himg : (univ.filter (fun c => cycRank σ h x c < cycRank σ h x a)).image (cycRank σ h x)
      = (Icc 1 (Fintype.card α)).filter (fun k => k < cycRank σ h x a) := by
    rw [← image_cycRank_right σ h x, filter_image]
  have hIcc : (Icc 1 (Fintype.card α)).filter (fun k => k < cycRank σ h x a)
      = Ico 1 (cycRank σ h x a) := by
    ext k
    simp only [mem_filter, mem_Icc, mem_Ico]
    have := cycRank_le σ h x a
    omega
  rw [← card_image_of_injective _ (cycRank_right_injective σ h x), himg, hIcc, Nat.card_Ico]

/-- `eq:mean-continuations` in counting form: summed over the exits `c`, the
number of initial positions `x` with `c` before `a` is `d(d-1)/2`. -/
theorem two_mul_sum_card_filter_lt (a : α) :
    2 * ∑ c, (univ.filter (fun x => cycRank σ h x c < cycRank σ h x a)).card
      = Fintype.card α * (Fintype.card α - 1) := by
  have h1 : ∑ c, (univ.filter (fun x => cycRank σ h x c < cycRank σ h x a)).card
      = ∑ x, (univ.filter (fun c => cycRank σ h x c < cycRank σ h x a)).card := by
    simp only [card_filter]
    exact sum_comm
  rw [h1]
  simp only [card_filter_cycRank_lt]
  have h2 : ∑ x, (cycRank σ h x a - 1) = ∑ k ∈ Icc 1 (Fintype.card α), (k - 1) := by
    rw [← image_cycRank_left σ h a, sum_image]
    intro x _ y _ hxy
    exact cycRank_left_injective σ h a hxy
  have hI : Icc 1 (Fintype.card α) = Ico 1 (Fintype.card α + 1) := by
    ext k
    simp only [mem_Icc, mem_Ico]
    omega
  rw [h2, hI, sum_Ico_eq_sum_range]
  have h3 : ∑ k ∈ range (Fintype.card α + 1 - 1), (1 + k - 1) = ∑ k ∈ range (Fintype.card α), k := by
    rw [Nat.add_sub_cancel]
    exact sum_congr rfl (fun k _ => by omega)
  rw [h3, mul_comm, sum_range_id_mul_two]

end Cyclic

end LatticeProb.Graph
