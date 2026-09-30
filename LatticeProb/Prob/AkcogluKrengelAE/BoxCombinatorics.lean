import LatticeProb.Prob.AkcogluKrengelAE.Defs

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# Box combinatorics (Step 1)

Splitting a box along one coordinate is an `IsBoxSplit`; hence a subadditive, volume-bounded box
function `f` at a box is at most `f` at a nested box plus `C` times the volume difference, and `f`
of the cube `[0, k m)^d` is at most the sum of `f` over the `k ^ d` grid cubes of side `m`.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- A subadditive, nonnegative, volume-bounded box function vanishes on the empty box. -/
theorem boxFun_empty_eq_zero {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (ω : Ω) : f ∅ ω = 0 := by
  have h0 := hC ∅ ω
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at h0
  linarith [h0.1, h0.2]


omit [MeasurableSpace Ω] in
/-- The volume bound constant `C` is nonnegative, read off at the singleton box. -/
theorem nonneg_of_boxFun_bound {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (ω : Ω) : 0 ≤ C := by
  have h := hC ({0} : Finset (Site d)) ω
  simp at h
  linarith [h.1, h.2]


/-- `IsBoxSplit` is symmetric in its two pieces. -/
theorem isBoxSplit_symm {d : ℕ} {B B₁ B₂ : Finset (Site d)} (h : IsBoxSplit B B₁ B₂) :
    IsBoxSplit B B₂ B₁ := by
  obtain ⟨hB, hB₁, hB₂, hdisj, hunion⟩ := h
  exact ⟨hB, hB₂, hB₁, hdisj.symm, by rw [Finset.union_comm]; exact hunion⟩


omit [MeasurableSpace Ω] in
/-- Subadditivity along a box split bounds `f B` by `f B₁` plus `C` times the volume of the
complementary piece `B₂`. -/
theorem boxFun_le_add_defect_of_isBoxSplit {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    {B B₁ B₂ : Finset (Site d)} (h : IsBoxSplit B B₁ B₂) (ω : Ω) :
    f B ω ≤ f B₁ ω + C * ((B.card : ℝ) - B₁.card) := by
  have h1 : f B ω ≤ f B₁ ω + f B₂ ω := hsub B B₁ B₂ ω h
  have h2 : f B₂ ω ≤ C * (B₂.card : ℝ) := (hC B₂ ω).2
  have hcardnat : B.card = B₁.card + B₂.card := h.2.2.2.2 ▸ Finset.card_union_of_disjoint h.2.2.2.1
  have hcard : (B.card : ℝ) = (B₁.card : ℝ) + (B₂.card : ℝ) := (by exact_mod_cast hcardnat)
  have hcast : C * ((B.card : ℝ) - B₁.card) = C * (B₂.card : ℝ) := (by rw [hcard]; ring)
  linarith


/-- A site lies in the box `latticeBox a b` iff it lies between `a` and `b` in every coordinate. -/
theorem mem_latticeBox_iff {d : ℕ} (a b x : Site d) :
    x ∈ latticeBox a b ↔ ∀ j, a j ≤ x j ∧ x j ≤ b j := by
  simp only [latticeBox, Finset.mem_Icc, Pi.le_def, forall_and]

/-- Cutting a box at coordinate `i`, value `t`, produces two disjoint pieces. -/
theorem disjoint_latticeBox_update {d : ℕ} (a b : Site d) (i : Fin d) (t : ℤ) :
    Disjoint (latticeBox a (Function.update b i (t - 1))) (latticeBox (Function.update a i t) b) :=
        by
  rw [Finset.disjoint_left]
  intro x h1 h2
  have e1 := ((mem_latticeBox_iff _ _ x).1 h1 i).2
  have e2 := ((mem_latticeBox_iff _ _ x).1 h2 i).1
  rw [Function.update_self] at e1 e2
  omega

/-- The union of the two pieces obtained by cutting coordinate `i` at `t` is contained in the
original box, when `t` lies in its range. -/
theorem latticeBox_update_union_subset {d : ℕ} (a b : Site d) (i : Fin d) (t : ℤ) (h1 : a i
    ≤ t)
    (h2 : t ≤ b i + 1) :
    latticeBox a (Function.update b i (t - 1)) ∪ latticeBox (Function.update a i t) b ⊆
      latticeBox a b := by
  intro x hx
  rw [mem_latticeBox_iff]
  intro j
  rcases Finset.mem_union.1 hx with h | h
  · have hj := (mem_latticeBox_iff _ _ x).1 h j
    have hi := ((mem_latticeBox_iff _ _ x).1 h i).2
    rw [Function.update_self] at hi
    by_cases hji : j = i
    · subst hji; rw [Function.update_self] at hj; exact ⟨hj.1, by omega⟩
    · rw [Function.update_of_ne hji] at hj; exact hj
  · have hj := (mem_latticeBox_iff _ _ x).1 h j
    have hi := ((mem_latticeBox_iff _ _ x).1 h i).1
    rw [Function.update_self] at hi
    by_cases hji : j = i
    · subst hji; rw [Function.update_self] at hj; exact ⟨by omega, hj.2⟩
    · rw [Function.update_of_ne hji] at hj; exact hj

/-- Every point of the box lies in one of the two pieces obtained by cutting coordinate `i` at `t`.
-/
theorem subset_latticeBox_update_union {d : ℕ} (a b : Site d) (i : Fin d) (t : ℤ) :
    latticeBox a b ⊆
      latticeBox a (Function.update b i (t - 1)) ∪ latticeBox (Function.update a i t) b := by
  intro x hx
  have hb := (mem_latticeBox_iff _ _ x).1 hx
  rw [Finset.mem_union, mem_latticeBox_iff, mem_latticeBox_iff]
  rcases le_or_gt t (x i) with h | h
  · right; intro j; by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact ⟨h, (hb j).2⟩
    · simp only [Function.update_of_ne hj]; exact hb j
  · left; intro j; by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact ⟨(hb j).1, by omega⟩
    · simp only [Function.update_of_ne hj]; exact hb j

/-- Cutting a box at coordinate `i`, value `t` in its range, is an `IsBoxSplit` into the two pieces
below and at-or-above `t`. -/
theorem isBoxSplit_latticeBox_update_of_mem {d : ℕ} (a b : Site d) (i : Fin d) (t : ℤ) (h1 :
    a i ≤ t)
    (h2 : t ≤ b i + 1) :
    IsBoxSplit (latticeBox a b) (latticeBox a (Function.update b i (t - 1)))
      (latticeBox (Function.update a i t) b) := by
  exact ⟨⟨a, b, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, disjoint_latticeBox_update a b i t,
    Finset.Subset.antisymm (latticeBox_update_union_subset a b i t h1 h2)
        (subset_latticeBox_update_union a b i t)⟩

omit [MeasurableSpace Ω] in
/-- Trimming coordinate `i` of a box to a subinterval `[s, e]` decreases `f` by at most `C` times
the volume lost, via two applications of the coordinate cut
`isBoxSplit_latticeBox_update_of_mem`. -/
theorem boxFun_le_trim_add_defect {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (a b : Site d) (i : Fin d) (s e : ℤ) (h1 : a i ≤ s) (h2 : s ≤ e) (h3 : e ≤ b i) (ω : Ω) :
    f (latticeBox a b) ω ≤
      f (latticeBox (Function.update a i s) (Function.update b i e)) ω +
        C * (((latticeBox a b).card : ℝ) -
          (latticeBox (Function.update a i s) (Function.update b i e)).card) := by
  have hsplit1 := isBoxSplit_latticeBox_update_of_mem a b i s h1 (by omega)
  have hL := boxFun_le_add_defect_of_isBoxSplit hC hsub (isBoxSplit_symm hsplit1) ω
  have hsplit2 := isBoxSplit_latticeBox_update_of_mem (Function.update a i s) b i (e + 1)
      (by rw [Function.update_self]; omega) (by omega)
  have hU := boxFun_le_add_defect_of_isBoxSplit hC hsub hsplit2 ω
  rw [show (e + 1 : ℤ) - 1 = e from by omega] at hU
  linarith [hL, hU]


/-- Updating the indicator description of a box's corner at a coordinate `i` not yet in `S` matches
the description over `insert i S`. -/
theorem update_ite_mem_insert {d : ℕ} (S : Finset (Fin d)) (i : Fin d) (a a' : Site d) :
    Function.update (fun j => if j ∈ S then a' j else a j) i (a' i) =
      fun j => if j ∈ insert i S then a' j else a j := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [ hj, Finset.mem_insert]


omit [MeasurableSpace Ω] in
/-- Trimming a box in every coordinate of a subset `S` to a nested box decreases `f` by at most `C`
times the volume lost, by induction on `S` from the single-coordinate trim
`boxFun_le_trim_add_defect`. -/
theorem boxFun_le_trim_subset_add_defect {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (a b a' b' : Site d) (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) (ω : Ω) (S : Finset (Fin d)) :
    f (latticeBox a b) ω ≤
      f (latticeBox (fun j => if j ∈ S then a' j else a j) (fun j => if j ∈ S then b' j else b j)) ω
        + C * (((latticeBox a b).card : ℝ) -
          (latticeBox (fun j => if j ∈ S then a' j else a j)
            (fun j => if j ∈ S then b' j else b j)).card) := by
  induction S using Finset.induction with
  | empty => simp
  | insert i S h ih =>
    have h1 : (if i ∈ S then a' i else a i) ≤ a' i := by rw [if_neg h]; exact ha i
    have h2 : a' i ≤ b' i := hab i
    have h3 : b' i ≤ (if i ∈ S then b' i else b i) := by rw [if_neg h]; exact hb i
    have h6 := boxFun_le_trim_add_defect hC hsub (fun j => if j ∈ S then a' j else a j)
      (fun j => if j ∈ S then b' j else b j) i (a' i) (b' i) h1 h2 h3 ω
    have e1 := update_ite_mem_insert S i a a'
    have e2 := update_ite_mem_insert S i b b'
    rw [e1, e2] at h6
    linarith [ih, h6]

omit [MeasurableSpace Ω] in
/-- Trimming a box in every coordinate of a subset `S` to a nested box decreases `f` by at most `C`
times the volume lost. -/
theorem boxFun_le_trim_subset_add_defect' {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (a b a' b' : Site d) (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) (ω : Ω) (S : Finset (Fin d)) :
    f (latticeBox a b) ω ≤
      f (latticeBox (fun j => if j ∈ S then a' j else a j) (fun j => if j ∈ S then b' j else b j)) ω
        + C * (((latticeBox a b).card : ℝ) -
          (latticeBox (fun j => if j ∈ S then a' j else a j)
            (fun j => if j ∈ S then b' j else b j)).card) := by
  exact boxFun_le_trim_subset_add_defect hC hsub a b a' b' ha hab hb ω S


omit [MeasurableSpace Ω] in
/-- For any two nested boxes, `f` of the outer box is at most `f` of the inner box plus `C` times
the volume difference. -/
theorem boxFun_le_nested_add_defect {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (a b a' b' : Site d) (ha : a ≤ a') (hb : b' ≤ b) (ω : Ω) :
    f (latticeBox a b) ω ≤
      f (latticeBox a' b') ω + C * (((latticeBox a b).card : ℝ) - (latticeBox a' b').card) := by
  by_cases hab : a' ≤ b'
  · have h8 := boxFun_le_trim_subset_add_defect' (f := f) (C := C) hC hsub a b a' b' ha hab hb ω
      Finset.univ
    simpa using h8
  · rw [show latticeBox a' b' = (∅ : Finset (Site d)) from Finset.Icc_eq_empty hab]
    rw [boxFun_empty_eq_zero hC ω, Finset.card_empty]
    simpa using (hC (latticeBox a b) ω).2


/-- The cube `latticeCube d n` has `n ^ d` sites. -/
theorem card_latticeCube_eq_pow (d n : ℕ) : (latticeCube d n).card = n ^ d := by
  rw [latticeCube, Pi.card_Icc]
  simp only [Pi.zero_apply, Int.card_Icc, sub_zero,
    show ((n : ℤ) - 1 + 1) = (n : ℤ) from by ring, Int.toNat_natCast,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]


omit [MeasurableSpace Ω] in
/-- `f` of the cube of side `n` is at most `f` of the cube of side `m ≤ n` plus `C` times the volume
difference `n ^ d - m ^ d`. -/
theorem boxFun_cube_le_cube_add_defect {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    {m n : ℕ} (hmn : m ≤ n) (ω : Ω) :
    f (latticeCube d n) ω ≤ f (latticeCube d m) ω + C * ((n : ℝ) ^ d - (m : ℝ) ^ d) := by
  have hb : (fun _ : Fin d => (m : ℤ) - 1) ≤ (fun _ : Fin d => (n : ℤ) - 1) :=
    fun i => sub_le_sub_right (Int.ofNat_le.mpr hmn) 1
  have h := boxFun_le_nested_add_defect hC hsub (0 : Site d) (fun _ => (n : ℤ) - 1) (0 : Site d)
    (fun _ => (m : ℤ) - 1) le_rfl hb ω
  have h1 : (latticeBox (0 : Site d) (fun _ => (n : ℤ) - 1)).card = n ^ d := card_latticeCube_eq_pow
      d n
  have h2 : (latticeBox (0 : Site d) (fun _ => (m : ℤ) - 1)).card = m ^ d := card_latticeCube_eq_pow
      d m
  rw [h1, h2, Nat.cast_pow, Nat.cast_pow] at h
  exact h


/-- Translating the cube of side `m` by `z` gives the box with lower corner `z` and side `m`. -/
theorem map_addRight_latticeCube_eq_latticeBox (d m : ℕ) (z : Site d) :
    (latticeCube d m).map (Equiv.addRight z).toEmbedding =
      latticeBox z (fun i => z i + (m : ℤ) - 1) := by
  simp only [latticeCube, latticeBox]
  have h : (Equiv.addRight z).toEmbedding = addRightEmbedding z := rfl
  rw [h, Finset.map_add_right_Icc]
  congr 1 <;> funext i <;> simp only [Pi.add_apply, Pi.zero_apply] <;> ring


omit [MeasurableSpace Ω] in
/-- `f` vanishes on a box whose bounds are inverted in some coordinate, since the box is empty. -/
theorem boxFun_eq_zero_of_lt_apply {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) {a b : Site d} {i : Fin d} (hlt : b i < a i)
    (ω : Ω) : f (latticeBox a b) ω = 0 := by
  have he : latticeBox a b = ∅ := Finset.Icc_eq_empty (fun h => absurd (h i) (not_le.2 hlt))
  rw [he]
  exact boxFun_empty_eq_zero hC ω

omit [MeasurableSpace Ω] in
/-- Induction step for the one-coordinate slab decomposition: cutting off the `k`-th slab of width
`m` and applying the inductive hypothesis to the remaining slabs. -/
theorem boxFun_le_sum_slabs_succ {d : ℕ} {f : Finset (Site d) → Ω → ℝ}
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (m : ℕ) (i : Fin d) (a : Site d) (ω : Ω) (k : ℕ)
    (ih : ∀ b : Site d, b i = a i + (k : ℤ) * m - 1 →
      f (latticeBox a b) ω ≤ ∑ j ∈ Finset.range k,
        f (latticeBox (Function.update a i (a i + (m : ℤ) * j))
          (Function.update b i (a i + (m : ℤ) * j + m - 1))) ω)
    (b : Site d) (hb : b i = a i + ((k + 1 : ℕ) : ℤ) * m - 1) :
    f (latticeBox a b) ω ≤ ∑ j ∈ Finset.range (k + 1),
        f (latticeBox (Function.update a i (a i + (m : ℤ) * j))
          (Function.update b i (a i + (m : ℤ) * j + m - 1))) ω := by
  have hs := isBoxSplit_latticeBox_update_of_mem a b i (a i + (m : ℤ) * k) (le_add_of_nonneg_right
      (by
      positivity))
    (by rw [hb]; push_cast; nlinarith)
  have h1 := hsub _ _ _ ω hs
  have h2 := ih (Function.update b i (a i + (m : ℤ) * k - 1)) (by rw [Function.update_self]; ring)
  simp only [Function.update_idem] at h2
  have e : a i + (m : ℤ) * k + m - 1 = b i := by rw [hb]; push_cast; ring
  rw [Finset.sum_range_succ, e, Function.update_eq_self]
  linarith

omit [MeasurableSpace Ω] in
/-- Splitting a box along one coordinate into `k` consecutive slabs of width `m` bounds `f` of the
whole box by the sum of `f` over the slabs. -/
theorem boxFun_le_sum_slabs {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (m : ℕ) (i : Fin d) (a : Site d) (ω : Ω) :
    ∀ (k : ℕ) (b : Site d), b i = a i + (k : ℤ) * m - 1 →
      f (latticeBox a b) ω ≤ ∑ j ∈ Finset.range k,
        f (latticeBox (Function.update a i (a i + (m : ℤ) * j))
          (Function.update b i (a i + (m : ℤ) * j + m - 1))) ω := by
  intro k
  induction k with
  | zero =>
    intro b hb
    rw [Finset.sum_range_zero, boxFun_eq_zero_of_lt_apply hC (i := i) (by simp at hb; omega) ω]
  | succ k ih =>
    intro b hb
    exact boxFun_le_sum_slabs_succ hsub m i a ω k ih b hb

/-- The partial grid over the empty coordinate set is the single point `0`. -/
theorem gridSet_empty (d n : ℕ) : gridSet d ∅ n = {0} := by
  rw [gridSet]
  simp only [Finset.notMem_empty, if_false]
  exact Fintype.piFinset_singleton 0


/-- A coordinate outside `s` vanishes on every point of the partial grid `gridSet d s n`. -/
theorem gridSet_apply_eq_zero_of_notMem {d : ℕ} {s : Finset (Fin d)} {n : ℕ} {w : Fin d → ℕ}
    {i : Fin d}
    (hw : w ∈ gridSet d s n) (hi : i ∉ s) : w i = 0 := by
  simp only [gridSet, Fintype.mem_piFinset] at hw
  have h := hw i
  rw [if_neg hi, Finset.mem_singleton] at h
  exact h


/-- Updating coordinate `i` of a grid point in `gridSet d s n` to a value `j` lands in `gridSet d
(insert i s) n` iff `j < n`. -/
theorem update_mem_gridSet_insert_iff {d : ℕ} {s : Finset (Fin d)} {i : Fin d} (_unused_hi :
    i ∉ s) (n : ℕ)
    (w : Fin d → ℕ) (j : ℕ) (hw : w ∈ gridSet d s n) :
    Function.update w i j ∈ gridSet d (insert i s) n ↔ j ∈ Finset.range n := by
  unfold gridSet at hw ⊢
  rw [Fintype.mem_piFinset] at hw ⊢
  constructor
  · intro h
    have := h i
    rw [Function.update_self, if_pos (Finset.mem_insert_self i s)] at this
    exact this
  · intro hj a
    by_cases ha : a = i
    · rw [ha, Function.update_self, if_pos (Finset.mem_insert_self i s)]
      exact hj
    · rw [Function.update_apply, if_neg ha]
      have hwa := hw a
      by_cases has : a ∈ s
      · rw [if_pos has] at hwa
        rw [if_pos (Finset.mem_insert_of_mem has)]
        exact hwa
      · rw [if_neg has] at hwa
        rw [if_neg (fun hmem => by
          rcases Finset.mem_insert.mp hmem with h' | h'
          · exact ha h'
          · exact has h')]
        exact hwa

/-- A point of `gridSet d (insert i s) n` restricts, after zeroing coordinate `i`, to a point of
`gridSet d s n`, with its `i`-th coordinate below `n`. -/
theorem update_zero_mem_gridSet_of_mem_insert {d : ℕ} {s : Finset (Fin d)} {i : Fin d} (hi :
    i ∉ s) (n : ℕ)
    (w : Fin d → ℕ) (hw : w ∈ gridSet d (insert i s) n) :
    Function.update w i 0 ∈ gridSet d s n ∧ w i ∈ Finset.range n := by
  unfold gridSet at hw ⊢
  rw [Fintype.mem_piFinset] at hw ⊢
  refine ⟨?_, ?_⟩
  · intro a
    by_cases ha : a = i
    · rw [ha, Function.update_self, if_neg hi]
      exact Finset.mem_singleton.mpr rfl
    · rw [Function.update_apply, if_neg ha]
      have hwa := hw a
      by_cases has : a ∈ s
      · rw [if_pos has]
        rw [if_pos (Finset.mem_insert_of_mem has)] at hwa
        exact hwa
      · rw [if_neg has]
        have hni : ¬ a ∈ insert i s := fun hmem => by
          rcases Finset.mem_insert.mp hmem with h' | h'
          · exact ha h'
          · exact has h'
        rw [if_neg hni] at hwa
        rw [Finset.mem_singleton] at hwa ⊢
        exact hwa
  · have := hw i
    rw [if_pos (Finset.mem_insert_self i s)] at this
    exact this

/-- A sum over the grid `gridSet d (insert i s) n` splits as a sum over `gridSet d s n` of sums over
the `n` values of the new coordinate `i`. -/
theorem sum_gridSet_insert {d : ℕ} {M : Type*} [AddCommMonoid M] (s : Finset (Fin d)) (i :
    Fin d)
    (hi : i ∉ s) (n : ℕ) (g : (Fin d → ℕ) → M) :
    ∑ w ∈ gridSet d (insert i s) n, g w =
      ∑ w ∈ gridSet d s n, ∑ j ∈ Finset.range n, g (Function.update w i j) := by
  rw [← Finset.sum_product (gridSet d s n) (Finset.range n)
        (fun p : (Fin d → ℕ) × ℕ => g (Function.update p.1 i p.2))]
  refine Finset.sum_nbij' (s := gridSet d (insert i s) n)
    (t := gridSet d s n ×ˢ Finset.range n) (f := g)
    (g := fun p : (Fin d → ℕ) × ℕ => g (Function.update p.1 i p.2))
    (i := fun w : Fin d → ℕ => (Function.update w i 0, w i))
    (j := fun p : (Fin d → ℕ) × ℕ => Function.update p.1 i p.2) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_product]
    exact update_zero_mem_gridSet_of_mem_insert hi n w hw
  · intro p hp
    rw [Finset.mem_product] at hp
    exact (update_mem_gridSet_insert_iff hi n p.1 p.2 hp.1).mpr hp.2
  · intro w hw
    rw [Function.update_idem, Function.update_eq_self]
  · intro p hp
    rw [Finset.mem_product] at hp
    have h0 : p.1 i = 0 := gridSet_apply_eq_zero_of_notMem hp.1 hi
    apply Prod.ext
    · rw [Function.update_idem, ← h0, Function.update_eq_self]
    · rw [Function.update_self]
  · intro w hw
    rw [Function.update_idem, Function.update_eq_self]


/-- Updating the lower and upper corner descriptions of `gridBox` at coordinate `i` to slide by `j`
slabs identifies the result with `gridBox` over `insert i s` at the updated grid point. -/
theorem gridBox_update_eq_gridBox_insert {d : ℕ} (m k : ℕ) (s : Finset (Fin d)) (i : Fin d)
    (hi : i ∉ s)
    (w : Fin d → ℕ) (hwi : w i = 0) (j : ℕ) :
    latticeBox (Function.update (fun l => (m : ℤ) * (w l : ℤ)) i
        ((fun l => (m : ℤ) * (w l : ℤ)) i + (m : ℤ) * (j : ℤ)))
      (Function.update (fun l => (m : ℤ) * (w l : ℤ) +
        (if l ∈ s then (m : ℤ) else (k : ℤ) * m) - 1) i
        ((fun l => (m : ℤ) * (w l : ℤ)) i + (m : ℤ) * (j : ℤ) + m - 1))
      = gridBox m k (insert i s) (Function.update w i j) := by
  simp only [gridBox, latticeBox]
  congr 1
  · funext l
    simp only [Function.update_apply]
    by_cases hl : l = i
    · subst hl
      simp [hwi]
    · simp [hl]
  · funext l
    simp only [Function.update_apply]
    by_cases hl : l = i
    · subst hl
      simp [hwi, Finset.mem_insert, hi]
    · simp [hl, Finset.mem_insert]

omit [MeasurableSpace Ω] in
/-- `f` of the grid box at `w` is at most the sum of `f` of the `k` grid boxes obtained by refining
coordinate `i` at `w`. -/
theorem boxFun_gridBox_le_sum_gridBox_insert {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (m k : ℕ) (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) (w : Fin d → ℕ)
    (hw : w ∈ gridSet d s k) (ω : Ω) :
    f (gridBox m k s w) ω ≤
      ∑ j ∈ Finset.range k, f (gridBox m k (insert i s) (Function.update w i j)) ω := by
  have hwi : w i = 0 := gridSet_apply_eq_zero_of_notMem hw hi
  have h13 := boxFun_le_sum_slabs hC hsub m i (fun l => (m : ℤ) * (w l : ℤ)) ω k
    (fun l => (m : ℤ) * (w l : ℤ) + (if l ∈ s then (m : ℤ) else (k : ℤ) * m) - 1)
    (by simp [hi])
  refine h13.trans ?_
  apply Finset.sum_le_sum
  intro j hj
  rw [gridBox_update_eq_gridBox_insert m k s i hi w hwi j]


/-- The grid box over the empty coordinate set at the origin is the cube of side `k * m`. -/
theorem gridBox_empty_eq_latticeCube {d : ℕ} (m k : ℕ) : gridBox m k (∅ : Finset (Fin d)) (0
    : Fin d → ℕ) = latticeCube d (k * m) := by
  unfold gridBox latticeCube latticeBox
  have h1 : (fun i : Fin d => (m : ℤ) * ((0 : Fin d → ℕ) i)) = (0 : Site d) := by
    funext i; simp
  have h2 : (fun i : Fin d => (m : ℤ) * ((0 : Fin d → ℕ) i) + (if i ∈ (∅ : Finset (Fin d)) then (m :
      ℤ) else (k : ℤ) * m) - 1)
      = (fun _ : Fin d => ((k * m : ℕ) : ℤ) - 1) := by
    funext i; simp [Nat.cast_mul]
  rw [h1, h2]

omit [MeasurableSpace Ω] in
/-- `f` of the cube of side `k * m` is at most the sum of `f` over the grid boxes indexed by
`gridSet d s k`, for every coordinate subset `s`. -/
theorem boxFun_cube_le_sum_gridBox {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (m k : ℕ) (ω : Ω) (s : Finset (Fin d)) :
    f (latticeCube d (k * m)) ω ≤ ∑ w ∈ gridSet d s k, f (gridBox m k s w) ω := by
  refine Finset.induction_on s (motive := fun t => f (latticeCube d (k * m)) ω ≤ ∑ w ∈ gridSet d t
      k, f (gridBox m k t w) ω) ?base ?step
  · rw [gridSet_empty, Finset.sum_singleton]
    exact le_of_eq (congrArg (fun A => f A ω) (gridBox_empty_eq_latticeCube m k)).symm
  · intro i t hi ih
    rw [sum_gridSet_insert t i hi k (fun w => f (gridBox m k (insert i t) w) ω)]
    exact le_trans ih (Finset.sum_le_sum (fun w hw => boxFun_gridBox_le_sum_gridBox_insert hC hsub m
        k t i hi w hw ω))


/-- The grid box over all coordinates at grid point `w` is the translate of the cube of side `m` by
`m • natToSite w`. -/
theorem gridBox_univ_eq_map_addRight {d : ℕ} (m k : ℕ) (w : Fin d → ℕ) :
    gridBox m k Finset.univ w =
      (latticeCube d m).map (Equiv.addRight ((m : ℤ) • natToSite w)).toEmbedding := by
  rw [map_addRight_latticeCube_eq_latticeBox]
  unfold gridBox latticeBox
  congr 1
  funext i
  simp [natToSite, Pi.smul_apply]

omit [MeasurableSpace Ω] in
/-- `f` of the cube of side `k * m` is at most the sum, over the full grid of `k ^ d` shifts, of `f`
of the cube of side `m` composed with the action `τ`. -/
theorem boxFun_cube_le_sum_stat {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ} (τ : Site d →
    Ω → Ω)
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    (m k : ℕ) (ω : Ω) :
    f (latticeCube d (k * m)) ω ≤
      ∑ w ∈ gridSet d Finset.univ k, f (latticeCube d m) (τ ((m : ℤ) • natToSite w) ω) := by
  exact le_trans (boxFun_cube_le_sum_gridBox hC hsub m k ω Finset.univ)
    (Finset.sum_le_sum (fun w _ => by rw [gridBox_univ_eq_map_addRight m k w, hstat]))


/-- The cube `latticeCube d n` has `n ^ d` sites. -/
theorem card_latticeCube_eq_pow' (d n : ℕ) : (latticeCube d n).card = n ^ d := by
  rw [latticeCube, Pi.Icc_eq, Fintype.card_piFinset]
  simp

omit [MeasurableSpace Ω] in
/-- The normalised value `cubeRatio f n ω` lies between `0` and the bound constant `C`. -/
theorem cubeRatio_nonneg_le {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (n : ℕ) (ω : Ω) :
    0 ≤ cubeRatio f n ω ∧ cubeRatio f n ω ≤ C := by
  have hcard : (latticeCube d n).card = n ^ d := card_latticeCube_eq_pow' d n
  have hC0 : 0 ≤ C :=
    le_trans (hC ({0} : Finset (Site d)) ω).1 (by simpa using (hC ({0} : Finset (Site d)) ω).2)
  constructor
  · simp only [cubeRatio]
    exact div_nonneg (hC (latticeCube d n) ω).1 (by positivity)
  · simp only [cubeRatio]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]
      simp only [Nat.cast_zero, zero_pow (by omega : d ≠ 0), div_zero]
      exact hC0
    · rw [div_le_iff₀ (pow_pos (Nat.cast_pos.mpr hn) d)]
      have h := (hC (latticeCube d n) ω).2
      rw [hcard] at h
      push_cast at h
      exact h


/-- `cubeRatio f n` is measurable, being `f (latticeCube d n)` divided by a constant. -/
theorem measurable_cubeRatio {d : ℕ} {f : Finset (Site d) → Ω → ℝ} (hmeas : ∀ A, Measurable
    (f A))
    (n : ℕ) : Measurable (cubeRatio f n) := by
  exact (hmeas (latticeCube d n)).div_const _

end LatticeProb
