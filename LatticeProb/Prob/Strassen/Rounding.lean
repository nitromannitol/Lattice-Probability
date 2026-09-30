import Mathlib

/-!
# B. Rounding real weights to denominator `D`

Rounds a probability weight `a : P → ℝ` on a bounded poset `P` to an integer weight with total
mass `D`: `roundLow` rounds every coordinate down (`⌊D * a⌋₊`) except `⊥`, which absorbs the
rounding excess, and `roundHigh` does the same rounding up off `⊤`. This preserves up-set
domination exactly (rounding down never raises the mass of an upper set, rounding up never lowers
it) and both approximate `D * ∑_E a` to within `card P` on every finset `E`
(`abs_sum_roundLow_and_roundHigh_sub_mul_sum_le_card`).
-/

open MeasureTheory Filter Topology

namespace LatticeProb

namespace StrassenAux

attribute [local instance 10] Classical.propDecidable

/-- Round down off `⊥`, give the remainder to `⊥` (keeps up-set masses from growing). -/
noncomputable def roundLow {P : Type*} [Fintype P] [PartialOrder P] [OrderBot P]
    (a : P → ℝ) (D : ℕ) (y : P) : ℕ :=
  if y = ⊥ then D - ∑ z ∈ Finset.univ.erase ⊥, ⌊(D : ℝ) * a z⌋₊ else ⌊(D : ℝ) * a y⌋₊

/-- Round down off `⊤`, give the remainder to `⊤` (keeps up-set masses from shrinking). -/
noncomputable def roundHigh {P : Type*} [Fintype P] [PartialOrder P] [OrderTop P]
    (b : P → ℝ) (D : ℕ) (x : P) : ℕ :=
  if x = ⊤ then D - ∑ z ∈ Finset.univ.erase ⊤, ⌊(D : ℝ) * b z⌋₊ else ⌊(D : ℝ) * b x⌋₊

/-- Two-sided bound on `∑ ⌊D * a⌋₊` in terms of `D * ∑ a`, up to an error of at most `card s`. -/
private theorem sum_floor_mul_bounds {P : Type*} (a : P → ℝ) (ha : ∀ z, 0 ≤ a z) (D : ℕ)
    (s : Finset P) :
    ((∑ z ∈ s, ⌊(D : ℝ) * a z⌋₊ : ℕ) : ℝ) ≤ D * ∑ z ∈ s, a z ∧
      (D : ℝ) * ∑ z ∈ s, a z - s.card ≤ ((∑ z ∈ s, ⌊(D : ℝ) * a z⌋₊ : ℕ) : ℝ) := by
  constructor
  · rw [Nat.cast_sum, Finset.mul_sum]; exact Finset.sum_le_sum
      (fun z _ => Nat.floor_le (mul_nonneg (Nat.cast_nonneg D) (ha z)))
  · rw [Nat.cast_sum, Finset.mul_sum,
      show (s.card : ℝ) = ∑ _z ∈ s, (1 : ℝ) by rw [Finset.sum_const, nsmul_eq_mul, mul_one],
      ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun z _ => by
      have hlt := Nat.lt_floor_add_one ((D : ℝ) * a z)
      linarith)


/-- `∑ ⌊D * a⌋₊ ≤ D` when `a` is a nonnegative probability weight. -/
private theorem sum_floor_mul_le {P : Type*} [Fintype P] (a : P → ℝ) (ha : ∀ z, 0 ≤ a z)
    (ha1 : ∑ z, a z = 1) (D : ℕ) (s : Finset P) :
    ∑ z ∈ s, ⌊(D : ℝ) * a z⌋₊ ≤ D := by
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have h2 : (∑ z ∈ s, a z) ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun i _ _ => ha i)).trans (le_of_eq ha1)
  refine (Nat.cast_le (α := ℝ)).mp ?_
  exact (Nat.cast_sum s (fun z => ⌊(D : ℝ) * a z⌋₊)).trans_le
    (((Finset.sum_le_sum (fun z _ => Nat.floor_le (mul_nonneg hD0 (ha z)))).trans
      (le_of_eq (Finset.mul_sum s a (D : ℝ)).symm)).trans
      ((mul_le_mul_of_nonneg_left h2 hD0).trans (le_of_eq (mul_one (D : ℝ)))))


/-- If `r` agrees with `⌊D * a⌋₊` off a point `p`, and `p ∉ E`, then `|∑_E r - D * ∑_E a| ≤ card P`.
-/
private theorem abs_sum_round_sub_mul_sum_le_card_of_notMem {P : Type*} [Fintype P] (a : P → ℝ)
    (ha : ∀ z, 0 ≤ a z)
    (D : ℕ) (r : P → ℕ) (p : P) (hr : ∀ z, z ≠ p → r z = ⌊(D : ℝ) * a z⌋₊)
    (E : Finset P) (hpE : p ∉ E) :
    |((∑ z ∈ E, r z : ℕ) : ℝ) - D * ∑ z ∈ E, a z| ≤ Fintype.card P := by
  have hlow : ∀ z ∈ E, (-1:ℝ) ≤ (r z : ℝ) - (D:ℝ) * a z := fun z hz => by
    have hzr : r z = ⌊(D:ℝ) * a z⌋₊ := hr z (fun h => hpE (h ▸ hz))
    rw [hzr]
    have hlt := Nat.lt_floor_add_one ((D:ℝ) * a z)
    linarith
  have hhigh : ∀ z ∈ E, (r z : ℝ) - (D:ℝ) * a z ≤ 1 := fun z hz => by
    have hzr : r z = ⌊(D:ℝ) * a z⌋₊ := hr z (fun h => hpE (h ▸ hz))
    rw [hzr]
    have hle := Nat.floor_le (show (0:ℝ) ≤ (D:ℝ) * a z by
      exact mul_nonneg (Nat.cast_nonneg D) (ha z))
    linarith
  have habs : ∀ z ∈ E, |(r z : ℝ) - (D:ℝ) * a z| ≤ (1:ℝ) :=
    fun z hz => abs_le.mpr ⟨hlow z hz, hhigh z hz⟩
  have h1 : |∑ z ∈ E, ((r z : ℝ) - (D:ℝ) * a z)| ≤ ∑ z ∈ E, (1:ℝ) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum habs)
  have h2 : (∑ z ∈ E, (1:ℝ)) = (E.card : ℝ) := by simp
  have h3 : (E.card : ℝ) ≤ (Fintype.card P : ℝ) := by exact_mod_cast Finset.card_le_univ E
  rw [Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  linarith


/-- If `r` agrees with `⌊D * a⌋₊` off a point `p`, sums to `D`, and `a` is a probability weight,
then `|∑_E r - D * ∑_E a| ≤ card P` for every `E`. -/
private theorem abs_sum_round_sub_mul_sum_le_card {P : Type*} [Fintype P] (a : P → ℝ)
    (ha : ∀ z, 0 ≤ a z)
    (ha1 : ∑ z, a z = 1) (D : ℕ) (r : P → ℕ) (hrD : ∑ z, r z = D) (p : P)
    (hr : ∀ z, z ≠ p → r z = ⌊(D : ℝ) * a z⌋₊) (E : Finset P) :
    |((∑ z ∈ E, r z : ℕ) : ℝ) - D * ∑ z ∈ E, a z| ≤ Fintype.card P := by
  classical
  have hmain : ∀ T : Finset P, p ∉ T → |((∑ z ∈ T, r z : ℕ) : ℝ) - (D : ℝ) * ∑ z ∈ T, a z| ≤
      (Fintype.card P : ℝ) := fun T hT => abs_sum_round_sub_mul_sum_le_card_of_notMem a ha D r p hr
          T hT
  by_cases hpE : p ∈ E
  · have hT : p ∉ Eᶜ := (Finset.notMem_compl).mpr hpE
    have h16 := hmain Eᶜ hT
    have hsum : ((∑ z ∈ E, r z : ℕ) : ℝ) + ((∑ z ∈ Eᶜ, r z : ℕ) : ℝ) = (D : ℝ) :=
        (by exact_mod_cast (Finset.sum_add_sum_compl E r).trans (by rw [hrD]))
    have ha0 : (∑ z ∈ E, a z) + (∑ z ∈ Eᶜ, a z) = 1 := (Finset.sum_add_sum_compl E a).trans
        (by rw [ha1])
    have hU : ((∑ z ∈ Eᶜ, r z : ℕ) : ℝ) = (D : ℝ) - ((∑ z ∈ E, r z : ℕ) : ℝ) := (by linarith)
    have hV : ∑ z ∈ Eᶜ, a z = 1 - ∑ z ∈ E, a z := (by linarith)
    have key : ((∑ z ∈ E, r z : ℕ) : ℝ) - (D : ℝ) * ∑ z ∈ E, a z =
        -(((∑ z ∈ Eᶜ, r z : ℕ) : ℝ) - (D : ℝ) * ∑ z ∈ Eᶜ, a z) := (by rw [hU, hV]; ring)
    rw [key, abs_neg]
    exact h16
  · exact hmain E hpE


/-- `∑ y, roundLow a D y = D`. -/
theorem sum_roundLow_eq {P : Type*} [Fintype P] [PartialOrder P] [OrderBot P] (a : P → ℝ)
    (ha : ∀ z, 0 ≤ a z) (ha1 : ∑ z, a z = 1) (D : ℕ) : ∑ y, roundLow a D y = D := by
  have h1 : roundLow a D (⊥ : P) = D - ∑ z ∈ Finset.univ.erase (⊥ : P), ⌊(D : ℝ) * a z⌋₊ :=
      (by simp [roundLow])
  have h2 : ∑ y ∈ Finset.univ.erase (⊥ : P), roundLow a D y = ∑ y ∈ Finset.univ.erase (⊥ : P),
      ⌊(D : ℝ) * a y⌋₊ := (by
    apply Finset.sum_congr rfl
    intro y hy
    simp only [roundLow, if_neg (Finset.ne_of_mem_erase hy)])
  rw [← Finset.add_sum_erase (Finset.univ : Finset P) (fun y => roundLow a D y)
      (Finset.mem_univ (⊥ : P))]
  rw [h1, h2]
  exact Nat.sub_add_cancel (sum_floor_mul_le a ha ha1 D _)


/-- `∑ x, roundHigh b D x = D`. -/
theorem sum_roundHigh_eq {P : Type*} [Fintype P] [PartialOrder P] [OrderTop P] (b : P → ℝ)
    (hb : ∀ z, 0 ≤ b z) (hb1 : ∑ z, b z = 1) (D : ℕ) : ∑ x, roundHigh b D x = D := by
  have hsplit := Finset.add_sum_erase (s := (Finset.univ : Finset P)) (f := roundHigh b D)
    (a := ⊤) (Finset.mem_univ _)
  have htop : roundHigh b D (⊤ : P) = D - ∑ x ∈ (Finset.univ.erase (⊤ : P)), ⌊(D : ℝ) * b x⌋₊ :=
    if_pos rfl
  have hoff : ∀ x ∈ (Finset.univ.erase (⊤ : P)),
      roundHigh b D x = ⌊(D : ℝ) * b x⌋₊ :=
    fun x hx => if_neg (Finset.ne_of_mem_erase hx)
  have hsum_off : ∑ x ∈ (Finset.univ.erase (⊤ : P)), roundHigh b D x
      = ∑ x ∈ (Finset.univ.erase (⊤ : P)), ⌊(D : ℝ) * b x⌋₊ :=
    Finset.sum_congr rfl hoff
  have hle : ∑ x ∈ (Finset.univ.erase (⊤ : P)), ⌊(D : ℝ) * b x⌋₊ ≤ D :=
    sum_floor_mul_le b hb hb1 D (Finset.univ.erase (⊤ : P))
  rw [← hsplit, htop, hsum_off, Nat.sub_add_cancel hle]


/-- An upper set containing `⊥` is everything. -/
private theorem eq_univ_of_isUpperSet_of_bot_mem {P : Type*} [Fintype P] [PartialOrder P]
    [OrderBot P] (U : Finset P)
    (hU : IsUpperSet (U : Set P)) (h : ⊥ ∈ U) : U = Finset.univ := by
  ext z
  simp only [Finset.mem_univ, iff_true]
  exact hU bot_le h


/-- A nonempty upper set contains `⊤`. -/
private theorem top_mem_of_isUpperSet_of_nonempty {P : Type*} [Fintype P] [PartialOrder P]
    [OrderTop P] (U : Finset P)
    (hU : IsUpperSet (U : Set P)) (h : U.Nonempty) : ⊤ ∈ U := by
  obtain ⟨y, hy⟩ := h
  exact hU le_top hy


/-- Rounding down never raises the mass of an upper set: `∑_U roundLow a D ≤ D * ∑_U a`. -/
theorem sum_roundLow_le_mul_sum_of_isUpperSet {P : Type*} [Fintype P] [PartialOrder P]
    [OrderBot P] (a : P → ℝ)
    (ha : ∀ z, 0 ≤ a z) (ha1 : ∑ z, a z = 1) (D : ℕ) (U : Finset P)
    (hU : IsUpperSet (U : Set P)) :
    ((∑ y ∈ U, roundLow a D y : ℕ) : ℝ) ≤ D * ∑ y ∈ U, a y := by
  exact if hbot : (⊥ : P) ∈ U then
      (by
        rw [eq_univ_of_isUpperSet_of_bot_mem U hU hbot]
        rw [sum_roundLow_eq a ha ha1 D]
        simp [ha1])
      else (by
        have hsum : ∑ y ∈ U, roundLow a D y = ∑ y ∈ U, ⌊(D:ℝ) * a y⌋₊ :=
          Finset.sum_congr rfl
            (fun y hy => by
              simp only [roundLow, if_neg (show ¬(y = ⊥) from fun h => hbot (h ▸ hy))])
        rw [hsum]
        exact (sum_floor_mul_bounds a ha D U).1)


/-- Rounding up never lowers the mass of an upper set: `D * ∑_U b ≤ ∑_U roundHigh b D`. -/
theorem mul_sum_le_sum_roundHigh_of_isUpperSet {P : Type*} [Fintype P] [PartialOrder P]
    [OrderTop P] (b : P → ℝ)
    (hb : ∀ z, 0 ≤ b z) (hb1 : ∑ z, b z = 1) (D : ℕ) (U : Finset P)
    (hU : IsUpperSet (U : Set P)) :
    (D : ℝ) * ∑ x ∈ U, b x ≤ ((∑ x ∈ U, roundHigh b D x : ℕ) : ℝ) := by
  classical
  by_cases hUne : U.Nonempty
  · have htop : ⊤ ∈ U := top_mem_of_isUpperSet_of_nonempty U hU hUne
    have hcompl : ∀ x : P, x ∉ U → roundHigh b D x = ⌊(D : ℝ) * b x⌋₊ := by
      intro x hxU
      have hxne : x ≠ ⊤ := fun h => hxU (h.symm ▸ htop)
      rw [roundHigh, if_neg hxne]
    have hCeq : (∑ x ∈ Uᶜ, roundHigh b D x) = ∑ x ∈ Uᶜ, ⌊(D : ℝ) * b x⌋₊ := by
      exact Finset.sum_congr rfl (fun x hx => hcompl x (Finset.mem_compl.mp hx))
    have hC : ((∑ x ∈ Uᶜ, roundHigh b D x : ℕ) : ℝ) ≤ (D : ℝ) * ∑ x ∈ Uᶜ, b x := by
      rw [hCeq]
      exact (sum_floor_mul_bounds b hb D Uᶜ).1
    have hsum_all : (∑ x, roundHigh b D x) = D := sum_roundHigh_eq b hb hb1 D
    have h1 : ((∑ x ∈ U, roundHigh b D x : ℕ) : ℝ)
        + ((∑ x ∈ Uᶜ, roundHigh b D x : ℕ) : ℝ) = (D : ℝ) := by
      rw [← Nat.cast_add, Finset.sum_add_sum_compl U (roundHigh b D), hsum_all]
    have h3 : ∑ x ∈ U, b x + ∑ x ∈ Uᶜ, b x = 1 := by
      rw [Finset.sum_add_sum_compl U b, hb1]
    have h4 : (D : ℝ) * ∑ x ∈ U, b x = (D : ℝ) - (D : ℝ) * ∑ x ∈ Uᶜ, b x := by
      have h5 : ∑ x ∈ U, b x = 1 - ∑ x ∈ Uᶜ, b x := by linarith
      rw [h5]; ring
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hUne]
    simp

/-- Restates `mul_sum_le_sum_roundHigh_of_isUpperSet`. -/
theorem mul_sum_le_sum_roundHigh_of_isUpperSet' {P : Type*} [Fintype P] [PartialOrder P]
    [OrderTop P] (b : P → ℝ)
    (hb : ∀ z, 0 ≤ b z) (hb1 : ∑ z, b z = 1) (D : ℕ) (U : Finset P)
    (hU : IsUpperSet (U : Set P)) :
    (D : ℝ) * ∑ x ∈ U, b x ≤ ((∑ x ∈ U, roundHigh b D x : ℕ) : ℝ) := by
  exact mul_sum_le_sum_roundHigh_of_isUpperSet b hb hb1 D U hU


/-- Both `roundLow` and `roundHigh` approximate `D * ∑_E a` to within `card P`, on every finset `E`.
-/
theorem abs_sum_roundLow_and_roundHigh_sub_mul_sum_le_card {P : Type*} [Fintype P]
    [PartialOrder P] [BoundedOrder P]
    (a : P → ℝ) (ha : ∀ z, 0 ≤ a z) (ha1 : ∑ z, a z = 1) (D : ℕ) (E : Finset P) :
    |((∑ z ∈ E, roundLow a D z : ℕ) : ℝ) - D * ∑ z ∈ E, a z| ≤ Fintype.card P ∧
      |((∑ z ∈ E, roundHigh a D z : ℕ) : ℝ) - D * ∑ z ∈ E, a z| ≤ Fintype.card P := by
  constructor
  · exact abs_sum_round_sub_mul_sum_le_card a ha ha1 D (roundLow a D) (sum_roundLow_eq a ha ha1 D) ⊥
      (fun z hz => by simp only [roundLow]; exact if_neg hz) E
  · exact abs_sum_round_sub_mul_sum_le_card a ha ha1 D (roundHigh a D)
      (sum_roundHigh_eq a ha ha1 D) ⊤
      (fun z hz => by simp only [roundHigh]; exact if_neg hz) E

end StrassenAux

end LatticeProb
