/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5XAdj at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XCell
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XRing

/-!
# DZZ Lemma 3.5: neighbouring cells contain adjacent grid squares (P2-DEC84, D84)

For the crossing argument on the level-`N` grid (decision D84, DEC-84 §4) the `δ`-geodesic
`𝖢_1, …, 𝖢_d` of DZZ l. 1067 is turned into a 4-path of squares. This file:

* `anc_eq_of_sub`: a level-`N` square inside a box of level `≤ N` has that box as ancestor.
* `eq_of_sub_cell`: a cell whose closure lies in the closure of another cell is that cell.
* `dy_nested`: dyadic intervals whose interiors meet are nested.
* **`exists_sqAdj_of_neighbour`**: two neighbouring cells (levels `≤ N`) contain 4-adjacent
  level-`N` squares.

Own elementary arguments; DEVIATIONS DV-D84.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma anc_eq_of_sub {s B : DyBox} {N : ℕ} (hs : s.n = N) (hB : B.n ≤ N)
    (h : s.closedBox ⊆ B.closedBox) : s.anc B.n = B := by
  obtain ⟨c1, c2, c3, c4⟩ := int_of_sub_closedBox hs hB h
  have hp : 0 < 2 ^ (N - B.n) := by positivity
  ext
  · show min B.n s.n = B.n; omega
  · show s.j / 2 ^ (s.n - B.n) = B.j
    rw [hs]; exact Nat.div_eq_of_lt_le (by linarith) (by linarith)
  · show s.k / 2 ^ (s.n - B.n) = B.k
    rw [hs]; exact Nat.div_eq_of_lt_le (by linarith) (by linarith)

/-- The level-`N` corner square of a box of level `≤ N`. -/
def cornerSq (N : ℕ) (B : DyBox) (hB : B.n ≤ N) : DyBox :=
  ⟨N, B.j * 2 ^ (N - B.n), B.k * 2 ^ (N - B.n),
    by
      have := B.hj
      calc B.j * 2 ^ (N - B.n) < 2 ^ B.n * 2 ^ (N - B.n) :=
            Nat.mul_lt_mul_of_pos_right this (by positivity)
        _ = 2 ^ N := by rw [← pow_add]; congr 1; omega,
    by
      have := B.hk
      calc B.k * 2 ^ (N - B.n) < 2 ^ B.n * 2 ^ (N - B.n) :=
            Nat.mul_lt_mul_of_pos_right this (by positivity)
        _ = 2 ^ N := by rw [← pow_add]; congr 1; omega⟩

lemma cornerSq_sub {N : ℕ} (B : DyBox) (hB : B.n ≤ N) :
    (cornerSq N B hB).closedBox ⊆ B.closedBox := by
  have hp : 0 < 2 ^ (N - B.n) := by positivity
  refine bx_sub_closedBox rfl hB ?_ ?_ ?_ ?_ <;> simp only [cornerSq] <;> push_cast <;> nlinarith

/-- A cell whose closure lies in the closure of another cell is that cell. -/
lemma eq_of_sub_cell {C C' : DyBox} {N : ℕ} (hC : IsCell m δ C) (hC' : IsCell m δ C')
    (hn : C.n ≤ N) (hn' : C'.n ≤ N) (h : C.closedBox ⊆ C'.closedBox) : C = C' := by
  set s := cornerSq N C hn
  have hs := cornerSq_sub C hn
  have e1 : s.anc C.n = C := anc_eq_of_sub rfl hn hs
  have e2 : s.anc C'.n = C' := anc_eq_of_sub rfl hn' (hs.trans h)
  exact isSqCell_unique ⟨hC, hn, e1⟩ ⟨hC', hn', e2⟩

/-- Dyadic intervals whose interiors meet are nested. -/
lemma dy_nested {a a' e e' : ℕ} (he : e ≤ e') (h1 : a * 2 ^ e < (a' + 1) * 2 ^ e')
    (h2 : a' * 2 ^ e' < (a + 1) * 2 ^ e) :
    a' * 2 ^ e' ≤ a * 2 ^ e ∧ (a + 1) * 2 ^ e ≤ (a' + 1) * 2 ^ e' := by
  have hK : 2 ^ e' = 2 ^ (e' - e) * 2 ^ e := by rw [← pow_add]; congr 1; omega
  have hp : 0 < 2 ^ e := by positivity
  rw [hK, ← mul_assoc] at h1 h2
  have i1 := Nat.lt_of_mul_lt_mul_right h1
  have i2 := Nat.lt_of_mul_lt_mul_right h2
  rw [hK]
  refine ⟨?_, ?_⟩
  · calc a' * (2 ^ (e' - e) * 2 ^ e) = (a' * 2 ^ (e' - e)) * 2 ^ e := by ring
      _ ≤ a * 2 ^ e := Nat.mul_le_mul_right _ (by omega)
  · calc (a + 1) * 2 ^ e ≤ ((a' + 1) * 2 ^ (e' - e)) * 2 ^ e := Nat.mul_le_mul_right _ (by omega)
      _ = (a' + 1) * (2 ^ (e' - e) * 2 ^ e) := by ring

lemma succ_mul_le_two_pow {N i n : ℕ} (hn : n ≤ N) (hi : i < 2 ^ n) :
    (i + 1) * 2 ^ (N - n) ≤ 2 ^ N := by
  calc (i + 1) * 2 ^ (N - n) ≤ 2 ^ n * 2 ^ (N - n) := Nat.mul_le_mul_right _ hi
    _ = 2 ^ N := by rw [← pow_add]; congr 1; omega

lemma scaled_eq {z z' : ℂ} {N : ℕ} (h1 : z.re * 2 ^ N = z'.re * 2 ^ N)
    (h2 : z.im * 2 ^ N = z'.im * 2 ^ N) : z = z' := by
  have hp : (2 : ℝ) ^ N ≠ 0 := by positivity
  exact Complex.ext (mul_right_cancel₀ hp h1) (mul_right_cancel₀ hp h2)

/-- Horizontal contact: `C` to the left of `C'` along a vertical line. -/
lemma adj_case_j {C C' : DyBox} {N : ℕ} (hn : C.n ≤ N) (hn' : C'.n ≤ N)
    (hA : (C.j + 1) * 2 ^ (N - C.n) = C'.j * 2 ^ (N - C'.n)) {z z' : ℂ}
    (hz : z ∈ C.closedBox ∩ C'.closedBox) (hz' : z' ∈ C.closedBox ∩ C'.closedBox) (hne : z ≠ z') :
    ∃ s s' : DyBox, s.n = N ∧ s.closedBox ⊆ C.closedBox ∧ s'.closedBox ⊆ C'.closedBox ∧
      SqAdj s s' := by
  obtain ⟨a1, a2, a3, a4⟩ := (bx_mem_closedBox hn).1 hz.1
  obtain ⟨b1, b2, b3, b4⟩ := (bx_mem_closedBox hn').1 hz.2
  obtain ⟨c1, c2, c3, c4⟩ := (bx_mem_closedBox hn).1 hz'.1
  obtain ⟨d1, d2, d3, d4⟩ := (bx_mem_closedBox hn').1 hz'.2
  have hw : 0 < 2 ^ (N - C.n) := by positivity
  have hw' : 0 < 2 ^ (N - C'.n) := by positivity
  have hA' : ((C.j + 1) * 2 ^ (N - C.n) : ℕ) = ((C'.j * 2 ^ (N - C'.n) : ℕ) : ℝ) := by
    exact_mod_cast hA
  set q := max (C.k * 2 ^ (N - C.n)) (C'.k * 2 ^ (N - C'.n)) with hq
  have hq1 : q + 1 ≤ (C.k + 1) * 2 ^ (N - C.n) ∧ q + 1 ≤ (C'.k + 1) * 2 ^ (N - C'.n) := by
    by_contra hcon
    have l1 : C.k * 2 ^ (N - C.n) ≤ (C'.k + 1) * 2 ^ (N - C'.n) := by
      have : ((C.k * 2 ^ (N - C.n) : ℕ) : ℝ) ≤ (((C'.k + 1) * 2 ^ (N - C'.n) : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have l2 : C'.k * 2 ^ (N - C'.n) ≤ (C.k + 1) * 2 ^ (N - C.n) := by
      have : ((C'.k * 2 ^ (N - C'.n) : ℕ) : ℝ) ≤ (((C.k + 1) * 2 ^ (N - C.n) : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hk1 : C.k * 2 ^ (N - C.n) < (C.k + 1) * 2 ^ (N - C.n) := by nlinarith
    have hk2 : C'.k * 2 ^ (N - C'.n) < (C'.k + 1) * 2 ^ (N - C'.n) := by nlinarith
    -- the vertical overlap is a single value `Y`
    have hY : ∃ Y : ℕ, (C.k * 2 ^ (N - C.n) = Y ∧ (C'.k + 1) * 2 ^ (N - C'.n) = Y) ∨
        (C'.k * 2 ^ (N - C'.n) = Y ∧ (C.k + 1) * 2 ^ (N - C.n) = Y) := by
      rcases le_total (C.k * 2 ^ (N - C.n)) (C'.k * 2 ^ (N - C'.n)) with h | h
      · rw [max_eq_right h] at hq
        exact ⟨_, Or.inr ⟨rfl, by omega⟩⟩
      · rw [max_eq_left h] at hq
        exact ⟨_, Or.inl ⟨rfl, by omega⟩⟩
    obtain ⟨Y, hY⟩ := hY
    apply hne
    apply scaled_eq (N := N)
    · have e1 : z.re * 2 ^ N = ((C'.j * 2 ^ (N - C'.n) : ℕ) : ℝ) := le_antisymm (hA' ▸ a2) b1
      have e2 : z'.re * 2 ^ N = ((C'.j * 2 ^ (N - C'.n) : ℕ) : ℝ) := le_antisymm (hA' ▸ c2) d1
      rw [e1, e2]
    · rcases hY with ⟨y1, y2⟩ | ⟨y1, y2⟩
      · have r1 : ((C.k * 2 ^ (N - C.n) : ℕ) : ℝ) = Y := by exact_mod_cast y1
        have r2 : (((C'.k + 1) * 2 ^ (N - C'.n) : ℕ) : ℝ) = Y := by exact_mod_cast y2
        have e1 : z.im * 2 ^ N = Y := le_antisymm (r2 ▸ b4) (r1 ▸ a3)
        have e2 : z'.im * 2 ^ N = Y := le_antisymm (r2 ▸ d4) (r1 ▸ c3)
        rw [e1, e2]
      · have r1 : ((C'.k * 2 ^ (N - C'.n) : ℕ) : ℝ) = Y := by exact_mod_cast y1
        have r2 : (((C.k + 1) * 2 ^ (N - C.n) : ℕ) : ℝ) = Y := by exact_mod_cast y2
        have e1 : z.im * 2 ^ N = Y := le_antisymm (r2 ▸ a4) (r1 ▸ b3)
        have e2 : z'.im * 2 ^ N = Y := le_antisymm (r2 ▸ c4) (r1 ▸ d3)
        rw [e1, e2]
  have hb1 := succ_mul_le_two_pow hn C.hj
  have hb2 := succ_mul_le_two_pow hn' C'.hj
  have hb3 := succ_mul_le_two_pow hn C.hk
  have hA0 : C.j * 2 ^ (N - C.n) + 1 ≤ (C.j + 1) * 2 ^ (N - C.n) := by nlinarith
  have hA0' : C'.j * 2 ^ (N - C'.n) + 1 ≤ (C'.j + 1) * 2 ^ (N - C'.n) := by nlinarith
  have hqN : q < 2 ^ N := lt_of_lt_of_le (Nat.lt_succ_self q) (hq1.1.trans hb3)
  set A1 := (C.j + 1) * 2 ^ (N - C.n) with hA1
  set A0' := C'.j * 2 ^ (N - C'.n) with hA0'def
  let s : DyBox := ⟨N, A1 - 1, q, by omega, hqN⟩
  let s' : DyBox := ⟨N, A0', q, by omega, hqN⟩
  refine ⟨s, s', rfl, ?_, ?_, ⟨rfl, Or.inr ⟨rfl, Or.inl (by simp only [s, s']; omega)⟩⟩⟩
  · refine bx_sub_closedBox rfl hn ?_ ?_ ?_ ?_
    · exact_mod_cast (show C.j * 2 ^ (N - C.n) ≤ A1 - 1 by omega)
    · exact_mod_cast (show A1 - 1 + 1 ≤ A1 by omega)
    · exact_mod_cast le_max_left _ _
    · exact_mod_cast hq1.1
  · refine bx_sub_closedBox rfl hn' ?_ ?_ ?_ ?_
    · exact le_rfl
    · exact_mod_cast hA0'
    · exact_mod_cast le_max_right _ _
    · exact_mod_cast hq1.2

/-- Vertical contact: `C` below `C'` along a horizontal line. -/
lemma adj_case_k {C C' : DyBox} {N : ℕ} (hn : C.n ≤ N) (hn' : C'.n ≤ N)
    (hA : (C.k + 1) * 2 ^ (N - C.n) = C'.k * 2 ^ (N - C'.n)) {z z' : ℂ}
    (hz : z ∈ C.closedBox ∩ C'.closedBox) (hz' : z' ∈ C.closedBox ∩ C'.closedBox) (hne : z ≠ z') :
    ∃ s s' : DyBox, s.n = N ∧ s.closedBox ⊆ C.closedBox ∧ s'.closedBox ⊆ C'.closedBox ∧
      SqAdj s s' := by
  obtain ⟨a1, a2, a3, a4⟩ := (bx_mem_closedBox hn).1 hz.1
  obtain ⟨b1, b2, b3, b4⟩ := (bx_mem_closedBox hn').1 hz.2
  obtain ⟨c1, c2, c3, c4⟩ := (bx_mem_closedBox hn).1 hz'.1
  obtain ⟨d1, d2, d3, d4⟩ := (bx_mem_closedBox hn').1 hz'.2
  have hw : 0 < 2 ^ (N - C.n) := by positivity
  have hw' : 0 < 2 ^ (N - C'.n) := by positivity
  have hA' : ((C.k + 1) * 2 ^ (N - C.n) : ℕ) = ((C'.k * 2 ^ (N - C'.n) : ℕ) : ℝ) := by
    exact_mod_cast hA
  set q := max (C.j * 2 ^ (N - C.n)) (C'.j * 2 ^ (N - C'.n)) with hq
  have hq1 : q + 1 ≤ (C.j + 1) * 2 ^ (N - C.n) ∧ q + 1 ≤ (C'.j + 1) * 2 ^ (N - C'.n) := by
    by_contra hcon
    have l1 : C.j * 2 ^ (N - C.n) ≤ (C'.j + 1) * 2 ^ (N - C'.n) := by
      have : ((C.j * 2 ^ (N - C.n) : ℕ) : ℝ) ≤ (((C'.j + 1) * 2 ^ (N - C'.n) : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have l2 : C'.j * 2 ^ (N - C'.n) ≤ (C.j + 1) * 2 ^ (N - C.n) := by
      have : ((C'.j * 2 ^ (N - C'.n) : ℕ) : ℝ) ≤ (((C.j + 1) * 2 ^ (N - C.n) : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hk1 : C.j * 2 ^ (N - C.n) < (C.j + 1) * 2 ^ (N - C.n) := by nlinarith
    have hk2 : C'.j * 2 ^ (N - C'.n) < (C'.j + 1) * 2 ^ (N - C'.n) := by nlinarith
    -- the vertical overlap is a single value `Y`
    have hY : ∃ Y : ℕ, (C.j * 2 ^ (N - C.n) = Y ∧ (C'.j + 1) * 2 ^ (N - C'.n) = Y) ∨
        (C'.j * 2 ^ (N - C'.n) = Y ∧ (C.j + 1) * 2 ^ (N - C.n) = Y) := by
      rcases le_total (C.j * 2 ^ (N - C.n)) (C'.j * 2 ^ (N - C'.n)) with h | h
      · rw [max_eq_right h] at hq
        exact ⟨_, Or.inr ⟨rfl, by omega⟩⟩
      · rw [max_eq_left h] at hq
        exact ⟨_, Or.inl ⟨rfl, by omega⟩⟩
    obtain ⟨Y, hY⟩ := hY
    apply hne
    apply scaled_eq (N := N)
    · rcases hY with ⟨y1, y2⟩ | ⟨y1, y2⟩
      · have r1 : ((C.j * 2 ^ (N - C.n) : ℕ) : ℝ) = Y := by exact_mod_cast y1
        have r2 : (((C'.j + 1) * 2 ^ (N - C'.n) : ℕ) : ℝ) = Y := by exact_mod_cast y2
        have e1 : z.re * 2 ^ N = Y := le_antisymm (r2 ▸ b2) (r1 ▸ a1)
        have e2 : z'.re * 2 ^ N = Y := le_antisymm (r2 ▸ d2) (r1 ▸ c1)
        rw [e1, e2]
      · have r1 : ((C'.j * 2 ^ (N - C'.n) : ℕ) : ℝ) = Y := by exact_mod_cast y1
        have r2 : (((C.j + 1) * 2 ^ (N - C.n) : ℕ) : ℝ) = Y := by exact_mod_cast y2
        have e1 : z.re * 2 ^ N = Y := le_antisymm (r2 ▸ a2) (r1 ▸ b1)
        have e2 : z'.re * 2 ^ N = Y := le_antisymm (r2 ▸ c2) (r1 ▸ d1)
        rw [e1, e2]
    · have e1 : z.im * 2 ^ N = ((C'.k * 2 ^ (N - C'.n) : ℕ) : ℝ) := le_antisymm (hA' ▸ a4) b3
      have e2 : z'.im * 2 ^ N = ((C'.k * 2 ^ (N - C'.n) : ℕ) : ℝ) := le_antisymm (hA' ▸ c4) d3
      rw [e1, e2]
  have hbj := succ_mul_le_two_pow hn C.hj
  have hbk := succ_mul_le_two_pow hn C.hk
  have hbk' := succ_mul_le_two_pow hn' C'.hk
  have hA0 : C.k * 2 ^ (N - C.n) + 1 ≤ (C.k + 1) * 2 ^ (N - C.n) := by nlinarith
  have hA0' : C'.k * 2 ^ (N - C'.n) + 1 ≤ (C'.k + 1) * 2 ^ (N - C'.n) := by nlinarith
  have hqN : q < 2 ^ N := lt_of_lt_of_le (Nat.lt_succ_self q) (hq1.1.trans hbj)
  set A1 := (C.k + 1) * 2 ^ (N - C.n) with hA1
  set A0' := C'.k * 2 ^ (N - C'.n) with hA0'def
  let s : DyBox := ⟨N, q, A1 - 1, hqN, by omega⟩
  let s' : DyBox := ⟨N, q, A0', hqN, by omega⟩
  refine ⟨s, s', rfl, ?_, ?_, ⟨rfl, Or.inl ⟨rfl, Or.inl (by simp only [s, s']; omega)⟩⟩⟩
  · refine bx_sub_closedBox rfl hn ?_ ?_ ?_ ?_
    · exact_mod_cast le_max_left _ _
    · exact_mod_cast hq1.1
    · exact_mod_cast (show C.k * 2 ^ (N - C.n) ≤ A1 - 1 by omega)
    · exact_mod_cast (show A1 - 1 + 1 ≤ A1 by omega)
  · refine bx_sub_closedBox rfl hn' ?_ ?_ ?_ ?_
    · exact_mod_cast le_max_right _ _
    · exact_mod_cast hq1.2
    · exact le_rfl
    · exact_mod_cast hA0'

lemma sub_of_int_le {C C' : DyBox} {N : ℕ} (hn : C.n ≤ N) (hn' : C'.n ≤ N)
    (h1 : C'.j * 2 ^ (N - C'.n) ≤ C.j * 2 ^ (N - C.n))
    (h2 : (C.j + 1) * 2 ^ (N - C.n) ≤ (C'.j + 1) * 2 ^ (N - C'.n))
    (h3 : C'.k * 2 ^ (N - C'.n) ≤ C.k * 2 ^ (N - C.n))
    (h4 : (C.k + 1) * 2 ^ (N - C.n) ≤ (C'.k + 1) * 2 ^ (N - C'.n)) :
    C.closedBox ⊆ C'.closedBox := by
  intro x hx
  obtain ⟨a1, a2, a3, a4⟩ := (bx_mem_closedBox hn).1 hx
  have c1 : ((C'.j * 2 ^ (N - C'.n) : ℕ) : ℝ) ≤ ((C.j * 2 ^ (N - C.n) : ℕ) : ℝ) := by exact_mod_cast h1
  have c2 : (((C.j + 1) * 2 ^ (N - C.n) : ℕ) : ℝ) ≤ (((C'.j + 1) * 2 ^ (N - C'.n) : ℕ) : ℝ) := by
    exact_mod_cast h2
  have c3 : ((C'.k * 2 ^ (N - C'.n) : ℕ) : ℝ) ≤ ((C.k * 2 ^ (N - C.n) : ℕ) : ℝ) := by exact_mod_cast h3
  have c4 : (((C.k + 1) * 2 ^ (N - C.n) : ℕ) : ℝ) ≤ (((C'.k + 1) * 2 ^ (N - C'.n) : ℕ) : ℝ) := by
    exact_mod_cast h4
  exact (bx_mem_closedBox hn').2 ⟨c1.trans a1, a2.trans c2, c3.trans a3, a4.trans c4⟩

/-- Neighbouring non-nested boxes of level `≤ N` contain 4-adjacent level-`N` squares. -/
theorem exists_sqAdj_of_neighbour' {C C' : DyBox} {N : ℕ}
    (hnest : C.closedBox ⊆ C'.closedBox → C = C') (hnest' : C'.closedBox ⊆ C.closedBox → C' = C)
    (hn : C.n ≤ N) (hn' : C'.n ≤ N) (h : Neighbour C C') :
    ∃ s s' : DyBox, s.n = N ∧ s.closedBox ⊆ C.closedBox ∧ s'.closedBox ⊆ C'.closedBox ∧
      SqAdj s s' := by
  obtain ⟨hne, hns⟩ := h
  simp only [Set.Subsingleton, not_forall] at hns
  obtain ⟨z, hz, z', hz', hzz⟩ := hns
  have hz2 : z ∈ C'.closedBox ∩ C.closedBox := ⟨hz.2, hz.1⟩
  have hz2' : z' ∈ C'.closedBox ∩ C.closedBox := ⟨hz'.2, hz'.1⟩
  obtain ⟨a1, a2, a3, a4⟩ := (bx_mem_closedBox hn).1 hz.1
  obtain ⟨b1, b2, b3, b4⟩ := (bx_mem_closedBox hn').1 hz.2
  have P1 : C.j * 2 ^ (N - C.n) ≤ (C'.j + 1) * 2 ^ (N - C'.n) := by
    have : ((C.j * 2 ^ (N - C.n) : ℕ) : ℝ) ≤ (((C'.j + 1) * 2 ^ (N - C'.n) : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have P2 : C'.j * 2 ^ (N - C'.n) ≤ (C.j + 1) * 2 ^ (N - C.n) := by
    have : ((C'.j * 2 ^ (N - C'.n) : ℕ) : ℝ) ≤ (((C.j + 1) * 2 ^ (N - C.n) : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have P3 : C.k * 2 ^ (N - C.n) ≤ (C'.k + 1) * 2 ^ (N - C'.n) := by
    have : ((C.k * 2 ^ (N - C.n) : ℕ) : ℝ) ≤ (((C'.k + 1) * 2 ^ (N - C'.n) : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have P4 : C'.k * 2 ^ (N - C'.n) ≤ (C.k + 1) * 2 ^ (N - C.n) := by
    have : ((C'.k * 2 ^ (N - C'.n) : ℕ) : ℝ) ≤ (((C.k + 1) * 2 ^ (N - C.n) : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have flip : ∀ s s' : DyBox, s.closedBox ⊆ C'.closedBox → s'.closedBox ⊆ C.closedBox →
      SqAdj s s' → s.n = N → ∃ s s' : DyBox, s.n = N ∧ s.closedBox ⊆ C.closedBox ∧
        s'.closedBox ⊆ C'.closedBox ∧ SqAdj s s' := fun s s' h1 h2 h3 h4 =>
    ⟨s', s, h3.1 ▸ h4, h2, h1, h3.symm⟩
  by_cases hj1 : C.j * 2 ^ (N - C.n) < (C'.j + 1) * 2 ^ (N - C'.n)
  · by_cases hj2 : C'.j * 2 ^ (N - C'.n) < (C.j + 1) * 2 ^ (N - C.n)
    · by_cases hk1 : C.k * 2 ^ (N - C.n) < (C'.k + 1) * 2 ^ (N - C'.n)
      · by_cases hk2 : C'.k * 2 ^ (N - C'.n) < (C.k + 1) * 2 ^ (N - C.n)
        · exfalso
          rcases le_total C'.n C.n with hle | hle
          · obtain ⟨u1, u2⟩ := dy_nested (show N - C.n ≤ N - C'.n by omega) hj1 hj2
            obtain ⟨v1, v2⟩ := dy_nested (show N - C.n ≤ N - C'.n by omega) hk1 hk2
            exact hne (hnest (sub_of_int_le hn hn' u1 u2 v1 v2))
          · obtain ⟨u1, u2⟩ := dy_nested (show N - C'.n ≤ N - C.n by omega) hj2 hj1
            obtain ⟨v1, v2⟩ := dy_nested (show N - C'.n ≤ N - C.n by omega) hk2 hk1
            exact hne (hnest' (sub_of_int_le hn' hn u1 u2 v1 v2)).symm
        · exact adj_case_k hn hn' (by omega) hz hz' hzz
      · obtain ⟨s, s', h1, h2, h3, h4⟩ := adj_case_k hn' hn (by omega) hz2 hz2' hzz
        exact flip s s' h2 h3 h4 h1
    · exact adj_case_j hn hn' (by omega) hz hz' hzz
  · obtain ⟨s, s', h1, h2, h3, h4⟩ := adj_case_j hn' hn (by omega) hz2 hz2' hzz
    exact flip s s' h2 h3 h4 h1

/-- **Neighbouring cells contain 4-adjacent level-`N` squares.** -/
theorem exists_sqAdj_of_neighbour {C C' : DyBox} {N : ℕ} (hC : IsCell m δ C) (hC' : IsCell m δ C')
    (hn : C.n ≤ N) (hn' : C'.n ≤ N) (h : Neighbour C C') :
    ∃ s s' : DyBox, s.n = N ∧ s.closedBox ⊆ C.closedBox ∧ s'.closedBox ⊆ C'.closedBox ∧
      SqAdj s s' :=
  exists_sqAdj_of_neighbour' (eq_of_sub_cell hC hC' hn hn') (eq_of_sub_cell hC' hC hn' hn) hn hn' h

end DZZ
end LQGMetric
