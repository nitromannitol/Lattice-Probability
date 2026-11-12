/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L316P2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinPath
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7Count

/-!
# DZZ Lemma 3.16: boundary boxes of enclosing boxes enclose (P2-DZZ316), part 1

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1393–1397: an enclosure of `B` by
boxes `B'_i ∈ 𝓑(B, ε)` all of whose boundary boxes `𝓑'_i = 𝓑_∂(B'_i, t/ε)` are good gives an
enclosure by good boxes of `𝓑(B, t)` (implicit in DZZ; own elementary argument).

This file: the index description of the boundary ring of a box.
* `fbox L x y`: the level-`L` box with indices `(x, y)`.
* `IsRingOf d b bt`: `bt` is a level-`(n_b + d)` box inside `b` touching an edge of `b` (indices).
* `closedBox_sub_of_ring`, `ring_mem_boxCollBdry`, `exists_ring_of_frontier`.
* `neighbour_idx`: neighbouring boxes of one level are `4`-adjacent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- The level-`L` box with indices `(x, y)` (clamped into the grid). -/
def fbox (L x y : ℕ) : DyBox := siteBox L (0, 0) ((x : ℤ), (y : ℤ))

lemma fbox_n (L x y : ℕ) : (fbox L x y).n = L := rfl

lemma fbox_j {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L) : (fbox L x y).j = x := by
  have h : InGrid L (0, 0) ((x : ℤ), (y : ℤ)) :=
    ⟨by simp, by simp; exact_mod_cast hx, by simp, by simp; exact_mod_cast hy⟩
  have := siteBox_j h
  simp only [zero_add] at this
  exact_mod_cast this

lemma fbox_k {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L) : (fbox L x y).k = y := by
  have h : InGrid L (0, 0) ((x : ℤ), (y : ℤ)) :=
    ⟨by simp, by simp; exact_mod_cast hx, by simp, by simp; exact_mod_cast hy⟩
  have := siteBox_k h
  simp only [zero_add] at this
  exact_mod_cast this

lemma fbox_self (b : DyBox) : fbox b.n b.j b.k = b := by
  have := siteBox_boxSite (0, 0) b rfl
  simpa [boxSite, fbox] using this

lemma neighbour_fbox_j {L x y : ℕ} (hx : x + 1 < 2 ^ L) (hy : y < 2 ^ L) :
    Neighbour (fbox L x y) (fbox L (x + 1) y) :=
  neighbour_of_j_succ rfl (by rw [fbox_k hx hy, fbox_k (by omega) hy])
    (by rw [fbox_j hx hy, fbox_j (by omega) hy])

lemma neighbour_fbox_k {L x y : ℕ} (hx : x < 2 ^ L) (hy : y + 1 < 2 ^ L) :
    Neighbour (fbox L x y) (fbox L x (y + 1)) :=
  neighbour_of_k_succ rfl (by rw [fbox_j hx hy, fbox_j hx (by omega)])
    (by rw [fbox_k hx hy, fbox_k hx (by omega)])

/-- `bt` lies in the boundary ring of `b` at depth `d` (index form). -/
def IsRingOf (d : ℕ) (b bt : DyBox) : Prop :=
  bt.n = b.n + d ∧ b.j * 2 ^ d ≤ bt.j ∧ bt.j + 1 ≤ (b.j + 1) * 2 ^ d ∧
    b.k * 2 ^ d ≤ bt.k ∧ bt.k + 1 ≤ (b.k + 1) * 2 ^ d ∧
    (bt.j = b.j * 2 ^ d ∨ bt.j + 1 = (b.j + 1) * 2 ^ d ∨
      bt.k = b.k * 2 ^ d ∨ bt.k + 1 = (b.k + 1) * 2 ^ d)

lemma succ_mul_pow_le (b : DyBox) (d : ℕ) :
    (b.j + 1) * 2 ^ d ≤ 2 ^ (b.n + d) ∧ (b.k + 1) * 2 ^ d ≤ 2 ^ (b.n + d) := by
  rw [pow_add]
  exact ⟨Nat.mul_le_mul_right _ b.hj, Nat.mul_le_mul_right _ b.hk⟩

/-- Ring boxes in index form. -/
lemma isRingOf_fbox {d : ℕ} {b : DyBox} {x y : ℕ} (h1 : b.j * 2 ^ d ≤ x)
    (h2 : x + 1 ≤ (b.j + 1) * 2 ^ d) (h3 : b.k * 2 ^ d ≤ y) (h4 : y + 1 ≤ (b.k + 1) * 2 ^ d)
    (h5 : x = b.j * 2 ^ d ∨ x + 1 = (b.j + 1) * 2 ^ d ∨ y = b.k * 2 ^ d ∨
      y + 1 = (b.k + 1) * 2 ^ d) : IsRingOf d b (fbox (b.n + d) x y) := by
  obtain ⟨e1, e2⟩ := succ_mul_pow_le b d
  have hx : x < 2 ^ (b.n + d) := by omega
  have hy : y < 2 ^ (b.n + d) := by omega
  rw [IsRingOf, fbox_j hx hy, fbox_k hx hy]
  exact ⟨rfl, h1, h2, h3, h4, h5⟩

lemma side_rel {b bt : DyBox} {d : ℕ} (hn : bt.n = b.n + d) :
    b.side = (2 : ℝ) ^ d * bt.side := by
  have := side_eq_pow_mul (b := b) (b' := bt) hn
  push_cast at this; exact this

lemma closedBox_sub_of_ring {d : ℕ} {b bt : DyBox} (h : IsRingOf d b bt) :
    bt.closedBox ⊆ b.closedBox := by
  obtain ⟨hn, h1, h2, h3, h4, -⟩ := h
  have e := side_rel hn
  have s0 := side_pos' bt
  have r1 : (b.j : ℝ) * 2 ^ d ≤ bt.j := by exact_mod_cast h1
  have r2 : (bt.j : ℝ) + 1 ≤ (b.j + 1) * 2 ^ d := by exact_mod_cast h2
  have r3 : (b.k : ℝ) * 2 ^ d ≤ bt.k := by exact_mod_cast h3
  have r4 : (bt.k : ℝ) + 1 ≤ (b.k + 1) * 2 ^ d := by exact_mod_cast h4
  rintro z ⟨a1, a2, a3, a4⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;> nlinarith

lemma closedBox_eq_reProdIm (b : DyBox) : b.closedBox =
    Icc (b.j * b.side) ((b.j + 1) * b.side) ×ℂ Icc (b.k * b.side) ((b.k + 1) * b.side) := by
  ext z; simp [DyBox.closedBox, Complex.mem_reProdIm, and_assoc]

/-- A point of a closed box on one of its edges is on its frontier. -/
lemma mem_frontier_closedBox {b : DyBox} {z : ℂ} (hz : z ∈ b.closedBox)
    (he : z.re = b.j * b.side ∨ z.re = (b.j + 1) * b.side ∨
      z.im = b.k * b.side ∨ z.im = (b.k + 1) * b.side) : z ∈ frontier b.closedBox := by
  have s0 := side_pos' b
  have hj : (b.j : ℝ) * b.side ≤ (b.j + 1) * b.side := by nlinarith
  have hk : (b.k : ℝ) * b.side ≤ (b.k + 1) * b.side := by nlinarith
  obtain ⟨a1, a2, a3, a4⟩ := hz
  rw [closedBox_eq_reProdIm, Complex.frontier_reProdIm, closure_Icc, closure_Icc,
    frontier_Icc hj, frontier_Icc hk]
  rcases he with h | h | h | h
  · exact Or.inr (Complex.mem_reProdIm.2 ⟨by simp [h], a3, a4⟩)
  · exact Or.inr (Complex.mem_reProdIm.2 ⟨by simp [h], a3, a4⟩)
  · exact Or.inl (Complex.mem_reProdIm.2 ⟨⟨a1, a2⟩, by simp [h]⟩)
  · exact Or.inl (Complex.mem_reProdIm.2 ⟨⟨a1, a2⟩, by simp [h]⟩)

/-- Ring boxes meet the frontier of the box: they are boundary boxes. -/
lemma ring_mem_boxCollBdry {d : ℕ} {b bt : DyBox} (h : IsRingOf d b bt) :
    bt ∈ boxCollBdry b d := by
  refine ⟨h.1, ?_⟩
  have hsub := closedBox_sub_of_ring h
  obtain ⟨hn, -, -, -, -, h5⟩ := h
  have e := side_rel hn
  have s0 := side_pos' bt
  set s := bt.side
  have cor : ∀ x y : ℝ, (x = bt.j ∨ x = bt.j + 1) → (y = bt.k ∨ y = bt.k + 1) →
      (⟨x * s, y * s⟩ : ℂ) ∈ bt.closedBox := by
    rintro x y hx hy
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> rcases hx with rfl | rfl <;>
      rcases hy with rfl | rfl <;> nlinarith
  rcases h5 with h | h | h | h
  · have hz := cor bt.j bt.k (Or.inl rfl) (Or.inl rfl)
    refine ⟨_, hz, mem_frontier_closedBox (hsub hz) (Or.inl ?_)⟩
    have : (bt.j : ℝ) = b.j * 2 ^ d := by exact_mod_cast h
    simp only; rw [e, this]; ring
  · have hz := cor (bt.j + 1) bt.k (Or.inr rfl) (Or.inl rfl)
    refine ⟨_, hz, mem_frontier_closedBox (hsub hz) (Or.inr (Or.inl ?_))⟩
    have : (bt.j : ℝ) + 1 = (b.j + 1) * 2 ^ d := by exact_mod_cast h
    simp only; rw [e, this]; ring
  · have hz := cor bt.j bt.k (Or.inl rfl) (Or.inl rfl)
    refine ⟨_, hz, mem_frontier_closedBox (hsub hz) (Or.inr (Or.inr (Or.inl ?_)))⟩
    have : (bt.k : ℝ) = b.k * 2 ^ d := by exact_mod_cast h
    simp only; rw [e, this]; ring
  · have hz := cor bt.j (bt.k + 1) (Or.inl rfl) (Or.inr rfl)
    refine ⟨_, hz, mem_frontier_closedBox (hsub hz) (Or.inr (Or.inr (Or.inr ?_)))⟩
    have : (bt.k : ℝ) + 1 = (b.k + 1) * 2 ^ d := by exact_mod_cast h
    simp only; rw [e, this]; ring

/-- The clamped index of a coordinate `X ∈ [J, J + N]` (`N ≥ 1`): `x ∈ [J, J+N-1]`,
`x ≤ X ≤ x + 1`, `x = J` if `X = J`, `x + 1 = J + N` if `X = J + N`. -/
lemma exists_ringClamp {J N : ℕ} (hN : 1 ≤ N) {X : ℝ} (h1 : (J : ℝ) ≤ X) (h2 : X ≤ J + N) :
    ∃ x : ℕ, J ≤ x ∧ x + 1 ≤ J + N ∧ (x : ℝ) ≤ X ∧ X ≤ x + 1 ∧
      (X = J → x = J) ∧ (X = J + N → x + 1 = J + N) := by
  have hX0 : 0 ≤ X := le_trans (Nat.cast_nonneg _) h1
  refine ⟨min ⌊X⌋₊ (J + N - 1), ?_, by omega, ?_, ?_, ?_, ?_⟩
  · exact le_min (Nat.le_floor h1) (by omega)
  · exact (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le hX0)
  · rcases le_total ⌊X⌋₊ (J + N - 1) with h | h
    · rw [min_eq_left h]; exact (Nat.lt_floor_add_one X).le
    · rw [min_eq_right h]
      have : ((J + N - 1 : ℕ) : ℝ) + 1 = J + N := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      linarith
  · intro hX
    have : ⌊X⌋₊ = J := by rw [hX]; exact Nat.floor_natCast J
    omega
  · intro hX
    have : ⌊X⌋₊ = J + N := by rw [hX]; exact_mod_cast Nat.floor_natCast (J + N)
    omega

/-- A frontier point of `b` lies in a ring box of `b` at any depth. -/
lemma exists_ring_of_frontier (d : ℕ) {b : DyBox} {z : ℂ} (hz : z ∈ frontier b.closedBox) :
    ∃ bt, IsRingOf d b bt ∧ z ∈ bt.closedBox := by
  obtain ⟨⟨a1, a2, a3, a4⟩, he⟩ := frontier_closedBox_sub hz
  set L := b.n + d
  have hs : b.side * 2 ^ L = 2 ^ d := by
    unfold DyBox.side; rw [show L = b.n + d from rfl, pow_add, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ two_ne_zero, one_pow, one_mul]
  have hN : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have hp : (0 : ℝ) < 2 ^ L := by positivity
  have key : ∀ (i : ℕ) (w : ℝ), (i : ℝ) * b.side ≤ w → w ≤ (i + 1) * b.side →
      ∃ x : ℕ, i * 2 ^ d ≤ x ∧ x + 1 ≤ (i + 1) * 2 ^ d ∧ (x : ℝ) ≤ w * 2 ^ L ∧
        w * 2 ^ L ≤ x + 1 ∧ (w = i * b.side → x = i * 2 ^ d) ∧
        (w = (i + 1) * b.side → x + 1 = (i + 1) * 2 ^ d) := by
    intro i w hw1 hw2
    have m1 := mul_le_mul_of_nonneg_right hw1 hp.le
    have m2 := mul_le_mul_of_nonneg_right hw2 hp.le
    rw [mul_assoc, hs] at m1 m2
    obtain ⟨x, c1, c2, c3, c4, c5, c6⟩ := exists_ringClamp (J := i * 2 ^ d) (N := 2 ^ d) hN
      (X := w * 2 ^ L) (by push_cast; linarith) (by push_cast; linarith)
    refine ⟨x, c1, ?_, c3, c4, fun h => c5 (by rw [h, mul_assoc, hs]; push_cast; ring),
      fun h => ?_⟩
    · rw [add_mul, one_mul]; exact c2
    · rw [add_mul, one_mul]; exact c6 (by rw [h, mul_assoc, hs]; push_cast; ring)
  obtain ⟨x, x1, x2, x3, x4, x5, x6⟩ := key b.j z.re a1 a2
  obtain ⟨y, y1, y2, y3, y4, y5, y6⟩ := key b.k z.im a3 a4
  have hring : IsRingOf d b (fbox L x y) := by
    refine isRingOf_fbox x1 x2 y1 y2 ?_
    rcases he with h | h | h | h
    · exact Or.inl (x5 h)
    · exact Or.inr (Or.inl (x6 h))
    · exact Or.inr (Or.inr (Or.inl (y5 h)))
    · exact Or.inr (Or.inr (Or.inr (y6 h)))
  refine ⟨_, hring, ?_⟩
  obtain ⟨e1, e2⟩ := succ_mul_pow_le b d
  have e1' : (b.j + 1) * 2 ^ d ≤ 2 ^ L := e1
  have e2' : (b.k + 1) * 2 ^ d ≤ 2 ^ L := e2
  have hx : x < 2 ^ L := by omega
  have hy : y < 2 ^ L := by omega
  have hsL : (fbox L x y).side * 2 ^ L = 1 := by
    unfold DyBox.side; rw [fbox_n]; exact pow_inv_mul_pow L
  have st : (fbox L x y).side = ((2 : ℝ) ^ L)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left hsL
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [st] <;> simp only [fbox_j hx hy, fbox_k hx hy] <;>
    first
    | (rw [← div_eq_mul_inv, div_le_iff₀ hp]; linarith)
    | (rw [← div_eq_mul_inv, le_div_iff₀ hp]; linarith)

/-- Neighbouring boxes of one level are `4`-adjacent. -/
lemma neighbour_idx {b₁ b₂ : DyBox} (hn : b₁.n = b₂.n) (h : Neighbour b₁ b₂) :
    (b₂.j = b₁.j + 1 ∧ b₂.k = b₁.k) ∨ (b₁.j = b₂.j + 1 ∧ b₂.k = b₁.k) ∨
      (b₂.k = b₁.k + 1 ∧ b₂.j = b₁.j) ∨ (b₁.k = b₂.k + 1 ∧ b₂.j = b₁.j) := by
  obtain ⟨hne, hns⟩ := h
  simp only [Set.Subsingleton, not_forall] at hns
  obtain ⟨p, ⟨hp1, hp2⟩, q, ⟨hq1, hq2⟩, hpq⟩ := hns
  have es : b₂.side = b₁.side := by unfold DyBox.side; rw [hn]
  have s0 := side_pos' b₁
  obtain ⟨p1, p2, p3, p4⟩ := hp1
  obtain ⟨p5, p6, p7, p8⟩ := hp2
  obtain ⟨q1, q2, q3, q4⟩ := hq1
  obtain ⟨q5, q6, q7, q8⟩ := hq2
  rw [es] at p5 p6 p7 p8 q5 q6 q7 q8
  obtain ⟨j1, -⟩ := l37_idx_bounds (d := b₂.j + 1) s0 p1 p2 p5 (by push_cast; exact p6)
  obtain ⟨j3, -⟩ := l37_idx_bounds (d := b₁.j + 1) s0 p5 p6 p1 (by push_cast; exact p2)
  obtain ⟨k1, -⟩ := l37_idx_bounds (d := b₂.k + 1) s0 p3 p4 p7 (by push_cast; exact p8)
  obtain ⟨k3, -⟩ := l37_idx_bounds (d := b₁.k + 1) s0 p7 p8 p3 (by push_cast; exact p4)
  -- if the columns differ, both points lie on the common vertical line
  have hre : b₁.j ≠ b₂.j → p.re = q.re := by
    intro hj
    rcases Nat.lt_or_gt_of_ne hj with hl | hl
    · have e : (b₂.j : ℝ) = b₁.j + 1 := by exact_mod_cast (show b₂.j = b₁.j + 1 by omega)
      rw [e] at p5 q5; linarith
    · have e : (b₁.j : ℝ) = b₂.j + 1 := by exact_mod_cast (show b₁.j = b₂.j + 1 by omega)
      rw [e] at p1 q1; linarith
  have him : b₁.k ≠ b₂.k → p.im = q.im := by
    intro hk
    rcases Nat.lt_or_gt_of_ne hk with hl | hl
    · have e : (b₂.k : ℝ) = b₁.k + 1 := by exact_mod_cast (show b₂.k = b₁.k + 1 by omega)
      rw [e] at p7 q7; linarith
    · have e : (b₁.k : ℝ) = b₂.k + 1 := by exact_mod_cast (show b₁.k = b₂.k + 1 by omega)
      rw [e] at p3 q3; linarith
  by_cases hj : b₁.j = b₂.j
  · by_cases hk : b₁.k = b₂.k
    · exact absurd (DyBox.ext hn hj hk) hne
    · omega
  · by_cases hk : b₁.k = b₂.k
    · omega
    · exact absurd (Complex.ext (hre hj) (him hk)) hpq

end DZZ
end LQGMetric
