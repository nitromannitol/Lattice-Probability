/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12U1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12T8

/-!
# DZZ Lemma 3.12: zones of the parents and the clipped case (D93, packets P-5, P-7)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12: `𝔠_parents`
(l. 1462–1466) are the cells containing `𝖡_lt, 𝖡_rt, 𝖡_lb`, the three boxes of side `2 s_𝖢` at
the outer corner `z*` of `𝖢` other than the parent `𝖡_rb ⊃ 𝖢`; "if `𝖢_large ∩ ∂𝕍 ≠ ∅` there is
at most one parent" (l. 1498). Orientation-free form (D93):

* `IsQuad C Q`: `Q` is a box of level `n_𝖢 - 1` with `z*(𝖢) ∈ Q̄`, other than the parent of `𝖢`;
* `cell_eq_of_sub`, `not_isCell_of_sub`: cells are disjoint dyadic boxes;
* **`exists_quad_of_parent`**: every parent contains a quadrant box (`parent_contains_quad`);
* **`parent_eq_of_quad`**: a quadrant box lies in at most one cell;
* `largeBox_sub_interior`, **`quad_unique_of_not_interior`**,
  **`le_one_parent_of_not_interior`**: near `∂𝕍` there is at most one parent (l. 1498);

* **`l312CoreR_of_ring`**: the clipped case (any segment of the enclosure, Cases 1–2 with at


Own elementary arguments (integer arithmetic on the level-`n_𝖢` grid), DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- Two cells containing a common box of finer or equal level are equal. -/
lemma cell_eq_of_sub {Q P P' : DyBox} (hP : IsCell m δ P) (hP' : IsCell m δ P')
    (h : P.n ≤ Q.n) (h' : P'.n ≤ Q.n) (hs : Q.closedBox ⊆ P.closedBox)
    (hs' : Q.closedBox ⊆ P'.closedBox) : P = P' :=
  isSqCell_unique ⟨hP, h, anc_eq_of_sub rfl h hs⟩ ⟨hP', h', anc_eq_of_sub rfl h' hs'⟩

/-- A cell does not strictly contain a cell. -/
lemma not_isCell_of_sub {C P : DyBox} (hC : IsCell m δ C) (hlt : P.n < C.n)
    (hs : C.closedBox ⊆ P.closedBox) : ¬ IsCell m δ P := by
  intro hP
  have h := hC.2 P.n hlt
  rw [anc_eq_of_sub rfl hlt.le hs] at h
  linarith [hP.1]

lemma n_lt_of_side_lt {c C : DyBox} (h : C.side < c.side) : c.n < C.n := by
  by_contra hn; push Not at hn
  have : c.side ≤ C.side := by
    unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  linarith

/-- The quadrant boxes of `𝖢` (`𝖡_lt, 𝖡_rt, 𝖡_lb` of DZZ l. 1462–1464, orientation-free). -/
def IsQuad (C Q : DyBox) : Prop :=
  Q.n + 1 = C.n ∧ outerCorner C ∈ Q.closedBox ∧ Q ≠ C.anc Q.n

/-- **Every parent contains a quadrant box** (`𝔠_parents`, l. 1462–1466). -/
theorem exists_quad_of_parent {C P : DyBox} (hC : IsCell m δ C) (hP : IsCell m δ P)
    (hs : C.side < P.side) (hPL : (P.closedBox ∩ C.largeBox).Nonempty) :
    ∃ Q, IsQuad C Q ∧ Q.closedBox ⊆ P.closedBox := by
  have hlt := n_lt_of_side_lt hs
  have hz := outerCorner_mem_of_side_lt hs hPL
  obtain ⟨Q, hQn, hQP, hzQ⟩ := exists_sq_of_mem_closedBox (K := C.n - 1) (by omega) hz
  refine ⟨Q, ⟨by omega, hzQ, fun he => ?_⟩, hQP⟩
  have hCQ : C.closedBox ⊆ Q.closedBox := by rw [he]; exact closedBox_sub_anc C _
  exact not_isCell_of_sub hC hlt (hCQ.trans hQP) hP

/-- **A quadrant box lies in at most one parent.** -/
theorem parent_eq_of_quad {C Q P P' : DyBox} (hP : IsCell m δ P) (hP' : IsCell m δ P')
    (hs : C.side < P.side) (hs' : C.side < P'.side) (hQ : IsQuad C Q)
    (hQP : Q.closedBox ⊆ P.closedBox) (hQP' : Q.closedBox ⊆ P'.closedBox) : P = P' := by
  have h1 := n_lt_of_side_lt hs
  have h2 := n_lt_of_side_lt hs'
  exact cell_eq_of_sub hP hP' (by have := hQ.1; omega) (by have := hQ.1; omega) hQP hQP'

/-- `𝖢_large ⊆ 𝕍°` for boxes away from `∂𝕍`. -/
lemma largeBox_sub_interior {C : DyBox} (h1 : 1 ≤ C.j) (h2 : C.j + 2 ≤ 2 ^ C.n)
    (h3 : 1 ≤ C.k) (h4 : C.k + 2 ≤ 2 ^ C.n) : C.largeBox ⊆ interior dzzV := by
  set U : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < 1}
  have hU : IsOpen U := by
    simp only [U, ofPred_and]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)))
  have hUV : U ⊆ dzzV := fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  refine fun z hz => interior_maximal hUV hU ?_
  have e := bx_side_mul (b := C) (N := C.n) le_rfl
  simp only [Nat.sub_self, pow_zero] at e
  have hs := C.side_pos'
  have r1 : (1 : ℝ) ≤ C.j := by exact_mod_cast h1
  have r2 : (C.j : ℝ) + 2 ≤ 2 ^ C.n := by exact_mod_cast h2
  have r3 : (1 : ℝ) ≤ C.k := by exact_mod_cast h3
  have r4 : (C.k : ℝ) + 2 ≤ 2 ^ C.n := by exact_mod_cast h4
  simp only [DyBox.largeBox, mem_ofPred_eq, abs_le, DyBox.center] at hz
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hz
  simp only [U, mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma quad_int {C Q : DyBox} (hQ : IsQuad C Q) :
    2 * Q.j ≤ C.j + C.j % 2 ∧ C.j + C.j % 2 ≤ 2 * Q.j + 2 ∧
      2 * Q.k ≤ C.k + C.k % 2 ∧ C.k + C.k % 2 ≤ 2 * Q.k + 2 := by
  obtain ⟨hn, hz, -⟩ := hQ
  obtain ⟨a1, a2, a3, a4⟩ := (bx_mem_closedBox (N := C.n) (by omega)).1 hz
  obtain ⟨e1, e2⟩ := outerCorner_scaled C
  rw [e1] at a1 a2; rw [e2] at a3 a4
  rw [show C.n - Q.n = 1 by omega, pow_one] at a1 a2 a3 a4
  have b1 : Q.j * 2 ≤ C.j + C.j % 2 := by exact_mod_cast a1
  have b2 : C.j + C.j % 2 ≤ (Q.j + 1) * 2 := by exact_mod_cast a2
  have b3 : Q.k * 2 ≤ C.k + C.k % 2 := by exact_mod_cast a3
  have b4 : C.k + C.k % 2 ≤ (Q.k + 1) * 2 := by exact_mod_cast a4
  omega

/-- **Near `∂𝕍` there is at most one quadrant box** (DZZ l. 1498). -/
theorem quad_unique_of_not_interior {C Q Q' : DyBox} (h : ¬ C.largeBox ⊆ interior dzzV)
    (hQ : IsQuad C Q) (hQ' : IsQuad C Q') : Q = Q' := by
  have hn : 1 ≤ C.n := by have := hQ.1; omega
  have hCj := C.hj; have hCk := C.hk
  have hQj := Q.hj; have hQk := Q.hk; have hQj' := Q'.hj; have hQk' := Q'.hk
  have p2 : 2 ^ C.n = 2 * 2 ^ Q.n := by rw [← hQ.1, pow_succ]; ring
  have p2' : 2 ^ Q'.n = 2 ^ Q.n := by rw [show Q'.n = Q.n by have := hQ.1; have := hQ'.1; omega]
  rw [p2'] at hQj' hQk'
  obtain ⟨c1, c2, c3, c4⟩ := quad_int hQ
  obtain ⟨d1, d2, d3, d4⟩ := quad_int hQ'
  have hne := hQ.2.2; have hne' := hQ'.2.2
  have q1 := hQ.1; have q2 := hQ'.1
  have eA : (C.anc Q.n).j = C.j / 2 ∧ (C.anc Q.n).k = C.k / 2 := by
    show C.j / 2 ^ (C.n - Q.n) = C.j / 2 ∧ C.k / 2 ^ (C.n - Q.n) = C.k / 2
    rw [show C.n - Q.n = 1 by omega, pow_one]; exact ⟨rfl, rfl⟩
  have eA' : (C.anc Q'.n).j = C.j / 2 ∧ (C.anc Q'.n).k = C.k / 2 := by
    show C.j / 2 ^ (C.n - Q'.n) = C.j / 2 ∧ C.k / 2 ^ (C.n - Q'.n) = C.k / 2
    rw [show C.n - Q'.n = 1 by omega, pow_one]; exact ⟨rfl, rfl⟩
  have hnA : (C.anc Q.n).n = Q.n := by show min Q.n C.n = Q.n; omega
  have hnA' : (C.anc Q'.n).n = Q'.n := by show min Q'.n C.n = Q'.n; omega
  have ne_of : ∀ R : DyBox, R ≠ C.anc R.n → (C.anc R.n).n = R.n →
      R.j ≠ (C.anc R.n).j ∨ R.k ≠ (C.anc R.n).k := by
    intro R hR hn'
    by_contra hc; push Not at hc
    exact hR (by cases R; cases h' : C.anc _; simp_all)
  have hb : C.j = 0 ∨ C.j + 1 = 2 ^ C.n ∨ C.k = 0 ∨ C.k + 1 = 2 ^ C.n := by
    by_contra hc; push Not at hc
    exact h (largeBox_sub_interior (by omega) (by omega) (by omega) (by omega))
  have hjk : Q.j = Q'.j ∧ Q.k = Q'.k := by
    have e1 := eA.1; have e2 := eA.2; have e3 := eA'.1; have e4 := eA'.2
    rcases ne_of Q hne hnA with x | x <;> rcases ne_of Q' hne' hnA' with y | y <;> omega
  have hn' : Q.n = Q'.n := by omega
  revert hn' hjk
  cases Q; cases Q'
  simp only [DyBox.mk.injEq]
  intro a b; exact ⟨b, a⟩

/-- **At most one parent near `∂𝕍`** (DZZ l. 1498). -/
theorem le_one_parent_of_not_interior {C P P' : DyBox} (h : ¬ C.largeBox ⊆ interior dzzV)
    (hC : IsCell m δ C) (hP : IsCell m δ P) (hP' : IsCell m δ P') (hs : C.side < P.side)
    (hs' : C.side < P'.side) (hPL : (P.closedBox ∩ C.largeBox).Nonempty)
    (hPL' : (P'.closedBox ∩ C.largeBox).Nonempty) : P = P' := by
  obtain ⟨Q, hQ, hQP⟩ := exists_quad_of_parent hC hP hs hPL
  obtain ⟨Q', hQ', hQP'⟩ := exists_quad_of_parent hC hP' hs' hPL'
  rw [quad_unique_of_not_interior h hQ' hQ] at hQP'
  exact parent_eq_of_quad hP hP' hs hs' hQ hQP hQP'

end DZZ
end LQGMetric
