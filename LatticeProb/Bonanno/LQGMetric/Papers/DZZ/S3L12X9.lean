/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X8

/-!
# DZZ Lemma 3.12: the parent zones in the coarse annulus (D93 §2, packet P-6a, coarse step)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 1462–1466 (`𝔠_parents`), in the
site coordinates of `HasCross` (S3L12X6): whether a site's box lies in a parent cell depends only
on the site's region, and no parent cell contains the boxes of two opposite corners of the
annulus (it would contain `𝖢`).

* `spl` (the outer-corner line of one coordinate), `farB_eq`;
* **`sub_parent_iff_of_region`**; **`not_parent_opposite`**.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- The outer-corner line of a coordinate: `h` for odd indices, `-h` for even ones. -/
def spl (j h : ℕ) : ℤ := if j % 2 = 1 then (h : ℤ) else -(h : ℤ)

lemma farB_eq {j h : ℕ} {x x' : ℤ} (hx : x < spl j h ↔ x' < spl j h) :
    farB j h x = farB j h x' := by
  unfold farB spl at *
  split_ifs at * with hj
  · simp only [decide_eq_decide]; omega
  · simp only [decide_eq_decide]; omega

/-- **Parents see regions**: two annulus sites of one region lie in the same parent cells. -/
lemma sub_parent_iff_of_region {C P : DyBox} {k h : ℕ} (hC : 1 ≤ C.n) (hK : 2 ^ k = 2 * h)
    (hh : 1 ≤ h) (hP : IsParent m δ C P) {z z' : ℤ × ℤ} (hz : InGrid (C.n + k) (l37c C h) z)
    (hN : annBox (2 * (h : ℤ) - 2) z) (hz' : InGrid (C.n + k) (l37c C h) z')
    (hN' : annBox (2 * (h : ℤ) - 2) z')
    (ex : farB C.j h z.1 = farB C.j h z'.1) (ey : farB C.k h z.2 = farB C.k h z'.2) :
    (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox ↔
      (siteBox (C.n + k) (l37c C h) z').closedBox ⊆ P.closedBox := by
  have hlt := n_lt_of_side_lt hP.2.1
  have hPL : P.n ≤ C.n - 1 := by omega
  have hL : C.n - 1 ≤ C.n + k := by omega
  rw [sub_anc_iff hPL hL, sub_anc_iff (s := siteBox (C.n + k) (l37c C h) z') hPL hL,
    anc_eq_of_region hC hK hh hz hN hz' hN' ex ey]

/-- **No parent contains the boxes of two opposite corners of the annulus.** -/
lemma not_parent_opposite {C P : DyBox} {k h : ℕ} (hC : IsCell m δ C) (hK : 2 ^ k = 2 * h)
    (hh : 2 ≤ h) (hP : IsParent m δ C P) {z z' : ℤ × ℤ} (hz : InGrid (C.n + k) (l37c C h) z)
    (hz' : InGrid (C.n + k) (l37c C h) z')
    (hx : z.1 = -(2 * (h : ℤ) - 2) ∧ z'.1 = 2 * (h : ℤ) - 2 ∨
      z.1 = 2 * (h : ℤ) - 2 ∧ z'.1 = -(2 * (h : ℤ) - 2))
    (hy : z.2 = -(2 * (h : ℤ) - 2) ∧ z'.2 = 2 * (h : ℤ) - 2 ∨
      z.2 = 2 * (h : ℤ) - 2 ∧ z'.2 = -(2 * (h : ℤ) - 2))
    (h1 : (siteBox (C.n + k) (l37c C h) z).closedBox ⊆ P.closedBox)
    (h2 : (siteBox (C.n + k) (l37c C h) z').closedBox ⊆ P.closedBox) : False := by
  have hlt := n_lt_of_side_lt hP.2.1
  set L := C.n + k
  have hPL : P.n ≤ L := by omega
  obtain ⟨a1, a2, a3, a4⟩ := int_of_sub_closedBox rfl hPL h1
  obtain ⟨c1, c2, c3, c4⟩ := int_of_sub_closedBox rfl hPL h2
  have j1 : ((siteBox L (l37c C h) z).j : ℤ) = 2 * h * C.j + h + z.1 := by
    rw [siteBox_j hz]; simp [l37c]
  have k1 : ((siteBox L (l37c C h) z).k : ℤ) = 2 * h * C.k + h + z.2 := by
    rw [siteBox_k hz]; simp [l37c]
  have j2 : ((siteBox L (l37c C h) z').j : ℤ) = 2 * h * C.j + h + z'.1 := by
    rw [siteBox_j hz']; simp [l37c]
  have k2 : ((siteBox L (l37c C h) z').k : ℤ) = 2 * h * C.k + h + z'.2 := by
    rw [siteBox_k hz']; simp [l37c]
  -- `2^(L - P.n) = 2^(C.n - P.n) * 2h`
  have e : 2 ^ (L - P.n) = 2 ^ (C.n - P.n) * (2 * h) := by
    rw [← hK, ← pow_add]; congr 1; omega
  set E := 2 ^ (C.n - P.n)
  have hE : 0 < E := by positivity
  have hh2 : 0 < 2 * h := by omega
  -- index inequalities at level `L`, in `ℤ`
  have A1 : ((P.j * (E * (2 * h)) : ℕ) : ℤ) ≤ (siteBox L (l37c C h) z).j := by
    rw [← e]; exact_mod_cast a1
  have A2 : ((siteBox L (l37c C h) z).j : ℤ) + 1 ≤ (((P.j + 1) * (E * (2 * h)) : ℕ) : ℤ) := by
    rw [← e]; exact_mod_cast a2
  have A3 : ((P.k * (E * (2 * h)) : ℕ) : ℤ) ≤ (siteBox L (l37c C h) z).k := by
    rw [← e]; exact_mod_cast a3
  have A4 : ((siteBox L (l37c C h) z).k : ℤ) + 1 ≤ (((P.k + 1) * (E * (2 * h)) : ℕ) : ℤ) := by
    rw [← e]; exact_mod_cast a4
  have B1 : ((P.j * (E * (2 * h)) : ℕ) : ℤ) ≤ (siteBox L (l37c C h) z').j := by
    rw [← e]; exact_mod_cast c1
  have B2 : ((siteBox L (l37c C h) z').j : ℤ) + 1 ≤ (((P.j + 1) * (E * (2 * h)) : ℕ) : ℤ) := by
    rw [← e]; exact_mod_cast c2
  have B3 : ((P.k * (E * (2 * h)) : ℕ) : ℤ) ≤ (siteBox L (l37c C h) z').k := by
    rw [← e]; exact_mod_cast c3
  have B4 : ((siteBox L (l37c C h) z').k : ℤ) + 1 ≤ (((P.k + 1) * (E * (2 * h)) : ℕ) : ℤ) := by
    rw [← e]; exact_mod_cast c4
  rw [j1] at A1 A2; rw [k1] at A3 A4; rw [j2] at B1 B2; rw [k2] at B3 B4
  push_cast at A1 A2 A3 A4 B1 B2 B3 B4
  have hh' : (2 : ℤ) ≤ h := by exact_mod_cast hh
  -- `C ⊆ P` at level `C.n`
  have X1 : P.j * E * (2 * h) ≤ C.j * (2 * h) := by
    have : ((P.j * E * (2 * h) : ℕ) : ℤ) ≤ ((C.j * (2 * h) : ℕ) : ℤ) := by
      push_cast; rcases hx with ⟨x1, x2⟩ | ⟨x1, x2⟩ <;> linarith
    exact_mod_cast this
  have X2 : (C.j + 1) * (2 * h) ≤ (P.j + 1) * E * (2 * h) := by
    have : (((C.j + 1) * (2 * h) : ℕ) : ℤ) ≤ (((P.j + 1) * E * (2 * h) : ℕ) : ℤ) := by
      push_cast; rcases hx with ⟨x1, x2⟩ | ⟨x1, x2⟩ <;> linarith
    exact_mod_cast this
  have Y1 : P.k * E * (2 * h) ≤ C.k * (2 * h) := by
    have : ((P.k * E * (2 * h) : ℕ) : ℤ) ≤ ((C.k * (2 * h) : ℕ) : ℤ) := by
      push_cast; rcases hy with ⟨x1, x2⟩ | ⟨x1, x2⟩ <;> linarith
    exact_mod_cast this
  have Y2 : (C.k + 1) * (2 * h) ≤ (P.k + 1) * E * (2 * h) := by
    have : (((C.k + 1) * (2 * h) : ℕ) : ℤ) ≤ (((P.k + 1) * E * (2 * h) : ℕ) : ℤ) := by
      push_cast; rcases hy with ⟨x1, x2⟩ | ⟨x1, x2⟩ <;> linarith
    exact_mod_cast this
  have hsub : C.closedBox ⊆ P.closedBox := bx_sub_closedBox rfl hlt.le
    (by exact_mod_cast Nat.le_of_mul_le_mul_right X1 hh2)
    (by exact_mod_cast Nat.le_of_mul_le_mul_right X2 hh2)
    (by exact_mod_cast Nat.le_of_mul_le_mul_right Y1 hh2)
    (by exact_mod_cast Nat.le_of_mul_le_mul_right Y2 hh2)
  exact not_isCell_of_sub hC hlt hsub hP.1

end DZZ
end LQGMetric
