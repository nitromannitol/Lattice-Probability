/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X5

/-!
# DZZ Lemma 3.12: the regions of the coarse annulus (D93 §2, packet P-6a, coarse step)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, l. 1462–1466
(`𝔠_parents`: the quadrant boxes `𝖡_lt, 𝖡_rt, 𝖡_lb` at the outer corner of `𝖢`), in the site
coordinates of `HasCross` (`2^k = 2h`, `𝖢` = sites `[-h, h-1]²`, the outer corner on the line
`h` or `-h` according to the parity of the index of `𝖢`): the level-`(n_𝖢 - 1)` ancestor of
the box of an annulus site depends only on which side of the two lines through the outer
corner the site lies (its *region*), and a box lies in a parent cell iff its region's
quadrant box does.

* `farB`, `qIdx`, **`q1d`** (one coordinate), **`anc_siteBox_j`**, **`anc_siteBox_k`**;
* `sub_anc_iff`: a box lies in a box of level `≤ L` iff its level-`L` ancestor does;
* `anc_home`: the region of `(near, near)` is the parent box of `𝖢`;
* **`anc_eq_of_region`** (region constancy), `inGrid_of_interior`.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

open DyBox

/-- The site coordinate `x` lies beyond the outer-corner line (`j` the index of `𝖢`). -/
def farB (j h : ℕ) (x : ℤ) : Bool :=
  if j % 2 = 1 then decide ((h : ℤ) ≤ x) else decide (x ≤ -(h : ℤ) - 1)

/-- The index of the level-`(n_𝖢 - 1)` box of a region (`far` or near). -/
def qIdx (j : ℕ) (far : Bool) : ℕ :=
  if far then (if j % 2 = 1 then j / 2 + 1 else j / 2 - 1) else j / 2

/-- **One coordinate of the region box.** -/
lemma q1d {j h : ℕ} {x : ℤ} (hh : 1 ≤ h) (hx1 : -(2 * (h : ℤ) - 2) ≤ x)
    (hx2 : x ≤ 2 * (h : ℤ) - 2) (hJ : 0 ≤ 2 * (h : ℤ) * j + h + x) :
    ((qIdx j (farB j h x) : ℕ) : ℤ) * (4 * h) ≤ 2 * (h : ℤ) * j + h + x ∧
      2 * (h : ℤ) * j + h + x < ((qIdx j (farB j h x) : ℕ) + 1) * (4 * h) := by
  obtain ⟨a, r, hr, rfl⟩ : ∃ a r, r < 2 ∧ j = 2 * a + r := ⟨j / 2, j % 2, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod j 2).symm⟩
  have e1 : (2 * a + r) / 2 = a := by omega
  have e2 : (2 * a + r) % 2 = r := by omega
  have hh' : (1 : ℤ) ≤ h := by exact_mod_cast hh
  interval_cases r
  · simp only [farB, qIdx, e1, e2]
    by_cases hf : x ≤ -(h : ℤ) - 1
    · have ha : 1 ≤ a := by
        by_contra h0; push Not at h0
        have : a = 0 := by omega
        subst this; push_cast at hJ; omega
      simp only [hf, decide_true, if_true, show ¬ (0 = 1) from by omega, if_false]
      rw [Nat.cast_sub ha]; push_cast
      constructor <;> nlinarith
    · simp only [hf, decide_false, Bool.false_eq_true, if_false]
      push_cast
      constructor <;> nlinarith
  · simp only [farB, qIdx, e1, e2, if_true]
    by_cases hf : (h : ℤ) ≤ x
    · simp only [hf, decide_true, if_true]
      push_cast
      constructor <;> nlinarith
    · simp only [hf, decide_false, Bool.false_eq_true, if_false]
      push_cast
      constructor <;> nlinarith

/-- The `j`-index of the level-`(n_𝖢 - 1)` ancestor of the box of an annulus site. -/
lemma anc_siteBox_j {C : DyBox} {k h : ℕ} (hC : 1 ≤ C.n) (hK : 2 ^ k = 2 * h) (hh : 1 ≤ h)
    {z : ℤ × ℤ} (hz : InGrid (C.n + k) (l37c C h) z) (hN : annBox (2 * (h : ℤ) - 2) z) :
    ((siteBox (C.n + k) (l37c C h) z).anc (C.n - 1)).j = qIdx C.j (farB C.j h z.1) := by
  obtain ⟨b1, b2, -, -⟩ := hN
  have hJ : 0 ≤ 2 * (h : ℤ) * C.j + h + z.1 := by have := hz.1; simp only [l37c] at this; linarith
  obtain ⟨q1, q2⟩ := q1d (j := C.j) hh b1 b2 hJ
  have e : (siteBox (C.n + k) (l37c C h) z).n - (C.n - 1) = k + 1 := by
    show C.n + k - (C.n - 1) = k + 1; omega
  show (siteBox (C.n + k) (l37c C h) z).j / 2 ^ ((siteBox (C.n + k) (l37c C h) z).n - (C.n - 1))
    = _
  rw [e, pow_succ, hK]
  have hJ' : ((siteBox (C.n + k) (l37c C h) z).j : ℤ) = 2 * h * C.j + h + z.1 := by
    rw [siteBox_j hz]; simp [l37c]
  apply Nat.div_eq_of_lt_le
  · have : ((qIdx C.j (farB C.j h z.1) * (2 * h * 2) : ℕ) : ℤ) ≤
        ((siteBox (C.n + k) (l37c C h) z).j : ℤ) := by push_cast; rw [hJ']; linarith
    exact_mod_cast this
  · have : ((siteBox (C.n + k) (l37c C h) z).j : ℤ) <
        (((qIdx C.j (farB C.j h z.1) + 1) * (2 * h * 2) : ℕ) : ℤ) := by push_cast; rw [hJ']; linarith
    exact_mod_cast this

/-- The `k`-index of the level-`(n_𝖢 - 1)` ancestor of the box of an annulus site. -/
lemma anc_siteBox_k {C : DyBox} {k h : ℕ} (hC : 1 ≤ C.n) (hK : 2 ^ k = 2 * h) (hh : 1 ≤ h)
    {z : ℤ × ℤ} (hz : InGrid (C.n + k) (l37c C h) z) (hN : annBox (2 * (h : ℤ) - 2) z) :
    ((siteBox (C.n + k) (l37c C h) z).anc (C.n - 1)).k = qIdx C.k (farB C.k h z.2) := by
  obtain ⟨-, -, b1, b2⟩ := hN
  have hJ : 0 ≤ 2 * (h : ℤ) * C.k + h + z.2 := by
    have := hz.2.2.1; simp only [l37c] at this; linarith
  obtain ⟨q1, q2⟩ := q1d (j := C.k) hh b1 b2 hJ
  have e : (siteBox (C.n + k) (l37c C h) z).n - (C.n - 1) = k + 1 := by
    show C.n + k - (C.n - 1) = k + 1; omega
  show (siteBox (C.n + k) (l37c C h) z).k / 2 ^ ((siteBox (C.n + k) (l37c C h) z).n - (C.n - 1))
    = _
  rw [e, pow_succ, hK]
  have hJ' : ((siteBox (C.n + k) (l37c C h) z).k : ℤ) = 2 * h * C.k + h + z.2 := by
    rw [siteBox_k hz]; simp [l37c]
  apply Nat.div_eq_of_lt_le
  · have : ((qIdx C.k (farB C.k h z.2) * (2 * h * 2) : ℕ) : ℤ) ≤
        ((siteBox (C.n + k) (l37c C h) z).k : ℤ) := by push_cast; rw [hJ']; linarith
    exact_mod_cast this
  · have : ((siteBox (C.n + k) (l37c C h) z).k : ℤ) <
        (((qIdx C.k (farB C.k h z.2) + 1) * (2 * h * 2) : ℕ) : ℤ) := by push_cast; rw [hJ']; linarith
    exact_mod_cast this

/-- A box lies in a box `P` of level `≤ L ≤` its own level iff its level-`L` ancestor does. -/
lemma sub_anc_iff {s P : DyBox} {L : ℕ} (hPL : P.n ≤ L) (hLs : L ≤ s.n) :
    s.closedBox ⊆ P.closedBox ↔ (s.anc L).closedBox ⊆ P.closedBox := by
  constructor
  · intro hs
    have e2 : s.anc P.n = P := anc_eq_of_sub rfl (hPL.trans hLs) hs
    have e3 : (s.anc L).anc P.n = P := by rw [anc_anc s hPL, e2]
    rw [← e3]
    exact closedBox_sub_anc _ _
  · intro h; exact (closedBox_sub_anc s L).trans h

/-- The home region `(near, near)` is the parent box of `𝖢`. -/
lemma anc_home {C : DyBox} {k h : ℕ} (hC : 1 ≤ C.n) (hK : 2 ^ k = 2 * h) (hh : 1 ≤ h)
    {z : ℤ × ℤ} (hz : InGrid (C.n + k) (l37c C h) z) (hN : annBox (2 * (h : ℤ) - 2) z)
    (hx : farB C.j h z.1 = false) (hy : farB C.k h z.2 = false) :
    (siteBox (C.n + k) (l37c C h) z).anc (C.n - 1) = parentBox C := by
  obtain ⟨p1, p2, p3⟩ := parentBox_jk C hC
  refine dybox_eq ?_ ?_ ?_
  · rw [p1]; show min (C.n - 1) (C.n + k) = C.n - 1; omega
  · rw [anc_siteBox_j hC hK hh hz hN, hx, p2]; rfl
  · rw [anc_siteBox_k hC hK hh hz hN, hy, p3]; rfl

/-- **Region constancy**: annulus sites on the same sides of the two outer-corner lines have the
same level-`(n_𝖢 - 1)` ancestor. -/
lemma anc_eq_of_region {C : DyBox} {k h : ℕ} (hC : 1 ≤ C.n) (hK : 2 ^ k = 2 * h) (hh : 1 ≤ h)
    {z z' : ℤ × ℤ} (hz : InGrid (C.n + k) (l37c C h) z) (hN : annBox (2 * (h : ℤ) - 2) z)
    (hz' : InGrid (C.n + k) (l37c C h) z') (hN' : annBox (2 * (h : ℤ) - 2) z')
    (ex : farB C.j h z.1 = farB C.j h z'.1) (ey : farB C.k h z.2 = farB C.k h z'.2) :
    (siteBox (C.n + k) (l37c C h) z).anc (C.n - 1) =
      (siteBox (C.n + k) (l37c C h) z').anc (C.n - 1) := by
  refine dybox_eq rfl ?_ ?_
  · rw [anc_siteBox_j hC hK hh hz hN, anc_siteBox_j hC hK hh hz' hN', ex]
  · rw [anc_siteBox_k hC hK hh hz hN, anc_siteBox_k hC hK hh hz' hN', ey]

/-- In the harder case every site of `annBox (2h - 2)` is a grid site. -/
lemma inGrid_of_interior {C : DyBox} {k h : ℕ} (hK : 2 ^ k = 2 * h) (hh : 1 ≤ h)
    (hint : C.largeBox ⊆ interior dzzV) {z : ℤ × ℤ} (hN : annBox (2 * (h : ℤ) - 2) z) :
    InGrid (C.n + k) (l37c C h) z := by
  obtain ⟨b1, b2, b3, b4⟩ := index_bounds_of_interior hint
  obtain ⟨a1, a2, a3, a4⟩ := hN
  have e := l37_pow C hK
  have r2 : (C.j : ℤ) + 2 ≤ 2 ^ C.n := by exact_mod_cast b2
  have r4 : (C.k : ℤ) + 2 ≤ 2 ^ C.n := by exact_mod_cast b4
  have hh' : (1 : ℤ) ≤ h := by exact_mod_cast hh
  have hj0 : (0 : ℤ) ≤ C.j := by positivity
  have hk0 : (0 : ℤ) ≤ C.k := by positivity
  simp only [InGrid, l37c]
  refine ⟨by nlinarith, ?_, by nlinarith, ?_⟩
  · rw [e]; nlinarith
  · rw [e]; nlinarith

end DZZ
end LQGMetric
