/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W3

/-!
# DZZ Lemma 3.12: geometry of the three parents (D93, packet P-5/P-8)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, l. 1462–1497:
`𝖡_lt` (diagonal to the parent `𝖡_rb ⊃ 𝖢`) and `𝖡_rt`, `𝖡_lb` (sharing an edge with `𝖡_rb`).

* `quad_facts`, `quad_eq`: integer description of the quadrant boxes;
* `diag_inter_parent`: a cell containing the diagonal quadrant and no other quadrant meets the
  parent box of `𝖢` only at `z*`.

Own elementary arguments (integer arithmetic), DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma dybox_eq {a b : DyBox} (h1 : a.n = b.n) (h2 : a.j = b.j) (h3 : a.k = b.k) : a = b := by
  obtain ⟨n, j, k, _, _⟩ := a
  obtain ⟨n', j', k', _, _⟩ := b
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

lemma quad_facts {C Q : DyBox} (hQ : IsQuad C Q) :
    Q.n + 1 = C.n ∧ 2 * Q.j ≤ C.j + C.j % 2 ∧ C.j + C.j % 2 ≤ 2 * Q.j + 2 ∧
      2 * Q.k ≤ C.k + C.k % 2 ∧ C.k + C.k % 2 ≤ 2 * Q.k + 2 ∧
      (Q.j ≠ C.j / 2 ∨ Q.k ≠ C.k / 2) := by
  have q1 := hQ.1
  obtain ⟨c1, c2, c3, c4⟩ := quad_int hQ
  refine ⟨q1, c1, c2, c3, c4, ?_⟩
  by_contra hc; push Not at hc
  apply hQ.2.2
  have e : C.n - Q.n = 1 := by omega
  refine dybox_eq (by show Q.n = min Q.n C.n; omega) ?_ ?_
  · show Q.j = C.j / 2 ^ (C.n - Q.n); rw [e, pow_one]; exact hc.1
  · show Q.k = C.k / 2 ^ (C.n - Q.n); rw [e, pow_one]; exact hc.2

lemma quad_eq {C Q Q' : DyBox} (hQ : IsQuad C Q) (hQ' : IsQuad C Q') (hj : Q.j = Q'.j)
    (hk : Q.k = Q'.k) : Q = Q' := by
  exact dybox_eq (by have := hQ.1; have := hQ'.1; omega) hj hk

/-- The parent box of `𝖢` (`𝖡_rb`). -/
def parentBox (C : DyBox) : DyBox := C.anc (C.n - 1)

lemma parentBox_jk (C : DyBox) (h : 1 ≤ C.n) :
    (parentBox C).n = C.n - 1 ∧ (parentBox C).j = C.j / 2 ∧ (parentBox C).k = C.k / 2 := by
  have e : C.n - (C.n - 1) = 1 := by omega
  refine ⟨by show min (C.n - 1) C.n = _; omega, ?_, ?_⟩
  · show C.j / 2 ^ (C.n - (C.n - 1)) = _; rw [e, pow_one]
  · show C.k / 2 ^ (C.n - (C.n - 1)) = _; rw [e, pow_one]

/-- A level-`(n_𝖢 - 1)` box of given indices around `z*` is a quadrant box. -/
lemma isQuad_mk {C : DyBox} (h : 1 ≤ C.n) (a b : ℕ) (ha : a < 2 ^ (C.n - 1))
    (hb : b < 2 ^ (C.n - 1)) (h1 : 2 * a ≤ C.j + C.j % 2) (h2 : C.j + C.j % 2 ≤ 2 * a + 2)
    (h3 : 2 * b ≤ C.k + C.k % 2) (h4 : C.k + C.k % 2 ≤ 2 * b + 2)
    (hne : a ≠ C.j / 2 ∨ b ≠ C.k / 2) : IsQuad C ⟨C.n - 1, a, b, ha, hb⟩ := by
  refine ⟨by simp only; omega, ?_, fun he => ?_⟩
  · rw [bx_mem_closedBox (N := C.n) (by simp only; omega)]
    obtain ⟨e1, e2⟩ := outerCorner_scaled C
    rw [e1, e2]
    simp only [show C.n - (C.n - 1) = 1 by omega, pow_one]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> exact_mod_cast (by omega)
  · have := parentBox_jk C h
    have hj := congrArg DyBox.j he
    have hk := congrArg DyBox.k he
    simp only at hj hk
    rw [show C.anc (C.n - 1) = parentBox C from rfl, this.2.1] at hj
    rw [show C.anc (C.n - 1) = parentBox C from rfl, this.2.2] at hk
    omega

/-- **The diagonal parent meets `𝖡_rb` only at `z*`.** -/
theorem diag_inter_parent {C Q d : DyBox} (hQ : IsQuad C Q) (hj : Q.j ≠ C.j / 2)
    (hk : Q.k ≠ C.k / 2) (hdn : d.n ≤ Q.n) (hQd : Q.closedBox ⊆ d.closedBox)
    (honly : ∀ Q', IsQuad C Q' → Q'.closedBox ⊆ d.closedBox → Q' = Q) {w : ℂ}
    (hw : w ∈ d.closedBox) (hwp : w ∈ (parentBox C).closedBox) : w = outerCorner C := by
  obtain ⟨q1, c1, c2, c3, c4, -⟩ := quad_facts hQ
  have hC1 : 1 ≤ C.n := by omega
  obtain ⟨pn, pj, pk⟩ := parentBox_jk C hC1
  set L := Q.n with hL
  have hpn : (parentBox C).n = L := by rw [pn]; omega
  obtain ⟨i1, i2, i3, i4⟩ := int_of_sub_closedBox rfl hdn hQd
  have hCj := C.hj; have hCk := C.hk
  have hpow : 2 ^ C.n = 2 * 2 ^ L := by rw [← q1, pow_succ]; ring
  set t := 2 ^ (L - d.n)
  -- the two side quadrants are not in `d`
  have side1 : ¬ (d.j * t ≤ C.j / 2 ∧ C.j / 2 + 1 ≤ (d.j + 1) * t) := by
    rintro ⟨a1, a2⟩
    have hq := isQuad_mk hC1 (C.j / 2) Q.k (by rw [show C.n - 1 = L by omega]; omega)
      (by have := Q.hk; rw [show C.n - 1 = L by omega]; exact this) (by omega) (by omega)
      (by omega) (by omega) (Or.inr hk)
    have := honly _ hq (bx_sub_closedBox (by simp only; omega) hdn
      (by exact_mod_cast a1)
      (by exact_mod_cast a2)
      (by exact_mod_cast i3)
      (by exact_mod_cast i4))
    exact hj (congrArg DyBox.j this).symm
  have side2 : ¬ (d.k * t ≤ C.k / 2 ∧ C.k / 2 + 1 ≤ (d.k + 1) * t) := by
    rintro ⟨a1, a2⟩
    have hq := isQuad_mk hC1 Q.j (C.k / 2)
      (by have := Q.hj; rw [show C.n - 1 = L by omega]; exact this)
      (by rw [show C.n - 1 = L by omega]; omega) (by omega) (by omega)
      (by omega) (by omega) (Or.inl hj)
    have := honly _ hq (bx_sub_closedBox (by simp only; omega) hdn
      (by exact_mod_cast i1)
      (by exact_mod_cast i2)
      (by exact_mod_cast a1)
      (by exact_mod_cast a2))
    exact hk (congrArg DyBox.k this).symm
  obtain ⟨w1, w2, w3, w4⟩ := (bx_mem_closedBox (N := L) hdn).1 hw
  obtain ⟨v1, v2, v3, v4⟩ := (bx_mem_closedBox (N := L) hpn.le).1 hwp
  simp only [hpn, Nat.sub_self, pow_zero, mul_one, pj, pk] at v1 v2 v3 v4
  -- integer conclusions
  have hre : ∃ V : ℕ, 2 * V = C.j + C.j % 2 ∧ (V : ℝ) ≤ w.re * 2 ^ L ∧ w.re * 2 ^ L ≤ V := by
    by_cases hc : C.j / 2 + 1 = Q.j
    · refine ⟨Q.j, by omega, ?_, ?_⟩
      · have : (d.j * t : ℕ) = Q.j := by
          have : ¬ d.j * t ≤ C.j / 2 := fun h => side1 ⟨h, by omega⟩
          omega
        rw [← this]; exact w1
      · have := v2; push_cast at this; rw [show (Q.j : ℝ) = ((C.j / 2 : ℕ) : ℝ) + 1 by
          rw [← hc]; push_cast; ring]; exact this
    · refine ⟨C.j / 2, by omega, ?_, ?_⟩
      · exact v1
      · have : (d.j + 1) * t ≤ C.j / 2 := by
          have : ¬ C.j / 2 + 1 ≤ (d.j + 1) * t := fun h => side1 ⟨by omega, h⟩
          omega
        exact w2.trans (by exact_mod_cast this)
  have him : ∃ V : ℕ, 2 * V = C.k + C.k % 2 ∧ (V : ℝ) ≤ w.im * 2 ^ L ∧ w.im * 2 ^ L ≤ V := by
    by_cases hc : C.k / 2 + 1 = Q.k
    · refine ⟨Q.k, by omega, ?_, ?_⟩
      · have : (d.k * t : ℕ) = Q.k := by
          have : ¬ d.k * t ≤ C.k / 2 := fun h => side2 ⟨h, by omega⟩
          omega
        rw [← this]; exact w3
      · have := v4; push_cast at this; rw [show (Q.k : ℝ) = ((C.k / 2 : ℕ) : ℝ) + 1 by
          rw [← hc]; push_cast; ring]; exact this
    · refine ⟨C.k / 2, by omega, ?_, ?_⟩
      · exact v3
      · have : (d.k + 1) * t ≤ C.k / 2 := by
          have : ¬ C.k / 2 + 1 ≤ (d.k + 1) * t := fun h => side2 ⟨by omega, h⟩
          omega
        exact w4.trans (by exact_mod_cast this)
  obtain ⟨V, hV, a1, a2⟩ := hre
  obtain ⟨U, hU, b1, b2⟩ := him
  obtain ⟨e1, e2⟩ := outerCorner_scaled C
  have hp : (0 : ℝ) < 2 ^ L := by positivity
  have hpow' : (2 : ℝ) ^ C.n = 2 * 2 ^ L := by exact_mod_cast hpow
  have hV' : ((C.j + C.j % 2 : ℕ) : ℝ) = 2 * V := by exact_mod_cast hV.symm
  have hU' : ((C.k + C.k % 2 : ℕ) : ℝ) = 2 * U := by exact_mod_cast hU.symm
  rw [hV', hpow'] at e1; rw [hU', hpow'] at e2
  apply Complex.ext
  · have : w.re * 2 ^ L = (outerCorner C).re * 2 ^ L := by nlinarith
    exact mul_right_cancel₀ hp.ne' this
  · have : w.im * 2 ^ L = (outerCorner C).im * 2 ^ L := by nlinarith
    exact mul_right_cancel₀ hp.ne' this

end DZZ
end LQGMetric
