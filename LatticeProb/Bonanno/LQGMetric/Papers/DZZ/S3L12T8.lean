/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12T8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12T6

/-!
# DZZ Lemma 3.12, one-step claim: the parents of `𝖢` meet at one corner (P2-DZZ312S)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1462–1466: `𝖡_lt, 𝖡_rt, 𝖡_lb, 𝖡_rb`
are the four dyadic boxes of side `2 s_𝖢` whose closures meet the closure of `𝖢`, with
`𝖢 ⊂ 𝖡_rb`; `𝔠_parents` are the cells containing `𝖡_lt, 𝖡_rt, 𝖡_lb`. Orientation-free form used
here: the *outer corner* `z*(𝖢)` of `𝖢` (the corner of `𝖢` that is a corner of its parent box) lies
in the closure of every dyadic box of level `< n_𝖢` whose closure meets `𝖢_large`; in particular
every cell of side `> s_𝖢` meeting `𝖢_large` (DZZ's parents) contains `z*(𝖢)` in its closure.

* `outerCorner`, `outerCorner_mem_closedBox_self`;
* **`outerCorner_mem_closedBox`**, **`outerCorner_mem_of_side_lt`**.

Own elementary argument (integer arithmetic on the level-`n_𝖢` grid).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- The outer corner of `𝖢`: the corner of `𝖢` on the even grid lines of its level (a corner of
the parent box of `𝖢`). -/
def outerCorner (C : DyBox) : ℂ :=
  ⟨((C.j + C.j % 2 : ℕ) : ℝ) * C.side, ((C.k + C.k % 2 : ℕ) : ℝ) * C.side⟩

lemma outerCorner_scaled (C : DyBox) :
    (outerCorner C).re * 2 ^ C.n = ((C.j + C.j % 2 : ℕ) : ℝ) ∧
      (outerCorner C).im * 2 ^ C.n = ((C.k + C.k % 2 : ℕ) : ℝ) := by
  have e := bx_side_mul (b := C) (N := C.n) le_rfl
  simp only [Nat.sub_self, pow_zero] at e
  simp only [outerCorner]
  constructor <;> rw [mul_assoc, e, mul_one]

lemma scaled_mem_largeBox {C : DyBox} {z : ℂ} (hz : z ∈ C.largeBox) :
    (C.j : ℝ) - 1 / 2 ≤ z.re * 2 ^ C.n ∧ z.re * 2 ^ C.n ≤ C.j + 3 / 2 ∧
      (C.k : ℝ) - 1 / 2 ≤ z.im * 2 ^ C.n ∧ z.im * 2 ^ C.n ≤ C.k + 3 / 2 := by
  have e := bx_side_mul (b := C) (N := C.n) le_rfl
  simp only [Nat.sub_self, pow_zero] at e
  simp only [DyBox.largeBox, mem_ofPred_eq, abs_le, DyBox.center] at hz
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hz
  have hp : (0 : ℝ) < 2 ^ C.n := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **The parents meet at the outer corner**: a dyadic box of level `< n_𝖢` whose closure meets
`𝖢_large` contains `z*(𝖢)` in its closure. -/
theorem outerCorner_mem_closedBox {C P : DyBox} (hlt : P.n < C.n)
    (hP : (P.closedBox ∩ C.largeBox).Nonempty) : outerCorner C ∈ P.closedBox := by
  obtain ⟨z, hzP, hzL⟩ := hP
  have hle : P.n ≤ C.n := hlt.le
  obtain ⟨a1, a2, a3, a4⟩ := (bx_mem_closedBox hle).1 hzP
  obtain ⟨b1, b2, b3, b4⟩ := scaled_mem_largeBox hzL
  rw [bx_mem_closedBox hle]
  obtain ⟨e1, e2⟩ := outerCorner_scaled C
  rw [e1, e2]
  obtain ⟨d, hd⟩ : ∃ d, C.n - P.n = d + 1 := ⟨C.n - P.n - 1, by omega⟩
  rw [hd] at a1 a2 a3 a4 ⊢
  have p2 : (2 : ℕ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
  rw [p2] at a1 a2 a3 a4 ⊢
  -- integer forms
  have i1 : P.j * (2 * 2 ^ d) ≤ C.j + 1 := by
    have : ((P.j * (2 * 2 ^ d) : ℕ) : ℝ) < C.j + 2 := by linarith
    exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have i2 : C.j ≤ (P.j + 1) * (2 * 2 ^ d) := by
    have : (C.j : ℝ) < (((P.j + 1) * (2 * 2 ^ d) : ℕ) : ℝ) + 1 := by linarith
    have : C.j < (P.j + 1) * (2 * 2 ^ d) + 1 := by exact_mod_cast this
    omega
  have i3 : P.k * (2 * 2 ^ d) ≤ C.k + 1 := by
    have : ((P.k * (2 * 2 ^ d) : ℕ) : ℝ) < C.k + 2 := by linarith
    exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have i4 : C.k ≤ (P.k + 1) * (2 * 2 ^ d) := by
    have : (C.k : ℝ) < (((P.k + 1) * (2 * 2 ^ d) : ℕ) : ℝ) + 1 := by linarith
    have : C.k < (P.k + 1) * (2 * 2 ^ d) + 1 := by exact_mod_cast this
    omega
  set t := 2 ^ d
  have q1 : P.j * (2 * t) = 2 * (P.j * t) := by ring
  have q2 : (P.j + 1) * (2 * t) = 2 * ((P.j + 1) * t) := by ring
  have q3 : P.k * (2 * t) = 2 * (P.k * t) := by ring
  have q4 : (P.k + 1) * (2 * t) = 2 * ((P.k + 1) * t) := by ring
  rw [q1] at i1; rw [q2] at i2; rw [q3] at i3; rw [q4] at i4
  rw [q1, q2, q3, q4]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact_mod_cast (by omega)

/-- **DZZ's parents** (l. 1462–1466): a box of side `> s_𝖢` whose closure meets `𝖢_large` contains
the outer corner `z*(𝖢)` in its closure. -/
theorem outerCorner_mem_of_side_lt {C P : DyBox} (hs : C.side < P.side)
    (hP : (P.closedBox ∩ C.largeBox).Nonempty) : outerCorner C ∈ P.closedBox := by
  refine outerCorner_mem_closedBox ?_ hP
  by_contra hn; push Not at hn
  have : P.side ≤ C.side := by
    unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  linarith

end DZZ
end LQGMetric
