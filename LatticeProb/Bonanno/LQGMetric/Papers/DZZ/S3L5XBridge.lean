/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5XBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3D6
import Mathlib.Analysis.Convex.PathConnected

/-!
# DZZ Def 3.6 enclosures separate grid paths (P2-DEC84, decision D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`), Definition 3.6 and the remark after
it (l. 920–939): a sequence of boxes *encloses* `B` if it separates `B` from `𝕍 ∩ ∂B_large` in `𝕍`
(`EnclosesBox`, continuous paths). Decision D84 keeps this path-based definition; the proof of
the crossing claim of Lemma 3.5 (l. 1071–1079) works on a fine dyadic grid (level `N`), and this
file is the bridge between the two:

* `SqAdj`: two boxes of the same level sharing an edge (4-adjacency of grid squares).
* `SqFree U s`: the square `s` lies in no box of `U`; `SqSep N C U`: every 4-path of level-`N`
  squares avoiding the boxes of `U` that starts in `C` stays in `C_large`.
* **`sqSep_of_enclosesBox`**: `EnclosesBox C U` (boxes of level `≤ N`, `n_C + 1 ≤ N`) gives
  `SqSep N C U`. Proof: the polygonal path through the centres of the squares avoids every
  closed box of `U` (integer arithmetic on the level-`N` grid), leaves `C_large` (the centre of
  a square not contained in the aligned box `C_large` lies outside it), so it meets
  `∂C_large`; truncated there it contradicts `EnclosesBox`.

Own elementary argument (DZZ use the separation property without comment); DEVIATIONS D84.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- Two boxes of the same level sharing an edge (4-adjacent grid squares). -/
def SqAdj (s t : DyBox) : Prop :=
  s.n = t.n ∧ ((s.j = t.j ∧ (s.k + 1 = t.k ∨ t.k + 1 = s.k)) ∨
    (s.k = t.k ∧ (s.j + 1 = t.j ∨ t.j + 1 = s.j)))

lemma SqAdj.symm {s t : DyBox} (h : SqAdj s t) : SqAdj t s := by
  obtain ⟨hn, h⟩ := h
  refine ⟨hn.symm, ?_⟩
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨h1.symm, Or.inr h2⟩
  · exact Or.inl ⟨h1.symm, Or.inl h2⟩
  · exact Or.inr ⟨h1.symm, Or.inr h2⟩
  · exact Or.inr ⟨h1.symm, Or.inl h2⟩

/-- The square `s` is contained in no box of `U`. -/
def SqFree (U : Set DyBox) (s : DyBox) : Prop := ∀ b ∈ U, ¬ s.closedBox ⊆ b.closedBox

/-- A step of a 4-path of squares avoiding the boxes of `U`. -/
def SqStep (U : Set DyBox) (s t : DyBox) : Prop := SqAdj s t ∧ SqFree U t

/-- Discrete separation at level `N`: every 4-path of level-`N` squares avoiding the boxes of `U`
that starts in `C` stays in `C_large`. -/
def SqSep (N : ℕ) (C : DyBox) (U : Set DyBox) : Prop :=
  ∀ s t : DyBox, s.n = N → s.closedBox ⊆ C.closedBox → SqFree U s →
    Relation.ReflTransGen (SqStep U) s t → t.closedBox ⊆ C.largeBox

/-! ### Scaled coordinates on the level-`N` grid -/

lemma bx_side_mul {b : DyBox} {N : ℕ} (h : b.n ≤ N) :
    b.side * (2 : ℝ) ^ N = (2 : ℝ) ^ (N - b.n) := by
  unfold DyBox.side
  rw [show N = (N - b.n) + b.n by omega, pow_add, ← mul_assoc, mul_comm, ← mul_assoc,
    ← mul_pow, show (2 : ℝ) * 2⁻¹ = 1 by norm_num, one_pow, one_mul]
  congr 1; omega

lemma bx_scale_le {a x : ℝ} (N : ℕ) : a ≤ x ↔ a * (2 : ℝ) ^ N ≤ x * 2 ^ N :=
  (mul_le_mul_iff_of_pos_right (by positivity)).symm

/-- A closed box of level `≤ N` in scaled coordinates. -/
lemma bx_mem_closedBox {b : DyBox} {N : ℕ} (hb : b.n ≤ N) {z : ℂ} :
    z ∈ b.closedBox ↔ ((b.j * 2 ^ (N - b.n) : ℕ) : ℝ) ≤ z.re * 2 ^ N ∧
      z.re * 2 ^ N ≤ (((b.j + 1) * 2 ^ (N - b.n) : ℕ) : ℝ) ∧
      ((b.k * 2 ^ (N - b.n) : ℕ) : ℝ) ≤ z.im * 2 ^ N ∧
      z.im * 2 ^ N ≤ (((b.k + 1) * 2 ^ (N - b.n) : ℕ) : ℝ) := by
  have e := bx_side_mul hb
  simp only [DyBox.closedBox, mem_ofPred_eq]
  push_cast
  rw [bx_scale_le N, bx_scale_le (a := z.re) N, bx_scale_le (x := z.im) N,
    bx_scale_le (a := z.im) N]
  simp only [mul_assoc, e]

/-- `C_large` in scaled coordinates (`n_C + 1 ≤ N`). -/
lemma bx_mem_largeBox {C : DyBox} {N : ℕ} (hC : C.n + 1 ≤ N) {z : ℂ} :
    z ∈ C.largeBox ↔ (((2 * C.j - 1 : ℤ) * 2 ^ (N - C.n - 1) : ℤ) : ℝ) ≤ z.re * 2 ^ N ∧
      z.re * 2 ^ N ≤ (((2 * C.j + 3 : ℤ) * 2 ^ (N - C.n - 1) : ℤ) : ℝ) ∧
      (((2 * C.k - 1 : ℤ) * 2 ^ (N - C.n - 1) : ℤ) : ℝ) ≤ z.im * 2 ^ N ∧
      z.im * 2 ^ N ≤ (((2 * C.k + 3 : ℤ) * 2 ^ (N - C.n - 1) : ℤ) : ℝ) := by
  have e := bx_side_mul (b := C) (N := N) (by omega)
  have e2 : (2 : ℝ) ^ (N - C.n) = 2 * 2 ^ (N - C.n - 1) := by
    rw [← pow_succ']; congr 1; omega
  simp only [DyBox.largeBox, DyBox.center, mem_ofPred_eq, abs_le]
  push_cast
  constructor
  · rintro ⟨⟨a1, a2⟩, b1, b2⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [pow_pos (two_pos (α := ℝ)) N]
  · rintro ⟨a1, a2, b1, b2⟩
    have hp : (0 : ℝ) < 2 ^ N := by positivity
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [bx_scale_le N]; nlinarith
    · rw [bx_scale_le N]; nlinarith
    · rw [bx_scale_le N]; nlinarith
    · rw [bx_scale_le N]; nlinarith

lemma bx_center_re {s : DyBox} {N : ℕ} (hs : s.n = N) :
    s.center.re * 2 ^ N = (s.j : ℝ) + 1 / 2 := by
  have e := bx_side_mul (b := s) (N := N) hs.le
  simp only [DyBox.center, mul_assoc, e, hs, Nat.sub_self, pow_zero, mul_one]

lemma bx_center_im {s : DyBox} {N : ℕ} (hs : s.n = N) :
    s.center.im * 2 ^ N = (s.k : ℝ) + 1 / 2 := by
  have e := bx_side_mul (b := s) (N := N) hs.le
  simp only [DyBox.center, mul_assoc, e, hs, Nat.sub_self, pow_zero, mul_one]

/-- A level-`N` square lies in a scaled integer rectangle if its indices do. -/
lemma bx_sub_of_int {s : DyBox} {N : ℕ} (hs : s.n = N) {X : Set ℂ} {A B C D : ℤ}
    (hX : ∀ z : ℂ, (A : ℝ) ≤ z.re * 2 ^ N → z.re * 2 ^ N ≤ B → (C : ℝ) ≤ z.im * 2 ^ N →
      z.im * 2 ^ N ≤ D → z ∈ X)
    (h1 : A ≤ s.j) (h2 : (s.j : ℤ) + 1 ≤ B) (h3 : C ≤ s.k) (h4 : (s.k : ℤ) + 1 ≤ D) :
    s.closedBox ⊆ X := by
  intro z hz
  rw [bx_mem_closedBox (N := N) hs.le, hs, Nat.sub_self, pow_zero] at hz
  obtain ⟨a1, a2, a3, a4⟩ := hz
  push_cast at a1 a2 a3 a4
  have c1 : (A : ℝ) ≤ s.j := by exact_mod_cast h1
  have c2 : (s.j : ℝ) + 1 ≤ B := by exact_mod_cast h2
  have c3 : (C : ℝ) ≤ s.k := by exact_mod_cast h3
  have c4 : (s.k : ℝ) + 1 ≤ D := by exact_mod_cast h4
  exact hX z (by linarith) (by linarith) (by linarith) (by linarith)

lemma int_le_of_lt_add_one' {A p : ℤ} {x : ℝ} (h1 : (A : ℝ) ≤ x) (h2 : x < p + 1) : A ≤ p := by
  by_contra h
  have : (p : ℝ) + 1 ≤ A := by exact_mod_cast (show p + 1 ≤ A by omega)
  linarith

lemma int_add_one_le' {B p : ℤ} {x : ℝ} (h1 : x ≤ B) (h2 : (p : ℝ) < x) : p + 1 ≤ B := by
  by_contra h
  have : (B : ℝ) ≤ p := by exact_mod_cast (show B ≤ p by omega)
  linarith

/-- One coordinate of a segment between the centres of two adjacent squares `p, p + 1`. -/
lemma coord_adj {A B p : ℤ} {x : ℝ} (hAB : A < B) (hx1 : (p : ℝ) + 1 / 2 ≤ x)
    (hx2 : x ≤ p + 3 / 2) (hA : (A : ℝ) ≤ x) (hB : x ≤ B) :
    (A ≤ p ∧ p + 1 ≤ B) ∨ (A ≤ p + 1 ∧ p + 1 + 1 ≤ B) := by
  have a1 : A ≤ p + 1 := int_le_of_lt_add_one' hA (by push_cast; linarith)
  have b1 : p + 1 ≤ B := int_add_one_le' hB (by linarith)
  omega

lemma coord_eq {A B p : ℤ} {x : ℝ} (hx : x = p + 1 / 2) (hA : (A : ℝ) ≤ x) (hB : x ≤ B) :
    A ≤ p ∧ p + 1 ≤ B :=
  ⟨int_le_of_lt_add_one' hA (by linarith), int_add_one_le' hB (by linarith)⟩

lemma seg_coord {x y z : ℂ} (hz : z ∈ segment ℝ x y) :
    (min x.re y.re ≤ z.re ∧ z.re ≤ max x.re y.re) ∧ (min x.im y.im ≤ z.im ∧ z.im ≤ max x.im y.im) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  obtain rfl : a = 1 - b := by linarith
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rcases le_total x.re y.re with h | h
    · rw [min_eq_left h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
    · rw [min_eq_right h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
  · rcases le_total x.re y.re with h | h
    · rw [max_eq_right h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
    · rw [max_eq_left h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
  · rcases le_total x.im y.im with h | h
    · rw [min_eq_left h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
    · rw [min_eq_right h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
  · rcases le_total x.im y.im with h | h
    · rw [max_eq_right h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
    · rw [max_eq_left h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h)]

/-- Integer bounds of a closed box of level `≤ N`. -/
lemma bx_closedBox_int {b : DyBox} {N : ℕ} (hb : b.n ≤ N) {z : ℂ} (hz : z ∈ b.closedBox) :
    (((b.j * 2 ^ (N - b.n) : ℕ) : ℤ) : ℝ) ≤ z.re * 2 ^ N ∧
      z.re * 2 ^ N ≤ ((((b.j + 1) * 2 ^ (N - b.n) : ℕ) : ℤ) : ℝ) ∧
      (((b.k * 2 ^ (N - b.n) : ℕ) : ℤ) : ℝ) ≤ z.im * 2 ^ N ∧
      z.im * 2 ^ N ≤ ((((b.k + 1) * 2 ^ (N - b.n) : ℕ) : ℤ) : ℝ) := by
  simp only [Int.cast_natCast]
  exact (bx_mem_closedBox hb).1 hz

lemma bx_sub_closedBox {s b : DyBox} {N : ℕ} (hs : s.n = N) (hb : b.n ≤ N)
    (h1 : ((b.j * 2 ^ (N - b.n) : ℕ) : ℤ) ≤ s.j)
    (h2 : (s.j : ℤ) + 1 ≤ (((b.j + 1) * 2 ^ (N - b.n) : ℕ) : ℤ))
    (h3 : ((b.k * 2 ^ (N - b.n) : ℕ) : ℤ) ≤ s.k)
    (h4 : (s.k : ℤ) + 1 ≤ (((b.k + 1) * 2 ^ (N - b.n) : ℕ) : ℤ)) :
    s.closedBox ⊆ b.closedBox :=
  bx_sub_of_int hs (fun z a1 a2 a3 a4 => (bx_mem_closedBox hb).2 (by
    simp only [Int.cast_natCast] at a1 a2 a3 a4; exact ⟨a1, a2, a3, a4⟩)) h1 h2 h3 h4

lemma bx_lt {b : DyBox} {N : ℕ} (i : ℕ) :
    ((i * 2 ^ (N - b.n) : ℕ) : ℤ) < (((i + 1) * 2 ^ (N - b.n) : ℕ) : ℤ) := by
  have : 0 < 2 ^ (N - b.n) := by positivity
  push_cast; nlinarith

/-- The segment between the centres of a square and its right neighbour avoids every closed box
containing neither square. -/
lemma seg_avoid_right {s t b : DyBox} {N : ℕ} (hs : s.n = N) (ht : t.n = N) (hj : s.j + 1 = t.j)
    (hk : s.k = t.k) (hb : b.n ≤ N) (hfs : ¬ s.closedBox ⊆ b.closedBox)
    (hft : ¬ t.closedBox ⊆ b.closedBox) {z : ℂ} (hz : z ∈ segment ℝ s.center t.center) :
    z ∉ b.closedBox := by
  intro hzb
  obtain ⟨a1, a2, a3, a4⟩ := bx_closedBox_int hb hzb
  obtain ⟨⟨r1, r2⟩, i1, i2⟩ := seg_coord hz
  have es := bx_center_re hs
  have et := bx_center_re ht
  have fs := bx_center_im hs
  have ft := bx_center_im ht
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have htj : (t.j : ℝ) = s.j + 1 := by rw [← hj]; push_cast; ring
  have htk : (t.k : ℝ) = s.k := by rw [hk]
  have hre : s.center.re ≤ t.center.re := by
    rw [bx_scale_le N, es, et, htj]; linarith
  have him : s.center.im = t.center.im := by
    have : s.center.im * 2 ^ N = t.center.im * 2 ^ N := by rw [fs, ft, htk]
    exact mul_right_cancel₀ hpos.ne' this
  rw [min_eq_left hre] at r1
  rw [max_eq_right hre] at r2
  rw [← him, min_self] at i1
  rw [← him, max_self] at i2
  have zim : z.im * 2 ^ N = (s.k : ℝ) + 1 / 2 := by rw [le_antisymm i2 i1, fs]
  have zr1 : ((s.j : ℤ) : ℝ) + 1 / 2 ≤ z.re * 2 ^ N := by
    push_cast; rw [← es]; exact (mul_le_mul_iff_of_pos_right hpos).2 r1
  have zr2 : z.re * 2 ^ N ≤ ((s.j : ℤ) : ℝ) + 3 / 2 := by
    have := (mul_le_mul_iff_of_pos_right hpos).2 r2
    rw [et, htj] at this; push_cast; linarith
  have ck := coord_eq (p := (s.k : ℤ)) (by push_cast; exact zim) a3 a4
  rcases coord_adj (bx_lt (b := b) b.j) zr1 zr2 a1 a2 with ⟨c1, c2⟩ | ⟨c1, c2⟩
  · exact hfs (bx_sub_closedBox hs hb c1 c2 ck.1 ck.2)
  · refine hft (bx_sub_closedBox ht hb ?_ ?_ ?_ ?_)
    · rw [← hj]; push_cast; exact c1
    · rw [← hj]; push_cast; exact c2
    · rw [← hk]; exact ck.1
    · rw [← hk]; exact ck.2

/-- The same for a square and its upper neighbour. -/
lemma seg_avoid_up {s t b : DyBox} {N : ℕ} (hs : s.n = N) (ht : t.n = N) (hj : s.j = t.j)
    (hk : s.k + 1 = t.k) (hb : b.n ≤ N) (hfs : ¬ s.closedBox ⊆ b.closedBox)
    (hft : ¬ t.closedBox ⊆ b.closedBox) {z : ℂ} (hz : z ∈ segment ℝ s.center t.center) :
    z ∉ b.closedBox := by
  intro hzb
  obtain ⟨a1, a2, a3, a4⟩ := bx_closedBox_int hb hzb
  obtain ⟨⟨r1, r2⟩, i1, i2⟩ := seg_coord hz
  have es := bx_center_re hs
  have et := bx_center_re ht
  have fs := bx_center_im hs
  have ft := bx_center_im ht
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have htk : (t.k : ℝ) = s.k + 1 := by rw [← hk]; push_cast; ring
  have htj : (t.j : ℝ) = s.j := by rw [hj]
  have him : s.center.im ≤ t.center.im := by
    rw [bx_scale_le N, fs, ft, htk]; linarith
  have hre : s.center.re = t.center.re := by
    have : s.center.re * 2 ^ N = t.center.re * 2 ^ N := by rw [es, et, htj]
    exact mul_right_cancel₀ hpos.ne' this
  rw [min_eq_left him] at i1
  rw [max_eq_right him] at i2
  rw [← hre, min_self] at r1
  rw [← hre, max_self] at r2
  have zre : z.re * 2 ^ N = (s.j : ℝ) + 1 / 2 := by rw [le_antisymm r2 r1, es]
  have zi1 : ((s.k : ℤ) : ℝ) + 1 / 2 ≤ z.im * 2 ^ N := by
    push_cast; rw [← fs]; exact (mul_le_mul_iff_of_pos_right hpos).2 i1
  have zi2 : z.im * 2 ^ N ≤ ((s.k : ℤ) : ℝ) + 3 / 2 := by
    have := (mul_le_mul_iff_of_pos_right hpos).2 i2
    rw [ft, htk] at this; push_cast; linarith
  have cj := coord_eq (p := (s.j : ℤ)) (by push_cast; exact zre) a1 a2
  rcases coord_adj (bx_lt (b := b) b.k) zi1 zi2 a3 a4 with ⟨c1, c2⟩ | ⟨c1, c2⟩
  · exact hfs (bx_sub_closedBox hs hb cj.1 cj.2 c1 c2)
  · refine hft (bx_sub_closedBox ht hb ?_ ?_ ?_ ?_)
    · rw [← hj]; exact cj.1
    · rw [← hj]; exact cj.2
    · rw [← hk]; push_cast; exact c1
    · rw [← hk]; push_cast; exact c2

/-- The segment between the centres of two adjacent level-`N` squares avoids every closed box of
level `≤ N` containing neither square. -/
lemma seg_avoid {s t b : DyBox} {N : ℕ} (hs : s.n = N) (hst : SqAdj s t) (hb : b.n ≤ N)
    (hfs : ¬ s.closedBox ⊆ b.closedBox) (hft : ¬ t.closedBox ⊆ b.closedBox) {z : ℂ}
    (hz : z ∈ segment ℝ s.center t.center) : z ∉ b.closedBox := by
  have ht : t.n = N := hst.1 ▸ hs
  rcases hst.2 with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact seg_avoid_up hs ht h1 h2 hb hfs hft hz
  · exact seg_avoid_up ht hs h1.symm h2 hb hft hfs (by rwa [segment_symm])
  · exact seg_avoid_right hs ht h2 h1 hb hfs hft hz
  · exact seg_avoid_right ht hs h2 h1.symm hb hft hfs (by rwa [segment_symm])

lemma center_mem_closedBox' (b : DyBox) : b.center ∈ b.closedBox := by
  have : 0 < b.side := by unfold DyBox.side; positivity
  simp only [DyBox.center, DyBox.closedBox, mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma closedBox_sub_dzzV' (b : DyBox) : b.closedBox ⊆ dzzV := by
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hs : 0 < b.side := by unfold DyBox.side; positivity
  have hjs : ((b.j : ℝ) + 1) * b.side ≤ 1 := by
    have h := b.hj
    have : ((b.j : ℝ) + 1) ≤ 2 ^ b.n := by exact_mod_cast h
    calc ((b.j : ℝ) + 1) * b.side ≤ 2 ^ b.n * b.side := by gcongr
      _ = 1 := by unfold DyBox.side; rw [← mul_pow]; norm_num
  have hks : ((b.k : ℝ) + 1) * b.side ≤ 1 := by
    have h := b.hk
    have : ((b.k : ℝ) + 1) ≤ 2 ^ b.n := by exact_mod_cast h
    calc ((b.k : ℝ) + 1) * b.side ≤ 2 ^ b.n * b.side := by gcongr
      _ = 1 := by unfold DyBox.side; rw [← mul_pow]; norm_num
  exact ⟨le_trans (by positivity) h1, h2.trans hjs, le_trans (by positivity) h3, h4.trans hks⟩

/-- A level-`N` square whose centre lies in a closed box of level `≤ N` lies in that box. -/
lemma sub_of_center_mem {s b : DyBox} {N : ℕ} (hs : s.n = N) (hb : b.n ≤ N)
    (h : s.center ∈ b.closedBox) : s.closedBox ⊆ b.closedBox := by
  obtain ⟨a1, a2, a3, a4⟩ := bx_closedBox_int hb h
  have c1 := coord_eq (p := (s.j : ℤ)) (by push_cast; exact bx_center_re hs) a1 a2
  have c2 := coord_eq (p := (s.k : ℤ)) (by push_cast; exact bx_center_im hs) a3 a4
  exact bx_sub_closedBox hs hb c1.1 c1.2 c2.1 c2.2

/-- A level-`N` square whose centre lies in `C_large` lies in `C_large` (`n_C + 1 ≤ N`). -/
lemma sub_largeBox_of_center_mem {s C : DyBox} {N : ℕ} (hs : s.n = N) (hC : C.n + 1 ≤ N)
    (h : s.center ∈ C.largeBox) : s.closedBox ⊆ C.largeBox := by
  obtain ⟨a1, a2, a3, a4⟩ := (bx_mem_largeBox hC).1 h
  have c1 := coord_eq (p := (s.j : ℤ)) (by push_cast; exact bx_center_re hs) a1 a2
  have c2 := coord_eq (p := (s.k : ℤ)) (by push_cast; exact bx_center_im hs) a3 a4
  exact bx_sub_of_int hs (fun z b1 b2 b3 b4 => (bx_mem_largeBox hC).2 ⟨b1, b2, b3, b4⟩)
    c1.1 c1.2 c2.1 c2.2

lemma seg_mem_dzzV {x y z : ℂ} (hx : x ∈ dzzV) (hy : y ∈ dzzV) (hz : z ∈ segment ℝ x y) :
    z ∈ dzzV := by
  obtain ⟨⟨r1, r2⟩, i1, i2⟩ := seg_coord hz
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  exact ⟨le_trans (le_min x1 y1) r1, r2.trans (max_le x2 y2), le_trans (le_min x3 y3) i1,
    i2.trans (max_le x4 y4)⟩

lemma closedBox_sub_largeBox' (C : DyBox) : C.closedBox ⊆ C.largeBox := by
  intro z hz
  obtain ⟨c1, c2, c3, c4⟩ := hz
  have hs0 : 0 < C.side := by unfold DyBox.side; positivity
  simp only [DyBox.largeBox, DyBox.center, mem_ofPred_eq, abs_le]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- **Bridge (D84)**: an enclosure in the sense of DZZ Def 3.6 (`EnclosesBox`, continuous paths)
separates 4-paths of level-`N` squares, for boxes of level `≤ N` and `n_C + 1 ≤ N`. -/
theorem sqSep_of_enclosesBox {C : DyBox} {U : Set DyBox} {N : ℕ} (hE : EnclosesBox C U)
    (hU : ∀ b ∈ U, b.n ≤ N) (hC : C.n + 1 ≤ N) : SqSep N C U := by
  intro s t hs hsC hsf hrt
  by_contra htC
  set F : Set ℂ := {z | z ∈ dzzV ∧ ∀ b ∈ U, z ∉ b.closedBox} with hF
  have hcF : ∀ a : DyBox, a.n = N → SqFree U a → a.center ∈ F := fun a ha hfa =>
    ⟨closedBox_sub_dzzV' a (center_mem_closedBox' a),
      fun b hb hcb => hfa b hb (sub_of_center_mem ha (hU b hb) hcb)⟩
  have key : ∀ t', Relation.ReflTransGen (SqStep U) s t' →
      t'.n = N ∧ SqFree U t' ∧ JoinedIn F s.center t'.center := by
    intro t' h
    induction h with
    | refl => exact ⟨hs, hsf, JoinedIn.refl (hcF s hs hsf)⟩
    | tail _ hac ih =>
      obtain ⟨ha, hfa, hJ⟩ := ih
      rename_i a c _
      have hc : c.n = N := hac.1.1 ▸ ha
      refine ⟨hc, hac.2, hJ.trans (JoinedIn.of_segment_subset fun z hz => ⟨?_, ?_⟩)⟩
      · exact seg_mem_dzzV (closedBox_sub_dzzV' a (center_mem_closedBox' a))
          (closedBox_sub_dzzV' c (center_mem_closedBox' c)) hz
      · intro b hb
        exact seg_avoid ha hac.1 (hU b hb) (hfa b hb) (hac.2 b hb) hz
  obtain ⟨ht, -, hJ⟩ := key t hrt
  set p : C(unitInterval, ℂ) := hJ.somePath.toContinuousMap with hpdef
  have hpF : ∀ x, p x ∈ F := fun x => hJ.somePath_mem x
  have hp0 : p 0 = s.center := hJ.somePath.source
  have hp1 : p 1 = t.center := hJ.somePath.target
  have hfr : (frontier (p ⁻¹' C.largeBox)).Nonempty := by
    refine nonempty_frontier_iff.2 ⟨⟨0, ?_⟩, fun h => ?_⟩
    · show p 0 ∈ C.largeBox
      rw [hp0]
      exact closedBox_sub_largeBox' C (hsC (center_mem_closedBox' s))
    · have h1 : (1 : unitInterval) ∈ p ⁻¹' C.largeBox := h ▸ mem_univ _
      simp only [mem_preimage, hp1] at h1
      exact htC (sub_largeBox_of_center_mem ht hC h1)
  obtain ⟨τ, hτ⟩ := hfr
  have hτ' : p τ ∈ frontier C.largeBox := p.continuous.frontier_preimage_subset _ hτ
  let q : C(unitInterval, ℂ) :=
    ⟨fun x => p ⟨τ.1 * x.1, unitInterval.mul_mem τ.2 x.2⟩, by fun_prop⟩
  have hq0 : q 0 = s.center := by
    rw [← hp0]; show p _ = p _; congr 1; apply Subtype.ext; simp
  have hq1 : q 1 = p τ := by
    show p _ = p _; congr 1; apply Subtype.ext; simp
  obtain ⟨x, b, hb, hx⟩ := hE q (fun x => (hpF _).1)
    (by rw [hq0]; exact hsC (center_mem_closedBox' s)) (by rw [hq1]; exact hτ')
  exact (hpF _).2 b hb hx

end DZZ
end LQGMetric
