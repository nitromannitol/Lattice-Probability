/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5W1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5YMain

/-!
# Walled DZZ Lemma 3.5, W1: the dyadic sub-boxes of a wall box as a copy of the dyadic grid of `𝕍`
(P2-DZZL35W, packet P-317K-L35, decisions D117/D123)

For a dyadic wall `K = B̄w` (DZZ Remark 5.2, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2281–2284;
D123: `S = cellsInside Bw`), the dyadic boxes contained in `B̄w` are the images of the dyadic boxes
of `𝕍` under the similarity `wHom Bw : z ↦ c_{Bw} + s_{Bw} z` (`c` the lower-left corner). This
file sets up the dictionary, so that the deterministic part of the proved Lemma 3.5
(`l35Crossing_holds`, S3L5YMain, D84) and the percolation geometry (S3L7Fin*, D72) transfer to the
wall by pulling the box-mass function back (`m ∘ wEmb Bw`), instead of being re-proved.

* `wEmb Bw b`: the sub-box of `Bw` at relative level `b.n`, column `b.j`, row `b.k`;
* `wHom Bw`: the similarity as a homeomorphism of `ℂ`; `closedBox_wEmb`, `side_wEmb`,
  `center_wEmb`, `largeBox_wEmb`;
* `wEmb_anc_add`, `wEmb_anc_le`: ancestors; `closedBox_wEmb_sub`, `exists_wEmb_of_sub`
  (`cellsInside Bw` is the range of `wEmb Bw`);
* `isCell_wEmb_iff`: cells of `m` inside `B̄w` are the cells of `m ∘ wEmb Bw` when `Bw` and its
  ancestors are split; `neighbour_wEmb_iff`; `mem_wEmb_iff` (points not on the top/right edge).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

lemma wEmb_lt {a n b m : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ m) : a * 2 ^ m + b < 2 ^ (n + m) := by
  have h1 : (a + 1) * 2 ^ m ≤ 2 ^ n * 2 ^ m := Nat.mul_le_mul_right _ ha
  rw [pow_add]; nlinarith

/-- The dyadic sub-box of `Bw` corresponding to the dyadic box `b` of `𝕍`. -/
def wEmb (Bw b : DyBox) : DyBox :=
  ⟨Bw.n + b.n, Bw.j * 2 ^ b.n + b.j, Bw.k * 2 ^ b.n + b.k, wEmb_lt Bw.hj b.hj, wEmb_lt Bw.hk b.hk⟩

lemma wEmb_injective (Bw : DyBox) : Function.Injective (wEmb Bw) := by
  intro b b' h
  have hn : b.n = b'.n := by have := congrArg DyBox.n h; simp only [wEmb] at this; omega
  have hj := congrArg DyBox.j h
  have hk := congrArg DyBox.k h
  simp only [wEmb, hn] at hj hk
  exact DyBox.ext hn (Nat.add_left_cancel hj) (Nat.add_left_cancel hk)

lemma wside_pos (b : DyBox) : 0 < b.side := by unfold DyBox.side; positivity

lemma side_wEmb (Bw b : DyBox) : (wEmb Bw b).side = Bw.side * b.side := by
  simp only [DyBox.side, wEmb, pow_add]

lemma two_pow_mul_side (b : DyBox) : (2 : ℝ) ^ b.n * b.side = 1 := by
  unfold DyBox.side; rw [← mul_pow]; norm_num

/-- The lower-left corner of `Bw`. -/
def wOff (Bw : DyBox) : ℂ := ⟨Bw.j * Bw.side, Bw.k * Bw.side⟩

/-- The similarity `z ↦ c_{Bw} + s_{Bw} z` of `𝕍` onto `B̄w`. -/
def wHom (Bw : DyBox) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ ((Bw.side : ℝ) : ℂ) (by exact_mod_cast (wside_pos Bw).ne')).trans
    (Homeomorph.addRight (wOff Bw))

lemma wHom_apply (Bw : DyBox) (z : ℂ) : wHom Bw z = (Bw.side : ℂ) * z + wOff Bw := rfl

@[simp] lemma wHom_re (Bw : DyBox) (z : ℂ) : (wHom Bw z).re = Bw.j * Bw.side + Bw.side * z.re := by
  simp [wHom_apply, wOff]; ring

@[simp] lemma wHom_im (Bw : DyBox) (z : ℂ) : (wHom Bw z).im = Bw.k * Bw.side + Bw.side * z.im := by
  simp [wHom_apply, wOff]; ring

lemma wHom_mem_closedBox {Bw b : DyBox} {z : ℂ} :
    wHom Bw z ∈ (wEmb Bw b).closedBox ↔ z ∈ b.closedBox := by
  have hP := two_pow_mul_side b
  have hs := wside_pos Bw
  have e1 : ∀ J t : ℝ, (J * 2 ^ b.n + t) * (Bw.side * b.side) = J * Bw.side + Bw.side * (t * b.side) :=
    fun J t => by linear_combination (J * Bw.side) * hP
  simp only [DyBox.closedBox, mem_ofPred_eq, wHom_re, wHom_im, side_wEmb]
  simp only [wEmb]
  push_cast
  rw [add_assoc (_ * _) (b.j : ℝ) 1, add_assoc (_ * _) (b.k : ℝ) 1, e1, e1, e1, e1]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma image_eq_of_mem_iff {f : ℂ ≃ₜ ℂ} {X Y : Set ℂ} (h : ∀ z, f z ∈ Y ↔ z ∈ X) : Y = f '' X := by
  ext w
  constructor
  · intro hw; exact ⟨f.symm w, (h _).1 (by simpa using hw), by simp⟩
  · rintro ⟨z, hz, rfl⟩; exact (h z).2 hz

lemma closedBox_wEmb (Bw b : DyBox) : (wEmb Bw b).closedBox = wHom Bw '' b.closedBox :=
  image_eq_of_mem_iff fun _ => wHom_mem_closedBox

lemma center_wEmb (Bw b : DyBox) : (wEmb Bw b).center = wHom Bw b.center := by
  have hP := two_pow_mul_side b
  apply Complex.ext
  · simp only [DyBox.center, wHom_re, side_wEmb]; simp only [wEmb]; push_cast
    linear_combination (Bw.j * Bw.side) * hP
  · simp only [DyBox.center, wHom_im, side_wEmb]; simp only [wEmb]; push_cast
    linear_combination (Bw.k * Bw.side) * hP

lemma largeBox_wEmb (Bw b : DyBox) : (wEmb Bw b).largeBox = wHom Bw '' b.largeBox := by
  refine image_eq_of_mem_iff fun z => ?_
  have hs := wside_pos Bw
  simp only [DyBox.largeBox, mem_ofPred_eq, center_wEmb, wHom_re, wHom_im, side_wEmb]
  rw [show Bw.j * Bw.side + Bw.side * z.re - (Bw.j * Bw.side + Bw.side * b.center.re) =
      Bw.side * (z.re - b.center.re) by ring,
    show Bw.k * Bw.side + Bw.side * z.im - (Bw.k * Bw.side + Bw.side * b.center.im) =
      Bw.side * (z.im - b.center.im) by ring, abs_mul, abs_mul, abs_of_pos hs,
    mul_le_mul_iff_right₀ hs, mul_le_mul_iff_right₀ hs]

/-! ### Ancestors and containment -/

lemma wEmb_anc_add (Bw b : DyBox) (i : ℕ) : (wEmb Bw b).anc (Bw.n + i) = wEmb Bw (b.anc i) := by
  rcases le_total i b.n with h | h
  · have hm : min i b.n = i := min_eq_left h
    have hpe : (2 : ℕ) ^ b.n = 2 ^ (b.n - i) * 2 ^ i := by rw [← pow_add]; congr 1; omega
    have hsub : Bw.n + b.n - (Bw.n + i) = b.n - i := by omega
    have hpos : 0 < 2 ^ (b.n - i) := by positivity
    ext
    · simp only [DyBox.anc, wEmb]; omega
    · simp only [DyBox.anc, wEmb, hsub, hm]
      rw [hpe, show Bw.j * (2 ^ (b.n - i) * 2 ^ i) + b.j = 2 ^ (b.n - i) * (Bw.j * 2 ^ i) + b.j by
        ring, Nat.mul_add_div hpos]
    · simp only [DyBox.anc, wEmb, hsub, hm]
      rw [hpe, show Bw.k * (2 ^ (b.n - i) * 2 ^ i) + b.k = 2 ^ (b.n - i) * (Bw.k * 2 ^ i) + b.k by
        ring, Nat.mul_add_div hpos]
  · rw [anc_self (by simp only [wEmb]; omega), anc_self h]

lemma wEmb_anc_le (Bw b : DyBox) {i : ℕ} (hi : i ≤ Bw.n) : (wEmb Bw b).anc i = Bw.anc i := by
  have hp : (2 : ℕ) ^ (Bw.n + b.n - i) = 2 ^ b.n * 2 ^ (Bw.n - i) := by
    rw [← pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ b.n := by positivity
  ext
  · simp only [DyBox.anc, wEmb]; omega
  · simp only [DyBox.anc, wEmb, hp, ← Nat.div_div_eq_div_mul]
    rw [mul_comm Bw.j, Nat.mul_add_div hpos, Nat.div_eq_of_lt b.hj, add_zero]
  · simp only [DyBox.anc, wEmb, hp, ← Nat.div_div_eq_div_mul]
    rw [mul_comm Bw.k, Nat.mul_add_div hpos, Nat.div_eq_of_lt b.hk, add_zero]

lemma closedBox_wEmb_sub (Bw b : DyBox) : (wEmb Bw b).closedBox ⊆ Bw.closedBox := by
  have := closedBox_sub_anc (wEmb Bw b) Bw.n
  rwa [wEmb_anc_le Bw b le_rfl, anc_self le_rfl] at this

lemma wEmb_mem_cellsInside (Bw b : DyBox) : wEmb Bw b ∈ cellsInside Bw := closedBox_wEmb_sub Bw b

/-- A dyadic box contained in `B̄w` is a sub-box `wEmb Bw b`. -/
lemma exists_wEmb_of_sub {Bw T : DyBox} (h : T.closedBox ⊆ Bw.closedBox) : ∃ b, T = wEmb Bw b := by
  have hT := wside_pos T
  have c1 : (⟨T.j * T.side, T.k * T.side⟩ : ℂ) ∈ T.closedBox := by
    refine ⟨le_rfl, ?_, le_rfl, ?_⟩ <;> dsimp only <;> nlinarith
  have c2 : (⟨(T.j + 1) * T.side, (T.k + 1) * T.side⟩ : ℂ) ∈ T.closedBox := by
    refine ⟨?_, le_rfl, ?_, le_rfl⟩ <;> dsimp only <;> nlinarith
  obtain ⟨a1, -, a3, -⟩ := h c1
  obtain ⟨-, b2, -, b4⟩ := h c2
  dsimp only at a1 a3 b2 b4
  have hside : T.side ≤ Bw.side := by nlinarith
  have hn := level_ge_of_side_le hside
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hn
  have hsd : Bw.side = (2 : ℝ) ^ d * T.side := by
    have := side_eq_pow_mul (b := Bw) (b' := T) hd; push_cast at this; exact this
  rw [hsd] at a1 a3 b2 b4
  have q1 : (Bw.j : ℝ) * 2 ^ d ≤ T.j := by nlinarith
  have q2 : (T.j : ℝ) + 1 ≤ (Bw.j + 1) * 2 ^ d := by nlinarith
  have q3 : (Bw.k : ℝ) * 2 ^ d ≤ T.k := by nlinarith
  have q4 : (T.k : ℝ) + 1 ≤ (Bw.k + 1) * 2 ^ d := by nlinarith
  have n1 : Bw.j * 2 ^ d ≤ T.j := by exact_mod_cast q1
  have n2 : T.j + 1 ≤ (Bw.j + 1) * 2 ^ d := by exact_mod_cast q2
  have n3 : Bw.k * 2 ^ d ≤ T.k := by exact_mod_cast q3
  have n4 : T.k + 1 ≤ (Bw.k + 1) * 2 ^ d := by exact_mod_cast q4
  rw [add_mul, one_mul] at n2 n4
  refine ⟨⟨d, T.j - Bw.j * 2 ^ d, T.k - Bw.k * 2 ^ d, by omega, by omega⟩, ?_⟩
  ext
  · simp only [wEmb]; omega
  · simp only [wEmb]; omega
  · simp only [wEmb]; omega

/-! ### Cells, neighbours, membership -/

section Cells

variable {m : DyBox → ℝ} {δ : ℝ} {Bw : DyBox}

/-- `Bw` and all its ancestors are split at `δ`. -/
def WSplit (m : DyBox → ℝ) (δ : ℝ) (Bw : DyBox) : Prop := ∀ i ≤ Bw.n, δ ^ 2 ≤ m (Bw.anc i)

lemma isCell_wEmb_iff (hs : WSplit m δ Bw) {b : DyBox} :
    IsCell m δ (wEmb Bw b) ↔ IsCell (fun c => m (wEmb Bw c)) δ b := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i hi => ?_⟩
    have := h2 (Bw.n + i) (by simp only [wEmb]; omega)
    rwa [wEmb_anc_add] at this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i hi => ?_⟩
    rcases le_or_gt i Bw.n with h | h
    · rw [wEmb_anc_le Bw b h]; exact hs i h
    · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le h.le
      rw [wEmb_anc_add]
      exact h2 i' (by simp only [wEmb] at hi; omega)

lemma not_isCell_root_of_split (hs : WSplit m δ Bw) :
    ∀ b, IsCell (fun c => m (wEmb Bw c)) δ b → 1 ≤ b.n := by
  intro b hb
  by_contra h0
  have h0' : b.n = 0 := by omega
  have := hs Bw.n le_rfl
  rw [anc_self le_rfl] at this
  have hb1 := hb.1
  have e : wEmb Bw b = Bw := by
    have := wEmb_anc_le Bw b (le_refl Bw.n)
    rw [anc_self (by simp only [wEmb]; omega), anc_self le_rfl] at this
    exact this
  simp only [e] at hb1
  linarith

lemma WSplit.mono {δ' : ℝ} (hs : WSplit m δ Bw) (h0 : 0 ≤ δ') (h : δ' ≤ δ) : WSplit m δ' Bw :=
  fun i hi => (pow_le_pow_left₀ h0 h 2).trans (hs i hi)

end Cells

lemma neighbour_wEmb_iff {Bw b b' : DyBox} :
    Neighbour (wEmb Bw b) (wEmb Bw b') ↔ Neighbour b b' := by
  unfold Neighbour
  rw [closedBox_wEmb, closedBox_wEmb, ← image_inter (wHom Bw).injective,
    (wHom Bw).injective.subsingleton_image_iff, (wEmb_injective Bw).ne_iff]

lemma idx_wHom {Bw : DyBox} (n : ℕ) {J : ℕ} (hJ : J < 2 ^ Bw.n) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) : idx (Bw.n + n) (J * Bw.side + Bw.side * x) = J * 2 ^ n + idx n x := by
  have hP := two_pow_mul_side Bw
  have e : (J * Bw.side + Bw.side * x) * 2 ^ (Bw.n + n) = x * 2 ^ n + ((J * 2 ^ n : ℕ) : ℝ) := by
    push_cast; rw [pow_add]; linear_combination (J * 2 ^ n + x * 2 ^ n) * hP
  have hfl : ⌊x * 2 ^ n⌋₊ < 2 ^ n := by
    rw [Nat.floor_lt (by positivity)]; push_cast
    have : (0 : ℝ) < 2 ^ n := by positivity
    nlinarith
  have hidx : idx n x = ⌊x * 2 ^ n⌋₊ := min_eq_left (by omega)
  have := wEmb_lt (m := n) hJ (idx_lt n x)
  show min ⌊(J * Bw.side + Bw.side * x) * 2 ^ (Bw.n + n)⌋₊ (2 ^ (Bw.n + n) - 1) = _
  rw [e, Nat.floor_add_natCast (by positivity), ← hidx, add_comm, min_eq_left (by omega)]

/-- Membership transfers for points off the top and right edges of `𝕍`. -/
lemma mem_wEmb_iff {Bw b : DyBox} {v : ℂ} (hv : v ∈ dzzV) (hre : v.re < 1) (him : v.im < 1) :
    (wEmb Bw b).Mem (wHom Bw v) ↔ b.Mem v := by
  have hb : boxAt (wEmb Bw b).n (wHom Bw v) = wEmb Bw (boxAt b.n v) := by
    ext
    · rfl
    · simp only [boxAt, wEmb, wHom_re]; exact idx_wHom b.n Bw.hj hv.1 hre
    · simp only [boxAt, wEmb, wHom_im]; exact idx_wHom b.n Bw.hk hv.2.2.1 him
  have hV : wHom Bw v ∈ dzzV := by
    have hvb : v ∈ DyBox.root.closedBox := by
      obtain ⟨h1, h2, h3, h4⟩ := hv
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [DyBox.root, DyBox.side] <;> linarith
    have := closedBox_wEmb_sub Bw DyBox.root (wHom_mem_closedBox.2 hvb)
    exact closedBox_sub_dzzV' Bw this
  unfold DyBox.Mem
  rw [hb, (wEmb_injective Bw).eq_iff]
  exact ⟨fun h => ⟨hv, h.2⟩, fun h => ⟨hV, h.2⟩⟩

end DZZ
end LQGMetric
