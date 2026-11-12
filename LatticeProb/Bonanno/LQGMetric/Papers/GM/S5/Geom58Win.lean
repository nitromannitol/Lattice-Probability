/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58Win at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

/-!
# GM Lemma 5.8: the staircase paths inside a window of points (task P2-M2L58b)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3080–3081): "choose in a deterministic manner a piecewise linear path `L_k`
from `z_{k−1} + 2ρr` to `z_k − 2ρr` … which do not intersect any of the balls `B_{2ρr}(z)` … and lie
at Euclidean distance at least `ρr` from one another".

GM leave the paths implicit; this is our explicit choice (own construction, for the D69 horizontal
stubs). For `z, w` with `w.re ≥ z.re + 10R`, `stair R z w` is the polygonal path
`z + 2R → z + 5R → (z.re + 5R, w.im) → w − 2R` (horizontal, vertical, horizontal). It is compact and
connected, and every point lies in the vertical strip `z.re + 2R ≤ Re ≤ w.re − 2R`, on the
horizontal ray of `z` (right of `z + 2R`), on the vertical line `Re = z.re + 5R`, or on the
horizontal ray of `w` (left of `w − 2R`) (`mem_stair`). For points on the upper or lower part of
`∂B_r(0)` with real parts `10R` apart, consecutive stairs are `4R` apart (disjoint strips) and meet
the `3R`-balls around the points only on their stubs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM

/-- the horizontal segment `[a, b] × {y}` -/
def hSeg (y a b : ℝ) : Set ℂ := (fun t : ℝ => (⟨t, y⟩ : ℂ)) '' Icc a b

/-- the vertical segment `{x} × [a, b]` (either order) -/
def vSeg (x a b : ℝ) : Set ℂ := (fun t : ℝ => (⟨x, t⟩ : ℂ)) '' uIcc a b

lemma continuous_hLine (y : ℝ) : Continuous (fun t : ℝ => (⟨t, y⟩ : ℂ)) :=
  Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk continuous_const)

lemma continuous_vLine (x : ℝ) : Continuous (fun t : ℝ => (⟨x, t⟩ : ℂ)) :=
  Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)

lemma isCompact_hSeg (y a b : ℝ) : IsCompact (hSeg y a b) :=
  isCompact_Icc.image (continuous_hLine y)

lemma isCompact_vSeg (x a b : ℝ) : IsCompact (vSeg x a b) :=
  isCompact_uIcc.image (continuous_vLine x)

lemma isConnected_hSeg (y : ℝ) {a b : ℝ} (hab : a ≤ b) : IsConnected (hSeg y a b) :=
  (isConnected_Icc hab).image _ (continuous_hLine y).continuousOn

lemma isConnected_vSeg (x a b : ℝ) : IsConnected (vSeg x a b) :=
  (isConnected_Icc (inf_le_sup : a ⊓ b ≤ a ⊔ b)).image _ (continuous_vLine x).continuousOn

lemma mem_hSeg {y a b : ℝ} {p : ℂ} : p ∈ hSeg y a b ↔ p.im = y ∧ a ≤ p.re ∧ p.re ≤ b := by
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨rfl, h1, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨p.re, ⟨h2, h3⟩, Complex.ext rfl h1.symm⟩

lemma mem_vSeg {x a b : ℝ} {p : ℂ} :
    p ∈ vSeg x a b ↔ p.re = x ∧ min a b ≤ p.im ∧ p.im ≤ max a b := by
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨rfl, h1, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨p.im, ⟨h2, h3⟩, Complex.ext h1.symm rfl⟩

/-- the staircase path from `z + 2R` to `w − 2R` -/
def stair (R : ℝ) (z w : ℂ) : Set ℂ :=
  hSeg z.im (z.re + 2 * R) (z.re + 5 * R) ∪ vSeg (z.re + 5 * R) z.im w.im ∪
    hSeg w.im (z.re + 5 * R) (w.re - 2 * R)

lemma isCompact_stair (R : ℝ) (z w : ℂ) : IsCompact (stair R z w) :=
  ((isCompact_hSeg _ _ _).union (isCompact_vSeg _ _ _)).union (isCompact_hSeg _ _ _)

lemma isConnected_stair {R : ℝ} (hR : 0 ≤ R) {z w : ℂ} (hzw : z.re + 7 * R ≤ w.re) :
    IsConnected (stair R z w) := by
  have c1 : (⟨z.re + 5 * R, z.im⟩ : ℂ) ∈ hSeg z.im (z.re + 2 * R) (z.re + 5 * R) ∩
      vSeg (z.re + 5 * R) z.im w.im :=
    ⟨mem_hSeg.2 ⟨rfl, by simp only; linarith, le_rfl⟩,
      mem_vSeg.2 ⟨rfl, min_le_left _ _, le_max_left _ _⟩⟩
  have c2 : (⟨z.re + 5 * R, w.im⟩ : ℂ) ∈ (hSeg z.im (z.re + 2 * R) (z.re + 5 * R) ∪
      vSeg (z.re + 5 * R) z.im w.im) ∩ hSeg w.im (z.re + 5 * R) (w.re - 2 * R) :=
    ⟨Or.inr (mem_vSeg.2 ⟨rfl, min_le_right _ _, le_max_right _ _⟩),
      mem_hSeg.2 ⟨rfl, le_rfl, by simp only; linarith⟩⟩
  exact (((isConnected_hSeg _ (by linarith)).union ⟨_, c1⟩ (isConnected_vSeg _ _ _)).union
    ⟨_, c2⟩ (isConnected_hSeg _ (by linarith)))

lemma left_mem_stair {R : ℝ} (hR : 0 ≤ R) (z w : ℂ) : z + 2 * (R : ℂ) ∈ stair R z w := by
  refine Or.inl (Or.inl (mem_hSeg.2 ⟨?_, ?_, ?_⟩))
  · simp
  · simp
  · simp; linarith

lemma right_mem_stair {R : ℝ} (hR : 0 ≤ R) {z w : ℂ} (hzw : z.re + 7 * R ≤ w.re) :
    w - 2 * (R : ℂ) ∈ stair R z w := by
  refine Or.inr (mem_hSeg.2 ⟨?_, ?_, ?_⟩)
  · simp
  · simp; linarith
  · simp

/-- the shape of a staircase -/
lemma mem_stair {R : ℝ} (hR : 0 ≤ R) {z w p : ℂ} (hzw : z.re + 7 * R ≤ w.re)
    (hp : p ∈ stair R z w) :
    z.re + 2 * R ≤ p.re ∧ p.re ≤ w.re - 2 * R ∧
      ((p.im = z.im ∧ p.re ≤ z.re + 5 * R) ∨
        (p.re = z.re + 5 * R ∧ min z.im w.im ≤ p.im ∧ p.im ≤ max z.im w.im) ∨
        (p.im = w.im ∧ z.re + 5 * R ≤ p.re)) := by
  rcases hp with (hp | hp) | hp
  · obtain ⟨h1, h2, h3⟩ := mem_hSeg.1 hp
    exact ⟨h2, by linarith, Or.inl ⟨h1, h3⟩⟩
  · obtain ⟨h1, h2, h3⟩ := mem_vSeg.1 hp
    exact ⟨by linarith, by linarith, Or.inr (Or.inl ⟨h1, h2, h3⟩)⟩
  · obtain ⟨h1, h2, h3⟩ := mem_hSeg.1 hp
    exact ⟨by linarith, h3, Or.inr (Or.inr ⟨h1, h2⟩)⟩

/-! ## A window of points with real parts in arithmetic progression -/

lemma dist_ge_re (p q : ℂ) : |p.re - q.re| ≤ dist p q := by
  rw [dist_eq_norm, ← Complex.sub_re]; exact Complex.abs_re_le_norm _

/-- consecutive-index staircases of a window are `R` apart (they lie in vertical strips `4R`
apart) -/
theorem stair_sep {R T : ℝ} (hR : 0 < R) {zs : ℕ → ℂ} (hre : ∀ j, (zs j).re = T + 10 * R * j)
    {i i' : ℕ} (hii' : i < i') {p q : ℂ} (hp : p ∈ stair R (zs i) (zs (i + 1)))
    (hq : q ∈ stair R (zs i') (zs (i' + 1))) : R ≤ dist p q := by
  have h7 : ∀ k, (zs k).re + 7 * R ≤ (zs (k + 1)).re := fun k => by
    rw [hre, hre]; push_cast; nlinarith
  obtain ⟨-, hp2, -⟩ := mem_stair hR.le (h7 i) hp
  obtain ⟨hq1, -, -⟩ := mem_stair hR.le (h7 i') hq
  have hi : (i : ℝ) + 1 ≤ i' := by exact_mod_cast hii'
  rw [hre] at hp2 hq1
  push_cast at hp2
  have := dist_ge_re q p
  rw [dist_comm] at this
  have hqp : 4 * R ≤ q.re - p.re := by nlinarith
  rw [abs_of_nonneg (by linarith)] at this
  linarith

/-- the staircase `zs i → zs (i+1)` meets the `3R`-balls around the window points only on its two
horizontal stubs -/
theorem stair_stub {R T : ℝ} (hR : 0 < R) {zs : ℕ → ℂ} (hre : ∀ j, (zs j).re = T + 10 * R * j)
    {i : ℕ} {p : ℂ} (hp : p ∈ stair R (zs i) (zs (i + 1))) (j : ℕ) (hd : dist p (zs j) < 3 * R) :
    (i + 1 = j ∧ p.im = (zs j).im ∧ p.re ≤ (zs j).re - 2 * R) ∨
      (i + 1 = j + 1 ∧ p.im = (zs j).im ∧ (zs j).re + 2 * R ≤ p.re) := by
  have h7 : (zs i).re + 7 * R ≤ (zs (i + 1)).re := by
    rw [hre, hre]; push_cast; nlinarith
  obtain ⟨hp1, hp2, hp3⟩ := mem_stair hR.le h7 hp
  have hre' := (abs_lt.1 (lt_of_le_of_lt (dist_ge_re p (zs j)) hd))
  have e1 := hre i
  have e2 := hre (i + 1)
  have e3 := hre j
  push_cast at e2
  have hj1 : j ≤ i + 1 := by
    by_contra h
    push Not at h
    have : (i : ℝ) + 2 ≤ j := by exact_mod_cast h
    nlinarith
  have hj2 : i ≤ j := by
    by_contra h
    push Not at h
    have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    nlinarith
  rcases eq_or_lt_of_le hj2 with rfl | hlt
  · right
    refine ⟨rfl, ?_, hp1⟩
    rcases hp3 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exfalso; linarith
    · exfalso; linarith
  · have hj : j = i + 1 := by omega
    subst hj
    left
    refine ⟨rfl, ?_, hp2⟩
    rcases hp3 with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exfalso; push_cast at hre'; linarith
    · exfalso; push_cast at hre'; linarith
    · exact h

end LQGMetric.GM
