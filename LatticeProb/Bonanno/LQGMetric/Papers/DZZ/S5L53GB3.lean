/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53GB3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Q1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J9

/-!
# DZZ Lemma 5.3, part 1: probabilistic inputs of the per-box Peierls step (P2-DZZ53GB)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2452–2514; DEC-131 §4, DEC-131-IF §2 J-4, §3
G-J3.

* `disjoint_sqBox_seven` (DEC-131-IF §4.2), **`l53_sub_region_disjoint`**: sub-boxes of the grid
  `l53Sub` (S5L53J9) at sites with `PercFar 7` have disjoint proxy regions
  `Ioo 0 (s²) ×ˢ sqBox c_B (7 t)` (J-4).
* `l53_hind_of_prod`: the product formula (Q2 part 3) gives the hypothesis `hind` of
  `l53_cell_desirable_prob(_on)` (S5L53J6, S5L53GB1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- Squares of side `7t` whose centres are `> 7t` apart in one coordinate are disjoint
(DEC-131-IF §4.2). -/
lemma disjoint_sqBox_seven {c c' : ℂ} {t : ℝ}
    (h : 7 * t < |c.re - c'.re| ∨ 7 * t < |c.im - c'.im|) :
    Disjoint (sqBox c (7 * t)) (sqBox c' (7 * t)) := by
  rw [Set.disjoint_left]
  rintro z ⟨h1, h2⟩ ⟨h3, h4⟩
  have e1 := abs_sub_le c.re z.re c'.re
  have e2 := abs_sub_le c.im z.im c'.im
  rw [abs_sub_comm c.re z.re] at e1
  rw [abs_sub_comm c.im z.im] at e2
  rcases h with h | h <;> linarith

/-- **The proxy regions of far sub-boxes are disjoint** (DEC-131-IF J-4): for sites `x, y` of
`l53EvenBox N` with `PercFar 7 x y`, the regions `Ioo 0 (s²) ×ˢ sqBox c_B (7 t)` of the sub-boxes
`l53Sub C k N x`, `l53Sub C k N y` (side `t`) are disjoint. -/
lemma l53_sub_region_disjoint (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) {x y : ℤ × ℤ}
    (hx : x ∈ l53EvenBox N) (hy : y ∈ l53EvenBox N) (hxy : PercFar 7 x y) (s : ℝ) :
    Disjoint (Ioo 0 (s ^ 2) ×ˢ sqBox (l53Sub C k N x).center (7 * (l53Sub C k N x).side))
      (Ioo 0 (s ^ 2) ×ˢ sqBox (l53Sub C k N y).center (7 * (l53Sub C k N y).side)) := by
  rw [Set.disjoint_prod]
  right
  obtain ⟨hx1, hx2⟩ := l53_sub_jk C hK hx
  obtain ⟨hy1, hy2⟩ := l53_sub_jk C hK hy
  have hside : (l53Sub C k N y).side = (l53Sub C k N x).side := rfl
  rw [hside]
  set t := (l53Sub C k N x).side
  have ht : 0 < t := side_pos' _
  have hre : (l53Sub C k N x).center.re - (l53Sub C k N y).center.re =
      (((l53Sub C k N x).j : ℤ) - ((l53Sub C k N y).j : ℤ) : ℤ) * t := by
    simp only [DyBox.center, hside]; push_cast; ring
  have him : (l53Sub C k N x).center.im - (l53Sub C k N y).center.im =
      (((l53Sub C k N x).k : ℤ) - ((l53Sub C k N y).k : ℤ) : ℤ) * t := by
    simp only [DyBox.center, hside]; push_cast; ring
  rw [hx1, hy1] at hre
  rw [hx2, hy2] at him
  have hre' : (l53Sub C k N x).center.re - (l53Sub C k N y).center.re =
      ((x.1 - y.1 : ℤ) : ℝ) * t := by rw [hre]; congr 1; push_cast; ring
  have him' : (l53Sub C k N x).center.im - (l53Sub C k N y).center.im =
      ((x.2 - y.2 : ℤ) : ℝ) * t := by rw [him]; congr 1; push_cast; ring
  have key : ∀ d : ℤ, (7 < d ∨ 7 < -d) → 7 * t < |(d : ℝ)| * t := by
    intro d hd
    have h8 : (8 : ℝ) ≤ |(d : ℝ)| := by
      rcases hd with hd | hd
      · have : (8 : ℝ) ≤ d := by exact_mod_cast hd
        exact this.trans (le_abs_self _)
      · have : (8 : ℝ) ≤ -d := by exact_mod_cast hd
        exact this.trans (neg_le_abs _)
    nlinarith
  apply disjoint_sqBox_seven
  rw [hre', him', abs_mul, abs_mul, abs_of_pos ht]
  simp only [PercFar] at hxy
  rcases hxy with h | h | h | h
  · exact Or.inl (key _ (Or.inl (by omega)))
  · exact Or.inl (key _ (Or.inr (by omega)))
  · exact Or.inr (key _ (Or.inl (by omega)))
  · exact Or.inr (key _ (Or.inr (by omega)))

/-- **`hind` of `l53_cell_desirable_prob(_on)` from the product formula** (Q2 part 3) and the
disjointness of the regions of `PercFar r` sites. -/
lemma l53_hind_of_prod (μ : Measure Ω) (Box : Finset (ℤ × ℤ)) (Bad : ℤ × ℤ → Set Ω) (r : ℕ)
    {R₀ : Set (ℝ × ℂ)} (R : ℤ × ℤ → Set (ℝ × ℂ)) (hR₀ : ∀ z ∈ Box, Disjoint R₀ (R z))
    (hRd : ∀ x ∈ Box, ∀ y ∈ Box, PercFar r x y → Disjoint (R x) (R y))
    (hprod : ∀ F : Finset (ℤ × ℤ), (∀ z ∈ F, z ∈ Box) →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (R i) (R j)) →
      (∀ i ∈ F, Disjoint R₀ (R i)) → μ (⋂ i ∈ F, Bad i) = ∏ i ∈ F, μ (Bad i)) :
    ∀ F : Finset (ℤ × ℤ), (∀ z ∈ F, z ∈ Box) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, Bad x) ≤ ∏ x ∈ F, μ (Bad x) :=
  fun F hF hfar => le_of_eq (hprod F hF (fun i hi j hj hij => hRd i (hF i hi) j (hF j hj)
    (hfar i hi j hj hij)) fun i hi => hR₀ i (hF i hi))

end DZZ
end LQGMetric
