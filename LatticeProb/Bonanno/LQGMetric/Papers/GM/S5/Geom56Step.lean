/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56Step at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.SepMeas56
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_9Chain

/-!
# GM Lemma 5.6, condition 3: Whitney chains of dyadic squares (task P2-M2L56)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6, condition 3
(l. 2991–2994): "Each point of `O_u` is contained in a square of `𝒦_r(z)` which lies at graph
distance at most 40 from a square which contains `u` … It therefore follows from (5.17) …".

GM's (5.17) bounds `D̃_h(·,·;S)` for the closed squares `S`; a closed square of `𝒦` may meet `∂V`,
so paths in `S` may leave `V` (deviation P2-M2L3-2). We use the bound at every dyadic level
`2^{-j} s` and chain dyadic squares that lie inside `V` (the classical Whitney chain).

* `geom56_step`: two points `x, y` with `|x − y| < σ` whose `3σ`-balls lie in `V` are joined in `V`
  through the two (touching) grid squares of side `σ` containing them.
* `geom56_whitney`: a point `p ∈ V` of a closed grid square `S` of side `s` with `int S ⊆ V` is at
  `d(·,·;V)`-distance `≤ C(χ) t` from the centre of `S` (points `p + λ(c − p)`, `λ ∈ [2^{-j-1},
  2^{-j}]`, joined by squares of side `2^{-j-3} s`).

Own elementary argument (the standard Whitney chain; GM leave the step implicit).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the index of a grid square of side `σ` containing `x` -/
def gridIdx (σ : ℝ) (x : ℂ) : ℤ × ℤ := (⌊x.re / σ⌋, ⌊x.im / σ⌋)

lemma mem_gridSquare_gridIdx {σ : ℝ} (hσ : 0 < σ) (x : ℂ) : x ∈ gridSquare σ (gridIdx σ x) := by
  simp only [gridSquare, gridIdx, mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Int.floor_le (x.re / σ); rwa [le_div_iff₀ hσ] at this
  · have := Int.lt_floor_add_one (x.re / σ); rw [div_lt_iff₀ hσ] at this; linarith
  · have := Int.floor_le (x.im / σ); rwa [le_div_iff₀ hσ] at this
  · have := Int.lt_floor_add_one (x.im / σ); rw [div_lt_iff₀ hσ] at this; linarith

lemma gridSquare_subset_ball {σ : ℝ} (hσ : 0 < σ) {m : ℤ × ℤ} {x : ℂ}
    (hx : x ∈ gridSquare σ m) : gridSquare σ m ⊆ ball x (3 * σ) := by
  intro w hw
  obtain ⟨a1, a2, a3, a4⟩ := hx
  obtain ⟨b1, b2, b3, b4⟩ := hw
  rw [mem_ball, dist_eq_norm]
  refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
  rw [Complex.sub_re, Complex.sub_im]
  have h1 : |w.re - x.re| ≤ σ := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have h2 : |w.im - x.im| ≤ σ := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  linarith

/-- one coordinate: a common grid coordinate of two close points -/
lemma floor_common {σ a b : ℝ} (hσ : 0 < σ) (hab : |a - b| < σ) :
    let g : ℝ := (max ⌊a / σ⌋ ⌊b / σ⌋ : ℤ) * σ
    (⌊a / σ⌋ * σ ≤ g ∧ g ≤ (⌊a / σ⌋ + 1) * σ) ∧ (⌊b / σ⌋ * σ ≤ g ∧ g ≤ (⌊b / σ⌋ + 1) * σ) := by
  intro g
  rw [abs_lt] at hab
  have hab1 : ⌊a / σ⌋ ≤ ⌊b / σ⌋ + 1 := by
    have : a / σ ≤ b / σ + 1 := by
      rw [div_add_one hσ.ne', div_le_div_iff_of_pos_right hσ]; linarith
    have := Int.floor_le_floor this
    rwa [Int.floor_add_one] at this
  have hab2 : ⌊b / σ⌋ ≤ ⌊a / σ⌋ + 1 := by
    have : b / σ ≤ a / σ + 1 := by
      rw [div_add_one hσ.ne', div_le_div_iff_of_pos_right hσ]; linarith
    have := Int.floor_le_floor this
    rwa [Int.floor_add_one] at this
  have e1 : (⌊a / σ⌋ : ℝ) ≤ (max ⌊a / σ⌋ ⌊b / σ⌋ : ℤ) := by exact_mod_cast le_max_left _ _
  have e2 : (⌊b / σ⌋ : ℝ) ≤ (max ⌊a / σ⌋ ⌊b / σ⌋ : ℤ) := by exact_mod_cast le_max_right _ _
  have e3 : ((max ⌊a / σ⌋ ⌊b / σ⌋ : ℤ) : ℝ) ≤ ⌊a / σ⌋ + 1 := by
    exact_mod_cast max_le (by omega) hab2
  have e4 : ((max ⌊a / σ⌋ ⌊b / σ⌋ : ℤ) : ℝ) ≤ ⌊b / σ⌋ + 1 := by
    exact_mod_cast max_le hab1 (by omega)
  exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

/-- **one chain step**: `|x − y| < σ`, `B_{3σ}(x), B_{3σ}(y) ⊆ V`, and the grid squares of side `σ`
containing `x` or `y` have internal diameter `≤ B`; then `d(x, y; V) ≤ 2B` -/
lemma geom56_step (d : ContMetric) {V : Set ℂ} {σ : ℝ} (hσ : 0 < σ) {B : ℝ≥0∞} {x y : ℂ}
    (hxy : ‖x - y‖ < σ) (hx : ball x (3 * σ) ⊆ V) (hy : ball y (3 * σ) ⊆ V)
    (hB : ∀ m, (x ∈ gridSquare σ m ∨ y ∈ gridSquare σ m) →
      internalDiam d (gridSquare σ m) (gridSquare σ m) ≤ B) :
    d.internal V x y ≤ 2 * B := by
  have hre : |x.re - y.re| < σ := by
    rw [← Complex.sub_re]; exact lt_of_le_of_lt (Complex.abs_re_le_norm _) hxy
  have him : |x.im - y.im| < σ := by
    rw [← Complex.sub_im]; exact lt_of_le_of_lt (Complex.abs_im_le_norm _) hxy
  obtain ⟨⟨r1, r2⟩, ⟨r3, r4⟩⟩ := floor_common hσ hre
  obtain ⟨⟨i1, i2⟩, ⟨i3, i4⟩⟩ := floor_common hσ him
  set g : ℂ := ⟨(max ⌊x.re / σ⌋ ⌊y.re / σ⌋ : ℤ) * σ, (max ⌊x.im / σ⌋ ⌊y.im / σ⌋ : ℤ) * σ⟩
  have hgx : g ∈ gridSquare σ (gridIdx σ x) := ⟨r1, r2, i1, i2⟩
  have hgy : g ∈ gridSquare σ (gridIdx σ y) := ⟨r3, r4, i3, i4⟩
  have hxQ := mem_gridSquare_gridIdx hσ x
  have hyQ := mem_gridSquare_gridIdx hσ y
  calc d.internal V x y ≤ d.internal V x g + d.internal V g y := DFGPS.internal_triangle d V x g y
    _ ≤ B + B := by
      refine add_le_add ?_ ?_
      · exact (DFGPS.internal_anti d ((gridSquare_subset_ball hσ hxQ).trans hx) x g).trans
          ((DFGPS.internal_le_internalDiam d hxQ hgx).trans (hB _ (Or.inl hxQ)))
      · exact (DFGPS.internal_anti d ((gridSquare_subset_ball hσ hyQ).trans hy) g y).trans
          ((DFGPS.internal_le_internalDiam d hgy hyQ).trans (hB _ (Or.inr hyQ)))
    _ = 2 * B := (two_mul B).symm

/-- telescoping along a finite sequence of points -/
lemma internal_le_sum_seq (d : ContMetric) (V : Set ℂ) (f : ℕ → ℂ) :
    ∀ n, d.internal V (f 0) (f (n + 1)) ≤
      ∑ i ∈ Finset.range (n + 1), d.internal V (f i) (f (i + 1))
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ]
    exact (DFGPS.internal_triangle d V _ (f (n + 1)) _).trans
      (add_le_add (internal_le_sum_seq d V f n) le_rfl)

end LQGMetric.GM
