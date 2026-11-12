import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Area of the thickened boundary of a round annulus

For a round annulus `D = B_r(c) \ B̄_s(c)` in `ℂ` with `0 ≤ s ≤ r ≤ 1`, the `δ`-thickening of its boundary has
Lebesgue measure at most `16 π δ` for every `δ ∈ (0, 1)`. This is the boundary-regularity hypothesis
`volume (thickening δ (frontier D)) ≤ C δ` on the domain in energy estimates for discrete harmonic functions on
random planar maps (with any constant `C ≥ 16 π`).

The estimate follows from the inclusion of the `δ`-thickening of the circle `∂B_R(c)` in the round annulus
`B_{R+δ}(c) \ B̄_{R-δ}(c)`, whose area is at most `4 π δ (R + δ)`, and from `∂D ⊆ ∂B_r(c) ∪ ∂B_s(c)`.

## Main results

* `LatticeProb.thickening_sphere_subset_ball_diff_closedBall`: `thickening δ (sphere c R) ⊆ B_{R+δ}(c) \ B̄_{R-δ}(c)`.
* `LatticeProb.volume_thickening_sphere_le`: `|thickening δ (∂B_R(c))| ≤ 4 π δ (R + δ)` in `ℂ`.
* `LatticeProb.frontier_ball_diff_closedBall_subset`: `∂(B_r(c) \ B̄_s(c)) ⊆ ∂B_r(c) ∪ ∂B_s(c)`.
* `LatticeProb.volume_thickening_frontier_annulus_le`: the bound for the boundary of an annulus.
* `LatticeProb.volume_thickening_frontier_annulus_le_mul`: the uniform bound `C δ`, `C ≥ 16 π`, `δ ∈ (0, 1)`.
-/

open Metric MeasureTheory Set

namespace LatticeProb

/-- The `δ`-thickening of the sphere `∂B_R(c)` lies in the round annulus `B_{R+δ}(c) \ B̄_{R-δ}(c)`. -/
theorem thickening_sphere_subset_ball_diff_closedBall {E : Type*} [PseudoMetricSpace E] (c : E) (R δ : ℝ) :
    thickening δ (sphere c R) ⊆ ball c (R + δ) \ closedBall c (R - δ) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
  rw [mem_sphere] at hy
  refine ⟨?_, ?_⟩
  · rw [mem_ball]
    have := dist_triangle x y c
    linarith
  · rw [mem_closedBall, not_le]
    have := dist_triangle y x c
    rw [dist_comm y x] at this
    linarith

/-- The boundary of the round annulus `B_r(c) \ B̄_s(c)` lies in the union of the two circles `∂B_r(c)` and
`∂B_s(c)`. -/
theorem frontier_ball_diff_closedBall_subset {E : Type*} [PseudoMetricSpace E] (c : E) (r s : ℝ) :
    frontier (ball c r \ closedBall c s) ⊆ sphere c r ∪ sphere c s := by
  rw [sdiff_eq]
  refine (frontier_inter_subset _ _).trans ?_
  rw [frontier_compl]
  rintro x (⟨hx, -⟩ | ⟨-, hx⟩)
  · exact Or.inl (frontier_ball_subset_sphere hx)
  · exact Or.inr (frontier_closedBall_subset_sphere hx)

private theorem coe_nnreal_pi_eq_ofReal : ((NNReal.pi : NNReal) : ENNReal) = ENNReal.ofReal Real.pi := by
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- **Area of the thickened circle** in `ℂ`: for `R ≥ 0` and `δ > 0`, the `δ`-thickening of the circle `∂B_R(c)`
has Lebesgue measure at most `4 π δ (R + δ)`. -/
theorem volume_thickening_sphere_le (c : ℂ) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    volume (thickening δ (sphere c R)) ≤ ENNReal.ofReal (4 * Real.pi * δ * (R + δ)) := by
  have hpi := Real.pi_pos
  have hsub : closedBall c (R - δ) ⊆ ball c (R + δ) := closedBall_subset_ball (by linarith)
  have hsplit : volume (ball c (R + δ) \ closedBall c (R - δ)) + volume (closedBall c (R - δ)) =
      volume (ball c (R + δ)) := by
    have := measure_sdiff_add_inter (μ := volume) (ball c (R + δ)) (measurableSet_closedBall (x := c) (ε := R - δ))
    rwa [inter_eq_right.2 hsub] at this
  have hfin : volume (closedBall c (R - δ)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hball : volume (ball c (R + δ)) ≤
      ENNReal.ofReal (4 * Real.pi * δ * (R + δ)) + volume (closedBall c (R - δ)) := by
    have hA : 0 ≤ 4 * Real.pi * δ * (R + δ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpi.le) hδ.le) (by linarith)
    rw [Complex.volume_ball, Complex.volume_closedBall, coe_nnreal_pi_eq_ofReal,
      ← ENNReal.ofReal_pow (by linarith)]
    by_cases h : δ ≤ R
    · rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hA (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have key : 4 * Real.pi * δ * (R + δ) + (R - δ) ^ 2 * Real.pi - (R + δ) ^ 2 * Real.pi =
          4 * Real.pi * δ ^ 2 := by ring
      have : 0 ≤ 4 * Real.pi * δ ^ 2 := by positivity
      linarith
    · rw [ENNReal.ofReal_of_nonpos (by linarith : R - δ ≤ 0)]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero]
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (R + δ) * (R + δ) ≤ (R + δ) * (4 * δ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h2 : (R + δ) ^ 2 * Real.pi ≤ (R + δ) * (4 * δ) * Real.pi := by
        rw [sq]; exact mul_le_mul_of_nonneg_right h1 hpi.le
      linarith [h2, show (R + δ) * (4 * δ) * Real.pi = 4 * Real.pi * δ * (R + δ) by ring]
  calc volume (thickening δ (sphere c R))
      ≤ volume (ball c (R + δ) \ closedBall c (R - δ)) :=
        measure_mono (thickening_sphere_subset_ball_diff_closedBall c R δ)
    _ ≤ ENNReal.ofReal (4 * Real.pi * δ * (R + δ)) := by
        rw [← ENNReal.add_le_add_iff_right hfin, hsplit]
        exact hball

/-- **Area of the thickened boundary of a round annulus**: for `r, s ≥ 0` and `δ > 0`,
`|thickening δ (∂(B_r(c) \ B̄_s(c)))| ≤ 4 π δ (r + δ) + 4 π δ (s + δ)`. -/
theorem volume_thickening_frontier_annulus_le (c : ℂ) {r s δ : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 < δ) :
    volume (thickening δ (frontier (ball c r \ closedBall c s))) ≤
      ENNReal.ofReal (4 * Real.pi * δ * (r + δ)) + ENNReal.ofReal (4 * Real.pi * δ * (s + δ)) :=
  calc volume (thickening δ (frontier (ball c r \ closedBall c s)))
      ≤ volume (thickening δ (sphere c r ∪ sphere c s)) :=
        measure_mono (thickening_subset_of_subset δ (frontier_ball_diff_closedBall_subset c r s))
    _ = volume (thickening δ (sphere c r) ∪ thickening δ (sphere c s)) := by rw [thickening_union]
    _ ≤ volume (thickening δ (sphere c r)) + volume (thickening δ (sphere c s)) := measure_union_le _ _
    _ ≤ _ := add_le_add (volume_thickening_sphere_le c hr hδ) (volume_thickening_sphere_le c hs hδ)

/-- **Uniform boundary regularity of round annuli**: for `0 ≤ s ≤ r ≤ 1` and `C ≥ 16 π`, the boundary of the annulus
`B_r(c) \ B̄_s(c)` satisfies `|thickening δ (∂D)| ≤ C δ` for every `δ ∈ (0, 1)`. -/
theorem volume_thickening_frontier_annulus_le_mul (c : ℂ) {r s C : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr : r ≤ 1)
    (hC : 16 * Real.pi ≤ C) :
    ∀ δ ∈ Ioo (0 : ℝ) 1,
      volume (thickening δ (frontier (ball c r \ closedBall c s))) ≤ ENNReal.ofReal (C * δ) := by
  intro δ hδ
  have hpi := Real.pi_pos
  have h4 : 0 ≤ 4 * Real.pi * δ := mul_nonneg (mul_nonneg (by norm_num) hpi.le) hδ.1.le
  refine (volume_thickening_frontier_annulus_le c (hs.trans hsr) hs hδ.1).trans ?_
  rw [← ENNReal.ofReal_add (mul_nonneg h4 (by linarith [hδ.1])) (mul_nonneg h4 (by linarith [hδ.1]))]
  apply ENNReal.ofReal_le_ofReal
  have h1 : 4 * Real.pi * δ * (r + δ) ≤ 4 * Real.pi * δ * 2 :=
    mul_le_mul_of_nonneg_left (by linarith [hδ.2]) h4
  have h2 : 4 * Real.pi * δ * (s + δ) ≤ 4 * Real.pi * δ * 2 :=
    mul_le_mul_of_nonneg_left (by linarith [hδ.2]) h4
  have h3 : 16 * Real.pi * δ ≤ C * δ := mul_le_mul_of_nonneg_right hC hδ.1.le
  linarith

end LatticeProb
