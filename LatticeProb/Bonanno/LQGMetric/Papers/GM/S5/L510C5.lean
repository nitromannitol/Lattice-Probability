/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.L510C5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510C4

/-!
# GM Lemma 5.10, condition (6) (task P2-M2M6)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, l. 3322:
"By Lemma 2.10 (applied with `ζ` in place of `ε`) and a union bound over all of the sides of all
of the squares in `𝓢_{ε₀r}(B_{2r}(0))`, we can choose `ζ ∈ (0, ε₀/100)` … such that
condition 6 holds with probability at least `1 − (1 − 𝕡)/100`."

Here: GM Lemma 2.10 = DFGPS Prop 4.1 (`Blueprint.DFGPSProp4_1`), with the exponent made negative
by `Blueprint.GMXiQBound` (GM l. 1056, as in `gm_L2_11`), applied to the finitely many segments
`lineSeg ε₀ R₀ l` (grid lines of spacing `ε₀`, clipped to `[−R₀, R₀]`, `R₀ = 3 + 3ε₀`; the
union bound runs over these grid lines, which contain all the sides) and transferred from the
normalized field `h − h_1(0)` to `h` by Axiom III. The deterministic corner step is
`l510_subpath` (`L510C4.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the grid line `{crd l.1 = l.2 ε₀}` clipped to `[−R, R]` (unit scale) -/
def lineSeg (ε₀ R : ℝ) (l : Bool × ℤ) : Set ℂ :=
  if l.1 then segment ℝ (⟨l.2 * ε₀, -R⟩ : ℂ) ⟨l.2 * ε₀, R⟩
  else segment ℝ (⟨-R, l.2 * ε₀⟩ : ℂ) ⟨R, l.2 * ε₀⟩

lemma isSegmentOrArc_lineSeg (ε₀ R : ℝ) (l : Bool × ℤ) : IsSegmentOrArc (lineSeg ε₀ R l) := by
  unfold lineSeg
  split_ifs
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩

lemma l510_mem_seg {R y : ℝ} (hR : 0 < R) (hy : |y| ≤ R) (p q : ℂ) :
    ((R - y) / (2 * R)) • p + ((R + y) / (2 * R)) • q ∈ segment ℝ p q := by
  rw [abs_le] at hy
  exact ⟨_, _, div_nonneg (by linarith) (by positivity), div_nonneg (by linarith) (by positivity),
    by field_simp; ring, rfl⟩

/-- a point of a strip of half-width `δ` in `cl B_{Rr}(0)` is `δ`-close to the clipped line -/
lemma l510_strip_subset {ε₀ R r δ : ℝ} (hr : 0 < r) (hR : 0 < R) (l : Bool × ℤ) {z : ℂ}
    (hz : z ∈ gStrip (ε₀ * r) δ l) (hzR : ‖z‖ ≤ R * r) :
    z ∈ thickening δ (scaleSet r 0 (lineSeg ε₀ R l)) := by
  obtain ⟨b, k⟩ := l
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz' : |crd b z - k * (ε₀ * r)| < δ := hz
  rw [mem_thickening_iff]
  cases b
  · -- horizontal line
    have hy : |z.re / r| ≤ R := by
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
      exact (Complex.abs_re_le_norm z).trans hzR
    refine ⟨(r : ℂ) * ⟨z.re / r, k * ε₀⟩ + 0, ⟨⟨z.re / r, k * ε₀⟩, ?_, rfl⟩, ?_⟩
    · have h := l510_mem_seg hR hy (⟨-R, k * ε₀⟩ : ℂ) ⟨R, k * ε₀⟩
      have e : ((R - z.re / r) / (2 * R)) • (⟨-R, k * ε₀⟩ : ℂ) +
          ((R + z.re / r) / (2 * R)) • (⟨R, k * ε₀⟩ : ℂ) = ⟨z.re / r, k * ε₀⟩ := by
        apply Complex.ext <;>
          simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
            smul_eq_mul] <;> field_simp <;> ring
      simp only [lineSeg, Bool.false_eq_true, ↓reduceIte]
      rw [← e]; exact h
    · rw [dist_eq_norm]
      have e : z - ((r : ℂ) * ⟨z.re / r, k * ε₀⟩ + 0) = ((z.im - k * (ε₀ * r) : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp <;> field_simp <;> ring
      rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hz'
  · -- vertical line
    have hy : |z.im / r| ≤ R := by
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
      exact (Complex.abs_im_le_norm z).trans hzR
    refine ⟨(r : ℂ) * ⟨k * ε₀, z.im / r⟩ + 0, ⟨⟨k * ε₀, z.im / r⟩, ?_, rfl⟩, ?_⟩
    · have h := l510_mem_seg hR hy (⟨k * ε₀, -R⟩ : ℂ) ⟨k * ε₀, R⟩
      have e : ((R - z.im / r) / (2 * R)) • (⟨k * ε₀, -R⟩ : ℂ) +
          ((R + z.im / r) / (2 * R)) • (⟨k * ε₀, R⟩ : ℂ) = ⟨k * ε₀, z.im / r⟩ := by
        apply Complex.ext <;>
          simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
            smul_eq_mul] <;> field_simp <;> ring
      simp only [lineSeg, ↓reduceIte]
      rw [← e]; exact h
    · rw [dist_eq_norm]
      have e : z - ((r : ℂ) * ⟨k * ε₀, z.im / r⟩ + 0) = ((z.re - k * (ε₀ * r) : ℝ) : ℂ) := by
        apply Complex.ext <;> simp <;> field_simp <;> ring
      rw [e, Complex.norm_real, Real.norm_eq_abs]
      exact hz'

/-- the points of the `ζ`-neighbourhood of the frontier of a tube of `𝓢_{ε₀r}(cl B_{2r}(0))`
lie in `cl B_{(3 + 3ε₀) r}(0)` -/
lemma l510_region {ε₀ r ζ : ℝ} (hε₀ : 0 < ε₀) (hr : 0 < r) (hζ : ζ ≤ r) {F : Finset (ℤ × ℤ)}
    (hF : ∀ m ∈ F, (gridSquare (ε₀ * r) m ∩ closedBall 0 (2 * r)).Nonempty) {y : ℂ}
    (hy : y ∈ thickening ζ (frontier (tubeOf (ε₀ * r) F))) : ‖y‖ ≤ (3 + 3 * ε₀) * r := by
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 hy
  have hzcl : z ∈ ⋃ m ∈ F, gridSquare (ε₀ * r) m := by
    have hc : IsClosed (⋃ m ∈ F, gridSquare (ε₀ * r) m) :=
      (Finset.finite_toSet F).isClosed_biUnion fun m _ => isClosed_gridSquare56 _ m
    exact closure_minimal interior_subset hc (frontier_subset_closure hz)
  obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.1 hzcl
  obtain ⟨x, hx, hxB⟩ := hF m hm
  have h1 := gridSquare_subset_ball (mul_pos hε₀ hr) hx hzm
  rw [mem_ball, dist_eq_norm] at h1
  rw [mem_closedBall, dist_zero_right] at hxB
  rw [dist_eq_norm] at hyz
  have := norm_le_norm_add_norm_sub' y z
  have := norm_le_norm_add_norm_sub' z x
  nlinarith

end LQGMetric.GM
