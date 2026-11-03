/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCTest at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCCircle

/-!
# Cut-off functions exhausting the open unit square (task P2-GMC, WP-24)

`sqCut n z = φₙ(Re z) φₙ(Im z)` with `φₙ(t) = min 1 (max 0 ((n+2) min(t, 1−t) − 1))`:
continuous, `0 ≤ sqCut n ≤ 1`, nondecreasing in `n`, supported in the closed square at distance
`1/(n+2)` from `∂𝕍` (`sqIn (1/(n+2))`), equal to `1` on `sqIn (2/(n+2))`. These are the test
functions through which the vague limit `qAreaMeasureOn` is read in `GMCMoment.lean`
(own elementary construction).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace LQGMetric

/-- the closed square at distance `s` from the boundary of `(0,1)²` -/
def sqIn (s : ℝ) : Set ℂ := {z | s ≤ z.re ∧ z.re ≤ 1 - s ∧ s ≤ z.im ∧ z.im ≤ 1 - s}

/-- the one-dimensional cut-off -/
def cut1 (n : ℕ) (t : ℝ) : ℝ := min 1 (max 0 (((n : ℝ) + 2) * min t (1 - t) - 1))

/-- the cut-off on the square -/
def sqCut (n : ℕ) (z : ℂ) : ℝ := cut1 n z.re * cut1 n z.im

lemma continuous_cut1 (n : ℕ) : Continuous (cut1 n) := by
  unfold cut1; fun_prop

lemma continuous_sqCut (n : ℕ) : Continuous (sqCut n) := by
  unfold sqCut
  exact ((continuous_cut1 n).comp Complex.continuous_re).mul
    ((continuous_cut1 n).comp Complex.continuous_im)

lemma cut1_nonneg (n : ℕ) (t : ℝ) : 0 ≤ cut1 n t := le_min zero_le_one (le_max_left _ _)
lemma cut1_le_one (n : ℕ) (t : ℝ) : cut1 n t ≤ 1 := min_le_left _ _

lemma sqCut_nonneg (n : ℕ) (z : ℂ) : 0 ≤ sqCut n z := mul_nonneg (cut1_nonneg _ _) (cut1_nonneg _ _)
lemma sqCut_le_one (n : ℕ) (z : ℂ) : sqCut n z ≤ 1 :=
  by
  have := cut1_le_one n z.re; have := cut1_le_one n z.im
  have := cut1_nonneg n z.re; have := cut1_nonneg n z.im
  unfold sqCut; nlinarith

lemma cut1_mono (t : ℝ) : Monotone fun n : ℕ => cut1 n t := by
  intro m n hmn
  simp only [cut1]
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  rcases le_total 0 (min t (1 - t)) with h | h
  · exact min_le_min le_rfl (max_le_max le_rfl (by nlinarith))
  · have h1 : ((m : ℝ) + 2) * min t (1 - t) - 1 ≤ 0 := by nlinarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
    rw [max_eq_left h1, min_eq_right zero_le_one]
    exact le_min zero_le_one (le_max_left _ _)

lemma sqCut_mono (z : ℂ) : Monotone fun n : ℕ => sqCut n z := fun m n hmn =>
  mul_le_mul (cut1_mono _ hmn) (cut1_mono _ hmn) (cut1_nonneg _ _) (cut1_nonneg _ _)

lemma cut1_pos_imp {n : ℕ} {t : ℝ} (h : cut1 n t ≠ 0) :
    1 / ((n : ℝ) + 2) ≤ t ∧ t ≤ 1 - 1 / ((n : ℝ) + 2) := by
  have hn : (0 : ℝ) < n + 2 := by positivity
  have hpos : 0 < ((n : ℝ) + 2) * min t (1 - t) - 1 := by
    by_contra hle; push Not at hle
    apply h; simp only [cut1, max_eq_left hle, min_eq_right zero_le_one]
  have hm : 1 / ((n : ℝ) + 2) ≤ min t (1 - t) := by
    rw [div_le_iff₀ hn]; linarith
  exact ⟨hm.trans (min_le_left _ _), by linarith [hm.trans (min_le_right _ _)]⟩

lemma mem_sqIn_of_sqCut_ne_zero {n : ℕ} {z : ℂ} (h : sqCut n z ≠ 0) :
    z ∈ sqIn (1 / ((n : ℝ) + 2)) := by
  have h1 : cut1 n z.re ≠ 0 := fun h0 => h (by simp [sqCut, h0])
  have h2 : cut1 n z.im ≠ 0 := fun h0 => h (by simp [sqCut, h0])
  exact ⟨(cut1_pos_imp h1).1, (cut1_pos_imp h1).2, (cut1_pos_imp h2).1, (cut1_pos_imp h2).2⟩

lemma cut1_eq_one {n : ℕ} {t : ℝ} (h1 : 2 / ((n : ℝ) + 2) ≤ t) (h2 : t ≤ 1 - 2 / ((n : ℝ) + 2)) :
    cut1 n t = 1 := by
  have hn : (0 : ℝ) < n + 2 := by positivity
  have hm : 2 / ((n : ℝ) + 2) ≤ min t (1 - t) := le_min h1 (by linarith)
  rw [div_le_iff₀ hn] at hm
  simp only [cut1]
  rw [max_eq_right (by nlinarith), min_eq_left (by nlinarith)]

lemma sqCut_eq_one {n : ℕ} {z : ℂ} (hz : z ∈ sqIn (2 / ((n : ℝ) + 2))) : sqCut n z = 1 := by
  obtain ⟨a, b, c, d⟩ := hz
  simp [sqCut, cut1_eq_one a b, cut1_eq_one c d]

lemma isClosed_sqIn (s : ℝ) : IsClosed (sqIn s) := by
  have : sqIn s = {z : ℂ | s ≤ z.re} ∩ ({z : ℂ | z.re ≤ 1 - s} ∩ ({z : ℂ | s ≤ z.im} ∩
      {z : ℂ | z.im ≤ 1 - s})) := by ext z; simp [sqIn]
  rw [this]
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

lemma sqIn_subset_openSquare {s : ℝ} (hs : 0 < s) : sqIn s ⊆ openSquare := fun z ⟨a, b, c, d⟩ =>
  ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma isCompact_sqIn {s : ℝ} (hs : 0 < s) : IsCompact (sqIn s) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_sqIn s) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun z hz => ?_
  obtain ⟨a, b, c, d⟩ := sqIn_subset_openSquare hs hz
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  rw [abs_of_pos a, abs_of_pos c]; linarith

lemma tsupport_sqCut_subset (n : ℕ) : tsupport (sqCut n) ⊆ sqIn (1 / ((n : ℝ) + 2)) :=
  closure_minimal (fun _ hz => mem_sqIn_of_sqCut_ne_zero hz) (isClosed_sqIn _)

lemma hasCompactSupport_sqCut (n : ℕ) : HasCompactSupport (sqCut n) :=
  (isCompact_sqIn (by positivity)).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_sqCut_subset n)

lemma tsupport_sqCut_subset_openSquare (n : ℕ) : tsupport (sqCut n) ⊆ openSquare :=
  (tsupport_sqCut_subset n).trans (sqIn_subset_openSquare (by positivity))

end LQGMetric
