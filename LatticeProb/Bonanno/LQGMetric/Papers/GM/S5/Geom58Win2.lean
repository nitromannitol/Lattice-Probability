/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58Win2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Win

/-!
# GM Lemma 5.8: windows of points on the upper part of `∂B_r(0)` (task P2-M2L58b)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Steps 1–2 (l. 3069–3081). Own explicit choice (GM's points are equally spaced on the
whole circle; with D69's horizontal stubs we use windows on the upper part of the circle, where it
is a graph over the real axis): `winPt r R c j = t_j + i √(r² − t_j²)`, `t_j = c + 10 R j`.
For `t_j, t_{j+1} ∈ [−r/2, r/2]` the staircase between consecutive points lies in the closed
annulus `r/2 ≤ |w| ≤ r + 5R` (`stair_norm`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM

/-- the `j`-th point of the window at `c` -/
def winPt (r R c : ℝ) (j : ℕ) : ℂ := ⟨c + 10 * R * j, Real.sqrt (r ^ 2 - (c + 10 * R * j) ^ 2)⟩

lemma winPt_re (r R c : ℝ) (j : ℕ) : (winPt r R c j).re = c + 10 * R * j := rfl

lemma winPt_im (r R c : ℝ) (j : ℕ) :
    (winPt r R c j).im = Real.sqrt (r ^ 2 - (c + 10 * R * j) ^ 2) := rfl

lemma norm_sq_eq_re_im (p : ℂ) : ‖p‖ ^ 2 = p.re ^ 2 + p.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma norm_winPt {r R c : ℝ} (hr : 0 ≤ r) {j : ℕ} (hj : |c + 10 * R * j| ≤ r) :
    ‖winPt r R c j‖ = r := by
  have h1 : (c + 10 * R * j) ^ 2 ≤ r ^ 2 := sq_le_sq' (abs_le.1 hj).1 (abs_le.1 hj).2
  have h2 : ‖winPt r R c j‖ ^ 2 = r ^ 2 := by
    rw [norm_sq_eq_re_im, winPt_re, winPt_im, Real.sq_sqrt (by linarith)]; ring
  have := norm_nonneg (winPt r R c j)
  nlinarith [sq_nonneg (‖winPt r R c j‖ - r), sq_nonneg (‖winPt r R c j‖ + r)]

/-- distinct window points are `10R` apart -/
lemma winPt_sep {r R c : ℝ} (hR : 0 < R) {j j' : ℕ} (hne : j ≠ j') :
    10 * R ≤ dist (winPt r R c j) (winPt r R c j') := by
  refine le_trans ?_ (dist_ge_re _ _)
  rw [winPt_re, winPt_re]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
    rw [abs_of_nonpos (by nlinarith)]; nlinarith
  · have : (j' : ℝ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_nonneg (by nlinarith)]; nlinarith

/-- the norm bound behind `stair_norm` -/
lemma stair_norm_aux {r R a b : ℝ} (hr : 0 < r) (hR : 0 < R) (hj : |a| ≤ r / 2)
    (hj' : |b| ≤ r / 2) (hab : b = a + 10 * R) {p : ℂ} (hp1 : a + 2 * R ≤ p.re)
    (hp2 : p.re ≤ b - 2 * R)
    (him : (p.im = Real.sqrt (r ^ 2 - a ^ 2) ∨ p.im = Real.sqrt (r ^ 2 - b ^ 2)) ∨
      (min (Real.sqrt (r ^ 2 - a ^ 2)) (Real.sqrt (r ^ 2 - b ^ 2)) ≤ p.im ∧
        p.im ≤ max (Real.sqrt (r ^ 2 - a ^ 2)) (Real.sqrt (r ^ 2 - b ^ 2)))) :
    r / 2 ≤ ‖p‖ ∧ ‖p‖ ≤ r + 5 * R := by
  have ha2 : a ^ 2 ≤ r ^ 2 / 4 := by
    have := sq_le_sq' (abs_le.1 hj).1 (abs_le.1 hj).2; nlinarith
  have hb2 : b ^ 2 ≤ r ^ 2 / 4 := by
    have := sq_le_sq' (abs_le.1 hj').1 (abs_le.1 hj').2; nlinarith
  have hr2 : 0 < r ^ 2 := by positivity
  have hsa : Real.sqrt (r ^ 2 - a ^ 2) ^ 2 = r ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith)
  have hsb : Real.sqrt (r ^ 2 - b ^ 2) ^ 2 = r ^ 2 - b ^ 2 := Real.sq_sqrt (by linarith)
  have hsa0 := Real.sqrt_nonneg (r ^ 2 - a ^ 2)
  have hsb0 := Real.sqrt_nonneg (r ^ 2 - b ^ 2)
  have hlo : r ^ 2 - r ^ 2 / 4 ≤ p.im ^ 2 ∧ 0 ≤ p.im := by
    have hA : r ^ 2 - r ^ 2 / 4 ≤ Real.sqrt (r ^ 2 - a ^ 2) ^ 2 := by rw [hsa]; linarith
    have hB : r ^ 2 - r ^ 2 / 4 ≤ Real.sqrt (r ^ 2 - b ^ 2) ^ 2 := by rw [hsb]; linarith
    rcases him with (h | h) | ⟨h1, h2⟩
    · rw [h]; exact ⟨hA, hsa0⟩
    · rw [h]; exact ⟨hB, hsb0⟩
    · rcases min_choice (Real.sqrt (r ^ 2 - a ^ 2)) (Real.sqrt (r ^ 2 - b ^ 2)) with e | e <;>
        rw [e] at h1
      · exact ⟨by nlinarith, by linarith⟩
      · exact ⟨by nlinarith, by linarith⟩
  have hhi : p.im ^ 2 ≤ r ^ 2 - min (a ^ 2) (b ^ 2) := by
    have hA : Real.sqrt (r ^ 2 - a ^ 2) ^ 2 ≤ r ^ 2 - min (a ^ 2) (b ^ 2) := by
      rw [hsa]; linarith [min_le_left (a ^ 2) (b ^ 2)]
    have hB : Real.sqrt (r ^ 2 - b ^ 2) ^ 2 ≤ r ^ 2 - min (a ^ 2) (b ^ 2) := by
      rw [hsb]; linarith [min_le_right (a ^ 2) (b ^ 2)]
    rcases him with (h | h) | ⟨h1, h2⟩
    · rw [h]; exact hA
    · rw [h]; exact hB
    · have h0 := hlo.2
      rcases max_choice (Real.sqrt (r ^ 2 - a ^ 2)) (Real.sqrt (r ^ 2 - b ^ 2)) with e | e <;>
        rw [e] at h2
      · nlinarith
      · nlinarith
  have hre2 : p.re ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
    rcases le_total 0 p.re with h | h
    · refine (pow_le_pow_left₀ h (show p.re ≤ |b| by linarith [le_abs_self b]) 2).trans ?_
      rw [sq_abs]; exact le_max_right _ _
    · have : p.re ^ 2 = (-p.re) ^ 2 := by ring
      rw [this]
      refine (pow_le_pow_left₀ (by linarith) (show -p.re ≤ |a| by
        linarith [neg_abs_le a]) 2).trans ?_
      rw [sq_abs]; exact le_max_left _ _
  have hsq := norm_sq_eq_re_im p
  have hn0 := norm_nonneg p
  have hmm : max (a ^ 2) (b ^ 2) - min (a ^ 2) (b ^ 2) ≤ 10 * R * r := by
    rcases le_total (a ^ 2) (b ^ 2) with h | h
    · rw [max_eq_right h, min_eq_left h, hab]
      have := abs_le.1 hj; have := abs_le.1 hj'
      nlinarith
    · rw [max_eq_left h, min_eq_right h, hab]
      have := abs_le.1 hj; have := abs_le.1 hj'
      nlinarith
  constructor
  · nlinarith [sq_nonneg (‖p‖ - r / 2)]
  · nlinarith [sq_nonneg (‖p‖ - (r + 5 * R))]


/-- the staircase between consecutive window points stays in `r/2 ≤ |w| ≤ r + 5R` -/
lemma stair_norm {r R c : ℝ} (hr : 0 < r) (hR : 0 < R) {j : ℕ}
    (hj : |c + 10 * R * j| ≤ r / 2) (hj' : |c + 10 * R * (j + 1 : ℕ)| ≤ r / 2) {p : ℂ}
    (hp : p ∈ stair R (winPt r R c j) (winPt r R c (j + 1))) :
    r / 2 ≤ ‖p‖ ∧ ‖p‖ ≤ r + 5 * R := by
  have h7 : (winPt r R c j).re + 7 * R ≤ (winPt r R c (j + 1)).re := by
    rw [winPt_re, winPt_re]; push_cast; nlinarith
  obtain ⟨hp1, hp2, hp3⟩ := mem_stair hR.le h7 hp
  rw [winPt_re] at hp1 hp2
  rw [winPt_im, winPt_im] at hp3
  refine stair_norm_aux hr hR hj hj' (by push_cast; ring) hp1 hp2 ?_
  rcases hp3 with ⟨h, -⟩ | ⟨-, h1, h2⟩ | ⟨h, -⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl (Or.inr h)

end LQGMetric.GM
