import Mathlib

/-!
# Paths that agree after a time shift

Let `f, g : ℝ≥0 → E` be two paths in a pseudo-metric space, stopped at times `τf, τg`, and suppose that
`f` and `g` become equal after the random shifts `Tf` and `Tg` of at most `r`:
`f ((t + Tf) ∧ τf) = g ((t + Tg) ∧ τg)` for every `t ≥ 0`.  If both paths have oscillation at most
`ε` over time windows of length at most `r` before their stopping times, and the starting points are
at distance at most `η`, then the stopped paths are uniformly at distance at most `2 ε + η`
(`dist_stopped_le_of_shift_coupled`).

Before the shift the paths are within `ε` of their starting points, and after the shift the two
arguments of the common path differ by at most `|Tf - Tg| ≤ r`.  This is the deterministic step in the
proof that the laws of two stopped random walks, started at nearby points, are close in the
Lévy–Prokhorov distance: a coupling under which the walks agree after their exit times from a ball
yields the uniform bound with high probability, and the Lévy–Prokhorov distance is at most the
coupling failure probability and the uniform bound.
-/

open scoped NNReal

namespace LatticeProb

variable {E : Type*} [PseudoMetricSpace E]

lemma nnreal_dist_zero_le {a r : ℝ≥0} (h : a ≤ r) : dist a 0 ≤ r := by
  rw [NNReal.dist_eq]
  simpa using h

lemma nnreal_dist_min_le {a b c r : ℝ≥0} (hab : dist a b ≤ r) : dist (min a c) (min b c) ≤ r := by
  rw [NNReal.dist_eq] at hab ⊢
  rw [NNReal.coe_min, NNReal.coe_min]
  refine le_trans (abs_min_sub_min_le_max _ _ _ _) ?_
  simpa using hab

/-- **Paths coupled after a time shift.**  If `f ((t + Tf) ∧ τf) = g ((t + Tg) ∧ τg)` for all `t ≥ 0`
with `Tf, Tg ≤ r`, both paths oscillate by at most `ε` over windows of length at most `r` before their
stopping times, and `dist (f 0) (g 0) ≤ η`, then the stopped paths satisfy
`dist (f (s ∧ τf)) (g (s ∧ τg)) ≤ 2 ε + η` for every `s ≥ 0`. -/
theorem dist_stopped_le_of_shift_coupled (f g : ℝ≥0 → E) (τf τg Tf Tg r : ℝ≥0) {ε η : ℝ}
    (hTf : Tf ≤ r) (hTg : Tg ≤ r)
    (hf : ∀ s t, s ≤ τf → t ≤ τf → dist s t ≤ r → dist (f s) (f t) ≤ ε)
    (hg : ∀ s t, s ≤ τg → t ≤ τg → dist s t ≤ r → dist (g s) (g t) ≤ ε)
    (h0 : dist (f 0) (g 0) ≤ η)
    (hcoup : ∀ t, f (min (t + Tf) τf) = g (min (t + Tg) τg)) (s : ℝ≥0) :
    dist (f (min s τf)) (g (min s τg)) ≤ 2 * ε + η := by
  by_cases hs : s ≤ r
  · have h1 : dist (f (min s τf)) (f 0) ≤ ε :=
      hf _ _ (min_le_right _ _) zero_le (nnreal_dist_zero_le ((min_le_left _ _).trans hs))
    have h3 : dist (g 0) (g (min s τg)) ≤ ε :=
      hg _ _ zero_le (min_le_right _ _)
        (by rw [dist_comm]; exact nnreal_dist_zero_le ((min_le_left _ _).trans hs))
    have h2 := dist_triangle (f (min s τf)) (f 0) (g (min s τg))
    have h4 := dist_triangle (f 0) (g 0) (g (min s τg))
    linarith
  · have hsr : r ≤ s := (not_le.1 hs).le
    have hε : 0 ≤ ε := le_trans dist_nonneg (hf 0 0 zero_le zero_le (by simp))
    have hη : 0 ≤ η := le_trans dist_nonneg h0
    have hTfs : Tf ≤ s := hTf.trans hsr
    have key := hcoup (s - Tf)
    rw [tsub_add_cancel_of_le hTfs] at key
    rw [key]
    have hdist : dist (s - Tf + Tg) s ≤ r := by
      rw [NNReal.dist_eq, NNReal.coe_add, NNReal.coe_sub hTfs]
      have h1 : (Tf : ℝ) ≤ r := by exact_mod_cast hTf
      have h2 : (Tg : ℝ) ≤ r := by exact_mod_cast hTg
      have h3 : (0 : ℝ) ≤ Tf := Tf.coe_nonneg
      have h4 : (0 : ℝ) ≤ Tg := Tg.coe_nonneg
      rw [abs_le]
      constructor <;> linarith
    refine le_trans (hg _ _ (min_le_right _ _) (min_le_right _ _) (nnreal_dist_min_le hdist)) ?_
    linarith

end LatticeProb
