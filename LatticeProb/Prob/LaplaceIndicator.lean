import Mathlib
import LatticeProb.Prob.LaplaceInterval
import LatticeProb.Prob.UpcrossLaplace

/-!
# The exponential density integrated over a window of `ℝ≥0∞`

For `q > 0` and `r ≤ s` in `[0, ∞]`, the density `q e^{-q t}` on `[0, ∞)` integrates over
`{t ≥ 0 | r ≤ t < s}` to `e^{-q r} - e^{-q s}` (with `e^{-q ∞} = 0`).
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace LatticeProb

/-- The exponential density `q e^{-q t}` on `[0, ∞)` integrates over the window
`r ≤ t < s` (`r ≤ s` in `[0, ∞]`, compared through `ENNReal.ofReal t`) to
`e^{-q r} - e^{-q s}`, with `e^{-q ∞} = 0`. -/
theorem lintegral_laplace_Ico_ennreal {q : ℝ} (hq : 0 < q) {r s : ℝ≥0∞} (hrs : r ≤ s) :
    ∫⁻ t in Set.Ici (0:ℝ), {t : ℝ | r ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < s}.indicator
      (fun t => ENNReal.ofReal (q * Real.exp (-(q * t)))) t = expNeg q r - expNeg q s := by
  have hmeas : MeasurableSet {t : ℝ | r ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < s} := by
    have h1 : Measurable fun t : ℝ => ENNReal.ofReal t := ENNReal.measurable_ofReal
    exact (measurableSet_le measurable_const h1).inter (measurableSet_lt h1 measurable_const)
  rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas]
  by_cases hr : r = ⊤
  · subst hr
    have hs : s = ⊤ := top_le_iff.1 hrs
    subst hs
    have hset : {t : ℝ | (⊤ : ℝ≥0∞) ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < ⊤} ∩ Set.Ici 0 = ∅ := by
      ext t
      simp
    rw [hset]
    simp
  have hexpr : expNeg q r = ENNReal.ofReal (Real.exp (-(q * r.toReal))) := by
    simp [expNeg, hr, neg_mul]
  by_cases hs : s = ⊤
  · subst hs
    have hset : {t : ℝ | r ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < ⊤} ∩ Set.Ici 0 =
        Set.Ici r.toReal := by
      ext t
      constructor
      · rintro ⟨⟨h1, _⟩, h0⟩
        exact (ENNReal.le_ofReal_iff_toReal_le hr h0).1 h1
      · intro ht
        have h0 : (0 : ℝ) ≤ t := le_trans ENNReal.toReal_nonneg ht
        exact ⟨⟨(ENNReal.le_ofReal_iff_toReal_le hr h0).2 ht, ENNReal.ofReal_lt_top⟩, h0⟩
    rw [hset, lintegral_laplace_Ici hq, hexpr]
    simp
  have hexps : expNeg q s = ENNReal.ofReal (Real.exp (-(q * s.toReal))) := by
    simp [expNeg, hs, neg_mul]
  have hle : r.toReal ≤ s.toReal := ENNReal.toReal_mono hs hrs
  have hset : {t : ℝ | r ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < s} ∩ Set.Ici 0 =
      Set.Ico r.toReal s.toReal := by
    ext t
    constructor
    · rintro ⟨⟨h1, h2⟩, h0⟩
      exact ⟨(ENNReal.le_ofReal_iff_toReal_le hr h0).1 h1,
        (ENNReal.ofReal_lt_iff_lt_toReal h0 hs).1 h2⟩
    · rintro ⟨h1, h2⟩
      have h0 : (0 : ℝ) ≤ t := le_trans ENNReal.toReal_nonneg h1
      exact ⟨⟨(ENNReal.le_ofReal_iff_toReal_le hr h0).2 h1,
        (ENNReal.ofReal_lt_iff_lt_toReal h0 hs).2 h2⟩, h0⟩
  rw [hset, lintegral_laplace_Ico hq hle, hexpr, hexps]

end LatticeProb
