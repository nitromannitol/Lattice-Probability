/-
# Band-limited compactness and translation continuity as theorems

`BandLimitedPrecompact` is the finite-net form of the Rellich–Kondrachov embedding
`rellichKondrachovNegSobolev_holds`, taken at accuracy `η = √δ`; the low-frequency net
`rkLowFreqNet` follows from it.  `BandLimitedTranslationContinuous` follows from the
quantitative translation bound `sobolevNormSq_translate_sub_le` together with the uniform
high-frequency truncation `exists_sobolevNormSqHigh_le_truncation` of the `H^s` unit ball.
-/
import LatticeProb.Analysis.Sobolev.RellichConvolvedCompact
import LatticeProb.Analysis.Sobolev.TranslationQuant
import LatticeProb.Analysis.Sobolev.FrechetKolmogorov
import LatticeProb.Analysis.Sobolev.Truncation

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Sobolev

/-- The `H^s` unit ball of test functions on a bounded domain has, for every accuracy `δ > 0`,
a finite net of test functions in the `H^{s₀}` norm (`s₀ < s`). -/
theorem bandLimitedPrecompact_holds : BandLimitedPrecompact := by
  intro d D hD s₀ s hlt δ hδ
  obtain ⟨N, ψ, hψ, hnet⟩ :=
    rellichKondrachovNegSobolev_holds d D hD s₀ s hlt (Real.sqrt δ) (Real.sqrt_pos.2 hδ)
  refine ⟨N, ψ, hψ, fun φ hφ hφn => ?_⟩
  obtain ⟨i, hi⟩ := hnet φ hφ hφn
  exact ⟨i, by rwa [Real.sq_sqrt hδ.le] at hi⟩

/-- The low-frequency net statement holds. -/
theorem rkLowFreqNet_holds : rkLowFreqNet :=
  rkLowFreqNet_of_bandLimitedPrecompact bandLimitedPrecompact_holds

/-- The `H^s` unit ball of test functions on a bounded domain is uniformly
translation-continuous in the `H^{s₀}` norm (`s₀ < s`). -/
theorem bandLimitedTranslationContinuous_holds : BandLimitedTranslationContinuous := by
  intro d D _hD s₀ s hlt η hη
  obtain ⟨R, hR, htail⟩ := exists_sobolevNormSqHigh_le_truncation (d := d) hlt
    (Real.sqrt (η / 8)) (Real.sqrt_pos.2 (by positivity))
  have hπ : 0 < Real.pi := Real.pi_pos
  have hR1 : 0 < R + 1 := by linarith
  have hA : 0 < 2 * Real.pi * (R + 1) := by positivity
  have hB : 0 < 4 * Real.pi * (R + 1) := by positivity
  have hsq : 0 < Real.sqrt (η / 2) := Real.sqrt_pos.2 (by positivity)
  refine ⟨min (1 / (2 * Real.pi * (R + 1))) (Real.sqrt (η / 2) / (4 * Real.pi * (R + 1))),
    lt_min (by positivity) (by positivity), fun h hh φ hφ hφn => ?_⟩
  have hn0 : 0 ≤ ‖h‖ := norm_nonneg h
  have hh1 : ‖h‖ * (2 * Real.pi * (R + 1)) ≤ 1 :=
    (le_div_iff₀ hA).1 (hh.le.trans (min_le_left _ _))
  have hh2 : ‖h‖ * (4 * Real.pi * (R + 1)) ≤ Real.sqrt (η / 2) :=
    (le_div_iff₀ hB).1 (hh.le.trans (min_le_right _ _))
  have hπh : 0 ≤ Real.pi * ‖h‖ := mul_nonneg hπ.le hn0
  have hc1 : 2 * Real.pi * R * ‖h‖ ≤ 1 := by nlinarith
  have hc0 : 0 ≤ 4 * Real.pi * R * ‖h‖ := by positivity
  have hc2 : (4 * Real.pi * R * ‖h‖) ^ 2 ≤ η / 2 := by
    have hle : 4 * Real.pi * R * ‖h‖ ≤ Real.sqrt (η / 2) := by nlinarith
    calc (4 * Real.pi * R * ‖h‖) ^ 2 ≤ Real.sqrt (η / 2) ^ 2 :=
          pow_le_pow_left₀ hc0 hle 2
      _ = η / 2 := Real.sq_sqrt (by positivity)
  have hφ0 : sobolevNormSq d s₀ φ ≤ 1 := (sobolevNormSq_mono hlt.le φ).trans hφn
  have ht := htail φ hφn
  rw [Real.sq_sqrt (by positivity)] at ht
  calc sobolevNormSq d s₀ (fun x => φ (x + h) - φ x)
      ≤ ENNReal.ofReal ((4 * Real.pi * R * ‖h‖) ^ 2) * sobolevNormSq d s₀ φ
        + 4 * sobolevNormSqHigh d s₀ R φ :=
        sobolevNormSq_translate_sub_le s₀ hR φ hφ.1 hφ.2.1 h hc1
    _ ≤ ENNReal.ofReal (η / 2) * 1 + 4 * ENNReal.ofReal (η / 8) := by
        gcongr
    _ = ENNReal.ofReal η := by
        rw [mul_one, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end LatticeProb.Sobolev
