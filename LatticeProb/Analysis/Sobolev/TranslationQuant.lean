/-
# The quantitative Sobolev translation bound

Completes the analytic half of the Fréchet–Kolmogorov route: for `2πR‖h‖ ≤ 1`,

  `sobolevNormSq d s₀ (φ(·+h) − φ)`
    `≤ (4πR‖h‖)² · sobolevNormSq d s₀ φ + 4 · sobolevNormSqHigh d s₀ R φ`

for a test function `φ`.  The frequency integral is split at `R`: below `R` the phase estimate
`norm_fourierChar_sub_one_le` gives `‖𝐞 ⟪h,ξ⟫ − 1‖ ≤ 4πR‖h‖`, above `R` the trivial bound
`norm_fourierChar_sub_one_le_two` is used.  This yields `BandLimitedTranslationContinuous` by
choosing `R` large (uniform high-frequency smallness, `s₀ < s`) and `‖h‖` small.
-/
import LatticeProb.Analysis.Sobolev.FourierCharPhase

open MeasureTheory Filter
open Set
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **The quantitative translation bound.** -/
theorem sobolevNormSq_translate_sub_le {d : ℕ} (s₀ : ℝ) {R : ℝ} (_hR : 0 ≤ R)
    (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (h : Space d) (hh : 2 * Real.pi * R * ‖h‖ ≤ 1) :
    sobolevNormSq d s₀ (fun x => φ (x + h) - φ x)
      ≤ ENNReal.ofReal ((4 * Real.pi * R * ‖h‖) ^ 2) * sobolevNormSq d s₀ φ
        + 4 * sobolevNormSqHigh d s₀ R φ := by
  set F : Space d → ℂ := 𝓕 (fun x => (φ x : ℂ)) with hF
  have hg : Integrable (fun x : Space d => ((φ x : ℝ) : ℂ)) :=
    (hcont.continuous.integrable_of_hasCompactSupport hcs).ofReal
  have hFcont : Continuous F := by
    rw [hF]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hg
  have hbase : (fun ξ : Space d => 𝓕 (fun x => ((φ (x + h) - φ x : ℝ) : ℂ)) ξ)
      = fun ξ => ((𝐞 (inner ℝ h ξ) : ℂ) - 1) • F ξ := by
    rw [show (fun x : Space d => ((φ (x + h) - φ x : ℝ) : ℂ))
        = fun x : Space d => (fun y : Space d => (φ y : ℂ)) (x + h)
            - (fun y : Space d => (φ y : ℂ)) x from
      funext fun x => by simp [Complex.ofReal_sub]]
    rw [fourier_translate_sub_lift (fun y : Space d => (φ y : ℂ)) h hg (hg.comp_add_right h), hF]
  have hfun : ∀ ξ : Space d, 𝓕 (fun x => ((φ (x + h) - φ x : ℝ) : ℂ)) ξ
      = ((𝐞 (inner ℝ h ξ) : ℂ) - 1) • F ξ := fun ξ => congrFun hbase ξ
  have hrefl : (∫⁻ a : Space d, ENNReal.ofReal
      ((1 + (2 * Real.pi * ‖a‖) ^ 2) ^ s₀ * ‖F a‖ ^ 2)) = sobolevNormSq d s₀ φ := by
    unfold sobolevNormSq
    rw [hF]
  have hhigh : (∫⁻ a : Space d, (({ξ : Space d | R < ‖ξ‖}.indicator
      fun y => ENNReal.ofReal ((1 + (2 * Real.pi * ‖y‖) ^ 2) ^ s₀ * ‖F y‖ ^ 2)) a))
      = sobolevNormSqHigh d s₀ R φ := by
    rw [lintegral_indicator (measurableSet_lt measurable_const measurable_norm)]
    unfold sobolevNormSqHigh
    rw [hF]
  have hmeas : AEMeasurable (fun ξ : Space d =>
      ENNReal.ofReal ((4 * Real.pi * R * ‖h‖) ^ 2)
        * ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ‖F ξ‖ ^ 2)) volume := by
    have h1 : Continuous (fun ξ : Space d => ENNReal.ofReal
        ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ‖F ξ‖ ^ 2)) := by
      refine ENNReal.continuous_ofReal.comp ?_
      refine (((continuous_const.add ((continuous_const.mul continuous_norm).pow 2)).rpow_const
        fun ξ => Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)))).mul
        (hFcont.norm.pow 2))
    exact h1.aemeasurable.const_mul _
  have hpoint : ∀ ξ : Space d, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
      * ‖((𝐞 (inner ℝ h ξ) : ℂ) - 1) • F ξ‖ ^ 2)
      ≤ ENNReal.ofReal ((4 * Real.pi * R * ‖h‖) ^ 2)
          * ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ‖F ξ‖ ^ 2)
        + 4 * (({ξ : Space d | R < ‖ξ‖}.indicator
            fun y => ENNReal.ofReal ((1 + (2 * Real.pi * ‖y‖) ^ 2) ^ s₀ * ‖F y‖ ^ 2)) ξ) := by
    intro ξ
    have hw : 0 ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ :=
      Real.rpow_nonneg (by positivity) s₀
    have hq : 0 ≤ ‖F ξ‖ ^ 2 := sq_nonneg _
    have hnorm : ‖((𝐞 (inner ℝ h ξ) : ℂ) - 1) • F ξ‖
        = ‖(𝐞 (inner ℝ h ξ) : ℂ) - 1‖ * ‖F ξ‖ := norm_smul _ _
    rw [hnorm]
    by_cases hξ : R < ‖ξ‖
    · rw [indicator_of_mem (show ξ ∈ {ξ : Space d | R < ‖ξ‖} from hξ)]
      have hPle : ‖(𝐞 (inner ℝ h ξ) : ℂ) - 1‖ ≤ 2 :=
        norm_fourierChar_sub_one_le_two _
      have hsq : ‖(𝐞 (inner ℝ h ξ) : ℂ) - 1‖ ^ 2 ≤ 4 := by
        nlinarith [hPle, norm_nonneg ((𝐞 (inner ℝ h ξ) : ℂ) - 1)]
      have hreal : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
          * (‖(𝐞 (inner ℝ h ξ) : ℂ) - 1‖ * ‖F ξ‖) ^ 2
          ≤ 4 * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ‖F ξ‖ ^ 2) := by
        calc (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
              * (‖(𝐞 (inner ℝ h ξ) : ℂ) - 1‖ * ‖F ξ‖) ^ 2
            = (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
              * (‖(𝐞 (inner ℝ h ξ) : ℂ) - 1‖ ^ 2 * ‖F ξ‖ ^ 2) := by ring
          _ ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * (4 * ‖F ξ‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hq) hw
          _ = 4 * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ‖F ξ‖ ^ 2) := by ring
      have h4 : (ENNReal.ofReal (4 : ℝ) : ℝ≥0∞) = 4 := by norm_num
      refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
      exact le_add_of_nonneg_left (by positivity)
    · rw [indicator_of_notMem (show ξ ∉ {ξ : Space d | R < ‖ξ‖} from hξ), mul_zero, add_zero]
      have hξle : ‖ξ‖ ≤ R := not_lt.mp hξ
      have hinner : |inner ℝ h ξ| ≤ R * ‖h‖ := by
        calc |inner ℝ h ξ| ≤ ‖h‖ * ‖ξ‖ := abs_real_inner_le_norm h ξ
          _ ≤ ‖h‖ * R := by gcongr
          _ = R * ‖h‖ := by ring
      have hphase : 2 * Real.pi * |inner ℝ h ξ| ≤ 1 := by
        calc 2 * Real.pi * |inner ℝ h ξ| ≤ 2 * Real.pi * (R * ‖h‖) := by gcongr
          _ = 2 * Real.pi * R * ‖h‖ := by ring
          _ ≤ 1 := hh
      have hPle : ‖(𝐞 (inner ℝ h ξ) : ℂ) - 1‖ ≤ 4 * Real.pi * R * ‖h‖ := by
        refine (norm_fourierChar_sub_one_le hphase).trans ?_
        calc 4 * Real.pi * |inner ℝ h ξ| ≤ 4 * Real.pi * (R * ‖h‖) := by gcongr
          _ = 4 * Real.pi * R * ‖h‖ := by ring
      have hsq : ‖(𝐞 (inner ℝ h ξ) : ℂ) - 1‖ ^ 2 ≤ (4 * Real.pi * R * ‖h‖) ^ 2 := by
        nlinarith [hPle, norm_nonneg ((𝐞 (inner ℝ h ξ) : ℂ) - 1)]
      have hreal : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
          * (‖(𝐞 (inner ℝ h ξ) : ℂ) - 1‖ * ‖F ξ‖) ^ 2
          ≤ (4 * Real.pi * R * ‖h‖) ^ 2
            * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ‖F ξ‖ ^ 2) := by
        calc (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
              * (‖(𝐞 (inner ℝ h ξ) : ℂ) - 1‖ * ‖F ξ‖) ^ 2
            = (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
              * (‖(𝐞 (inner ℝ h ξ) : ℂ) - 1‖ ^ 2 * ‖F ξ‖ ^ 2) := by ring
          _ ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ((4 * Real.pi * R * ‖h‖) ^ 2 * ‖F ξ‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hq) hw
          _ = (4 * Real.pi * R * ‖h‖) ^ 2
              * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ‖F ξ‖ ^ 2) := by ring
      exact (ENNReal.ofReal_le_ofReal hreal).trans
        (le_of_eq (ENNReal.ofReal_mul (sq_nonneg _)))
  have hLHS : sobolevNormSq d s₀ (fun x => φ (x + h) - φ x)
      = ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
          * ‖((𝐞 (inner ℝ h ξ) : ℂ) - 1) • F ξ‖ ^ 2) := by
    unfold sobolevNormSq
    refine lintegral_congr fun ξ => ?_
    show ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
        * ‖𝓕 (fun x => ((φ (x + h) - φ x : ℝ) : ℂ)) ξ‖ ^ 2) = _
    rw [hfun ξ]
  refine le_trans (le_of_eq hLHS) ?_
  refine le_trans (lintegral_mono hpoint) ?_
  rw [lintegral_add_left' hmeas,
    lintegral_const_mul' (ENNReal.ofReal ((4 * Real.pi * R * ‖h‖) ^ 2))
      (fun a => ENNReal.ofReal ((1 + (2 * Real.pi * ‖a‖) ^ 2) ^ s₀ * ‖F a‖ ^ 2))
      ENNReal.ofReal_ne_top,
    lintegral_const_mul' 4
      (fun a => (({ξ : Space d | R < ‖ξ‖}.indicator
        fun y => ENNReal.ofReal ((1 + (2 * Real.pi * ‖y‖) ^ 2) ^ s₀ * ‖F y‖ ^ 2)) a))
      (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    hrefl, hhigh]

end LatticeProb.Sobolev
