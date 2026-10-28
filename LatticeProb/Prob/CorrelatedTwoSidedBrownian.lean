import LatticeProb.Prob.CorrelatedGaussianProcess
import LatticeProb.Prob.TwoSidedBrownianPair

/-! # Correlated two-sided Brownian pair

A correlation transform of independent two-sided Brownian coordinates, with the
parameter in the open interval where the time-one covariance is positive definite.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The correlation parameter associated to an admissible Brownian coupling parameter. -/
noncomputable def brownianCorrelation (γ : {x : ℝ // 0 < x ∧ x < 2}) : ℝ :=
  -Real.cos (Real.pi * (γ : ℝ) ^ 2 / 4)

/-- The explicitly constructed correlated pair on the fourfold product space. -/
noncomputable def correlatedTwoSidedBrownian (γ : {x : ℝ // 0 < x ∧ x < 2})
    (B : ℝ≥0 → Ω → ℝ) : ℝ × Fin 2 → (Fin 4 → Ω) → ℝ :=
  correlationTransform (brownianCorrelation γ) (twoSidedBrownianPair B)

/-- The correlation is strictly inside the interval `(-1, 1)`. -/
theorem abs_brownianCorrelation_lt_one (γ : {x : ℝ // 0 < x ∧ x < 2}) :
    |brownianCorrelation γ| < 1 := by
  have hp : 0 < (γ : ℝ) ^ 2 := sq_pos_of_pos γ.property.1
  have hq : (γ : ℝ) ^ 2 < 4 := by nlinarith [γ.property.1, γ.property.2]
  have hx : 0 < Real.pi * (γ : ℝ) ^ 2 / 4 := by positivity
  have hy : Real.pi * (γ : ℝ) ^ 2 / 4 < Real.pi := by
    have := Real.pi_pos
    nlinarith
  have hleft := Real.strictAntiOn_cos (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by
      exact ⟨le_rfl, Real.pi_pos.le⟩)
    (show Real.pi * (γ : ℝ) ^ 2 / 4 ∈ Set.Icc 0 Real.pi by exact ⟨hx.le, hy.le⟩) hx
  have hright := Real.strictAntiOn_cos
    (show Real.pi * (γ : ℝ) ^ 2 / 4 ∈ Set.Icc 0 Real.pi by exact ⟨hx.le, hy.le⟩)
    (show Real.pi ∈ Set.Icc 0 Real.pi by exact ⟨Real.pi_pos.le, le_rfl⟩) hy
  simp only [Real.cos_zero] at hleft
  simp only [Real.cos_pi] at hright
  apply abs_lt.mpr
  dsimp [brownianCorrelation]
  constructor <;> linarith

/-- The time-one covariance quadratic form is positive for every nonzero vector. -/
theorem brownian_correlation_quadratic_pos (γ : {x : ℝ // 0 < x ∧ x < 2})
    (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    0 < a ^ 2 + 2 * brownianCorrelation γ * a * b + b ^ 2 := by
  have hρ := abs_lt.mp (abs_brownianCorrelation_lt_one γ)
  have hdet : 0 < 1 - (brownianCorrelation γ) ^ 2 := by nlinarith
  by_cases hb : b = 0
  · subst b
    have ha : a ≠ 0 := h.resolve_right (not_not.mpr rfl)
    have := sq_pos_of_ne_zero ha
    nlinarith
  · have hp := mul_pos hdet (sq_pos_of_ne_zero hb)
    have hs := sq_nonneg (a + brownianCorrelation γ * b)
    nlinarith

/-- Joint law, covariance and path properties of the correlated two-sided pair. -/
theorem correlated_two_sided_brownian (γ : {x : ℝ // 0 < x ∧ x < 2})
    (B : ℝ≥0 → Ω → ℝ) {P : Measure Ω} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω) :
    IsGaussianProcess (correlatedTwoSidedBrownian γ B) (Measure.pi fun _ : Fin 4 => P) ∧
    (∀ p, ∫ ω, correlatedTwoSidedBrownian γ B p ω ∂(Measure.pi fun _ : Fin 4 => P) = 0) ∧
    (∀ s t i j, cov[correlatedTwoSidedBrownian γ B (s, i),
      correlatedTwoSidedBrownian γ B (t, j); Measure.pi fun _ : Fin 4 => P] =
      ((|s| + |t| - |s - t|) / 2) * (if i = j then 1 else brownianCorrelation γ)) ∧
    (∀ p, Measurable (correlatedTwoSidedBrownian γ B p)) ∧
    (∀ i ω, Continuous fun t => correlatedTwoSidedBrownian γ B (t, i) ω) ∧
    (∀ i ω, correlatedTwoSidedBrownian γ B (0, i) ω = 0) := by
  obtain ⟨hG, hmean, hcov, hmeas, hcont, hzero⟩ := two_sided_brownian_pair B hB hm hc
  refine ⟨correlationTransform_isGaussianProcess hG _, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨t, i⟩
    exact correlationTransform_mean hG _ hmean t i
  · intro s t i j
    exact correlationTransform_covariance hG _ (abs_brownianCorrelation_lt_one γ).le
      (fun s t => (|s| + |t| - |s - t|) / 2) hcov s t i j
  · exact correlationTransform_measurable _ _ hmeas
  · exact correlationTransform_continuous _ _ hcont
  · intro i ω
    simp [correlatedTwoSidedBrownian, correlationTransform, hzero]

/-- The time-one covariance matrix is positive definite. -/
theorem correlated_two_sided_brownian_time_one
    (γ : {x : ℝ // 0 < x ∧ x < 2}) (B : ℝ≥0 → Ω → ℝ) {P : Measure Ω}
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) :
    (∀ i j, cov[correlatedTwoSidedBrownian γ B (1, i),
      correlatedTwoSidedBrownian γ B (1, j); Measure.pi fun _ : Fin 4 => P] =
      if i = j then 1 else brownianCorrelation γ) ∧
    (∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      0 < a ^ 2 + 2 * brownianCorrelation γ * a * b + b ^ 2) := by
  refine ⟨?_, brownian_correlation_quadratic_pos γ⟩
  intro i j
  have h := (correlated_two_sided_brownian γ B hB hm hc).2.2.1 1 1 i j
  norm_num at h
  exact h

end LatticeProb
