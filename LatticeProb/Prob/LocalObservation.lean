import Mathlib

/-!
# Recentred, mass-normalized and weighted restrictions of a random measure on `ℂ`

Definitions and their measurability, for a random measure `μ ω` on `ℂ`:

* `recenteredRestriction η r z`: the restriction of `η` to the ball `B_r(z)`, translated by `-z`;
* `massNormalize r η`: the measure `η` divided by its mass on the ball `B_{r/2}(0)`;
* `normalizedRestriction μ U`: the restriction of `μ` to `U`, divided by its mass `μ(U)`;
* `normalizedRestrictionKernel A hA`: the kernel `μ ↦ normalizedRestriction μ A` on the space of measures;
* `weightedRestrictionKernel P μ hμ B hB w hw`: the sampling kernel of the normalized restriction to `B` of the
  measure `μ ω` weighted by a measurable density `w`, for a probability space `(Ω, P)`.

The measurability lemmas `measurable_normalizedRestriction`, `measurable_normalizedRestriction_measure` and
`measurable_measure_withDensity` are needed for the kernels; they are standard measure theory (Mathlib
`Measure.measurable_measure`, `Measurable.measure_of_isPiSystem`, `Measure.measurable_lintegral`).
-/

namespace LatticeProb.Prob

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

/-- The recentred restriction `(T_z)_* (η|B_r(z))` with `T_z x = x - z`. -/
noncomputable def recenteredRestriction (η : Measure ℂ) (r : ℝ) (z : ℂ) : Measure ℂ :=
  (η.restrict (ball z r)).map (fun x : ℂ => x - z)

/-- The mass normalization `η ↦ η(B_{r/2}(0))⁻¹ • η` at scale `r`. -/
noncomputable def massNormalize (r : ℝ) (η : Measure ℂ) : Measure ℂ :=
  (η (ball 0 (r / 2)))⁻¹ • η

/-- The restriction of a measure to a set, normalized by its total mass on that set: `(μ U)⁻¹ • μ|_U`. -/
noncomputable def normalizedRestriction (μ : Measure ℂ) (U : Set ℂ) : Measure ℂ :=
  (μ U)⁻¹ • μ.restrict U

/-- A normalized restriction is finite, including when its original mass is zero or infinite. -/
instance normalizedRestriction_isFiniteMeasure (μ : Measure ℂ) (U : Set ℂ) :
    IsFiniteMeasure (normalizedRestriction μ U) := by
  unfold normalizedRestriction
  simpa only [Measure.restrict_apply_univ] using
    (inferInstance : IsFiniteMeasure (((μ.restrict U) univ)⁻¹ • μ.restrict U))

/-- The normalized restriction is a measurable function of a random measure, as soon as the masses `μ ω (V ∩ U) /
μ ω U` are measurable for every open `V`. -/
theorem measurable_normalizedRestriction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure ℂ) (U : Set ℂ)
    (h : ∀ V : Set ℂ, IsOpen V → Measurable (fun ω => μ ω (V ∩ U) / μ ω U)) :
    Measurable (fun ω => normalizedRestriction (μ ω) U) := by
  apply Measurable.measure_of_isPiSystem BorelSpace.measurable_eq isPiSystem_isOpen
  · intro V hV
    change IsOpen V at hV
    simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hV.measurableSet, ENNReal.div_eq_inv_mul] using h V hV
  · simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply_univ, univ_inter, ENNReal.div_eq_inv_mul] using h univ isOpen_univ

/-- For a measurable set `A`, the normalized restriction to `A` is a measurable function of the measure. -/
theorem measurable_normalizedRestriction_measure (A : Set ℂ) (hA : MeasurableSet A) :
    Measurable (fun μ : Measure ℂ => normalizedRestriction μ A) := by
  apply measurable_normalizedRestriction _ A
  intro V hV
  exact (Measure.measurable_coe (hV.measurableSet.inter hA)).div (Measure.measurable_coe hA)

/-- The normalized restriction to a measurable set `A`, as a kernel from the space of measures to `ℂ`. -/
noncomputable def normalizedRestrictionKernel (A : Set ℂ) (hA : MeasurableSet A) :
    Kernel (Measure ℂ) ℂ :=
  ⟨fun μ => normalizedRestriction μ A, measurable_normalizedRestriction_measure A hA⟩

/-- Weighting by a fixed measurable density is a measurable map on the space of measures. -/
theorem measurable_measure_withDensity (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    Measurable (fun μ : Measure ℂ => μ.withDensity w) := by
  rw [Measure.measurable_measure]
  intro S hS
  simp only [withDensity_apply _ hS, ← lintegral_indicator hS]
  exact Measure.measurable_lintegral (hw.indicator hS)

/-- The normalized restriction to `B` of the measure `μ ω` weighted by the density `w`, as a sampling kernel on
`Ω`. The measurable representative `hν.mk` of the almost-everywhere measurable random measure is used. -/
noncomputable def weightedRestrictionKernel
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    Kernel Ω ℂ :=
  let ν : Ω → Measure ℂ := fun ω => (μ ω).withDensity w
  let hν : AEMeasurable ν P := (measurable_measure_withDensity w hw).comp_aemeasurable hμ
  (normalizedRestrictionKernel B hB).comap (hν.mk ν) hν.measurable_mk

end LatticeProb.Prob
