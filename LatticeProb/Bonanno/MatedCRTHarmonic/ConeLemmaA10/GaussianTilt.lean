/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.GaussianTilt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGauss

/-!
# The finite circle-regularization Gaussian tilt

This is the exact finite-regularization Cameron--Martin step in the whole-plane clause of
DMS14 Lemma A.10. For a fixed point `z`, circle radius `ε`, and smooth approximation level
`n`, weight a normalized whole-plane GFF by the Wick exponential of

`γ (h(circBump n z ε) - h(circBump n 0 1))`.

The law of all mean-zero pairings is then translated by its covariance with this random
variable. The subtraction at `(0, 1)` is forced by the additive-constant normalization and
makes the regularizing test function mean zero. The result is a direct specialization of the
Gaussian-process Cameron--Martin theorem; no limiting or GMC assumption is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- The mean-zero test function for the finite approximation of
`h_ε(z) - h_1(0)`. -/
abbrev finiteCircleIndex (n : ℕ) (z : ℂ) (ε : ℝ) : TestC0 :=
  circDiff n z ε n 0 1

/-- The exact Wick density used to root the finite circle regularization at `z`. -/
def finiteCircleDensity (γ : ℝ) (n : ℕ) (z : ℂ) (ε : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal <| Real.exp <|
    γ * (mollAvg (h ω) n z ε - mollAvg (h ω) n 0 1) -
      γ ^ 2 * logCov (finiteCircleIndex n z ε).1 (finiteCircleIndex n z ε).1 / 2

/-- **Finite-radius Gaussian tilt.** Under the Wick-weighted law at the fixed point `z` and
radius `ε`, the full path of mean-zero GFF pairings is translated by
`γ Cov(⟨h, ψ⟩, h_ε(z) - h_1(0))`.

The smoothing level `n` is explicit. This is the exact finite approximation used before the
circle-average/GMC limit in DMS14 Lemma A.10. -/
theorem map_finiteCircleTilt_eq_covShift (hh : IsNormalizedWPGFF h P) (γ : ℝ) (n : ℕ)
    (z : ℂ) (ε : ℝ) :
    (P.withDensity (finiteCircleDensity (h := h) γ n z ε)).map (fun ω => pair0 (h ω)) =
      P.map fun ω ψ =>
        pair0 (h ω) ψ + γ * logCov ψ.1 (finiteCircleIndex n z ε).1 := by
  let ρ : TestC0 := finiteCircleIndex n z ε
  let σ : TestC0 →₀ ℝ := Finsupp.single ρ γ
  have hmeas : ∀ ψ : TestC0, Measurable (pairProc h ψ) := fun ψ =>
    (measurable_evalDist ψ.1).comp hh.1.measurable
  have hcov : ∀ ψ ρ : TestC0,
      QuantumZipper.CameronMartin.covK (pairProc h) P ψ ρ = logCov ψ.1 ρ.1 := by
    intro ψ ρ
    exact hh.1.covariance_eq ψ ρ
  have key := QuantumZipper.CameronMartin.map_tiltMeasure_path
    (gaussian_pairProc hh.1) hmeas (centered_pairProc hh.1) σ
  have htilt :
      QuantumZipper.CameronMartin.tiltMeasure (pairProc h) P σ =
        P.withDensity (finiteCircleDensity (h := h) γ n z ε) := by
    unfold QuantumZipper.CameronMartin.tiltMeasure finiteCircleDensity
    congr 1
    funext ω
    congr 1
    unfold QuantumZipper.CameronMartin.tiltDensity
      QuantumZipper.CameronMartin.comb QuantumZipper.CameronMartin.covNorm
      QuantumZipper.CameronMartin.covShift
    by_cases hγ : γ = 0
    · subst γ
      simp [σ]
    · simp only [σ, Finsupp.support_single _ hγ, Finset.sum_singleton,
        Finsupp.single_eq_same, hcov]
      rw [mollAvg_sub_eq]
      dsimp [ρ, pairProc]
      ring_nf
  rw [htilt] at key
  exact key.trans (Measure.map_congr (ae_of_all _ fun ω => by
    funext ψ
    change pair0 (h ω) ψ + _ = pair0 (h ω) ψ + _
    unfold QuantumZipper.CameronMartin.covShift
    by_cases hγ : γ = 0
    · subst γ
      simp [σ]
    · simp only [σ, Finsupp.support_single _ hγ, Finset.sum_singleton,
        Finsupp.single_eq_same, hcov]
      dsimp [ρ]))

end MatedCRTHarmonic.ConeLemmaA10

