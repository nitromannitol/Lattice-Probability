import LatticeProb.LQG.RadialSpliceLateralIndep

/-! # Brownian law of the exterior radial process -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- Any fixed-time version of the centered radial process has its Gaussian law,
mean and covariance. -/
theorem IsWholePlaneGFF.radialVersion_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {ρ : Ω → C(ℝ, ℝ)}
    (hρ : ∀ t, (fun ω => ρ ω t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0) :
    IsGaussianProcess (fun t ω => ρ ω t) P ∧
      (∀ t, ∫ ω, ρ ω t ∂P = 0) ∧
      ∀ s t, cov[fun ω => ρ ω s, fun ω => ρ ω t; P] = radCov s t := by
  obtain ⟨R, -, hR, hRg, hR0, hRc⟩ := exists_radialProcess hX
  have heq : ∀ t, (fun ω => R ω t) =ᵐ[P] fun ω => ρ ω t :=
    fun t => (hR t).trans (hρ t).symm
  refine ⟨hRg.congr heq, ?_, ?_⟩
  · intro t
    rw [← integral_congr_ae (heq t)]
    exact hR0 t
  · intro s t
    rw [← covariance_congr_ae (heq s) (heq t)]
    exact hRc s t

/-- The exterior half of a centered radial version is a pre-Brownian motion. -/
theorem IsWholePlaneGFF.radialVersion_exterior_isPreBrownianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {ρ : Ω → C(ℝ, ℝ)}
    (hρ : ∀ t, (fun ω => ρ ω t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0) :
    IsPreBrownianReal (fun t ω => ρ ω (-(t : ℝ))) P := by
  obtain ⟨hG, h0, hcov⟩ := IsWholePlaneGFF.radialVersion_gaussian hX hρ
  refine (hG.comp_right (fun t : ℝ≥0 => -(t : ℝ))).isPreBrownianReal_of_covariance
    (fun t => h0 _) ?_
  intro s t hst
  change cov[fun ω => ρ ω (-(s : ℝ)), fun ω => ρ ω (-(t : ℝ)); P] = (s : ℝ)
  rw [hcov]
  have hst' : (s : ℝ) ≤ t := hst
  have hs : 0 ≤ (s : ℝ) := s.coe_nonneg
  have ht : 0 ≤ (t : ℝ) := t.coe_nonneg
  simp only [radCov, neg_neg, min_eq_right (neg_le_neg hst'), max_eq_left hs,
    max_eq_left ht]
  ring

end LatticeProb.LQG
