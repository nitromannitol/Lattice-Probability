import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF

/-!
# The whole-plane GFF on the Polish space `ℕ → ℝ`

`exists_wholePlaneGFF_nat` and `exists_normalizedWPGFF_nat` are the statements of `exists_wholePlaneGFF` and
`exists_normalizedWPGFF` with the sample space made explicit: the whole-plane Gaussian free field (as a random
distribution), respectively its normalization `h_1(0) = 0`, is defined on `(ℕ → ℝ, P)`, a Polish space with its
Borel σ-algebra (a standard Borel space). The proofs are those of the two theorems cited, the existential over the
sample space being replaced by the sample space of the construction (the countable product of lines carrying the
space-time white noise).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace GFFExist

open WhiteNoise

/-- **Existence of the whole-plane GFF** as a random distribution on the Polish space `ℕ → ℝ`. -/
theorem exists_wholePlaneGFF_nat :
    ∃ (P : Measure (ℕ → ℝ)) (h : (ℕ → ℝ) → DistC),
      IsProbabilityMeasure P ∧ IsWholePlaneGFF h P := by
  obtain ⟨W, hW⟩ := exists_isWhiteNoise
  have hP := hW.isProbabilityMeasure
  obtain ⟨Y, hYc, hYm, hYW⟩ := exists_continuous_rectField hW
  refine ⟨LQGDimension.ExistAsm.stdP, gffOf Y hYc, hP, ?_⟩
  have hae : ∀ φ : TestC, (fun ω => gffOf Y hYc ω φ) =ᵐ[LQGDimension.ExistAsm.stdP]
      W (testL2 φ) := fun φ => by
    simpa only [gffOf_apply] using ae_integral_d12_mul_eq hW hYc hYm hYW φ
  have hmean : ∀ φ : TestC, ∫ ω, gffOf Y hYc ω φ ∂LQGDimension.ExistAsm.stdP = 0 := fun φ => by
    rw [integral_congr_ae (hae φ),
      QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _)]
  refine ⟨measurable_gffOf Y hYc hYm, ?_, fun φ => hmean φ.1, ?_⟩
  · exact (hW.isGaussianProcess_comp (fun φ : TestC0 => testL2 φ.1)).congr
      (fun φ => (hae φ.1).symm)
  · intro φ ψ
    have hm1 := (wn_memLp hW (testL2 φ.1)).ae_eq (hae φ.1).symm
    have hm2 := (wn_memLp hW (testL2 ψ.1)).ae_eq (hae ψ.1).symm
    rw [covariance_eq_sub hm1 hm2, hmean φ.1, zero_mul, sub_zero,
      integral_congr_ae ((hae φ.1).mul (hae ψ.1))]
    have := wn_integral_mul hW (testL2 φ.1) (testL2 ψ.1)
    simp only [Pi.mul_apply]
    rw [this, inner_testL2_testL2 φ.1 ψ.1 φ.2 ψ.2]

/-- **Existence of a normalized whole-plane GFF** (`h_1(0) = 0` almost surely) on the Polish space `ℕ → ℝ`. -/
theorem exists_normalizedWPGFF_nat :
    ∃ (P : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P) (h : (ℕ → ℝ) → DistC),
      IsNormalizedWPGFF h P := by
  obtain ⟨P, h, hP, hh⟩ := exists_wholePlaneGFF_nat
  have hc : Measurable fun ω => -circleAvg (h ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).neg
  refine ⟨P, hP, fun ω => addConst (h ω) (-circleAvg (h ω) 1 0), hh.addConst hc, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
  rw [hω, add_neg_cancel]

end GFFExist
end LQGMetric
