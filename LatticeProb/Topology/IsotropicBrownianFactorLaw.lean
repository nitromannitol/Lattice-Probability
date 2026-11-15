import LatticeProb.Bonanno.ReflectedGMS.Process.QuenchedLimit

/-! # Isotropic Brownian covariance and its path law -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal
open ReflectedGMS.StatementIngredients

namespace LatticeProb

noncomputable section

/-- A path law with isotropic covariance is the scalar image of its base law
when that law is invariant under orthogonal linear maps. -/
theorem isotropicBrownian_pathLaw_eq_scalar_image
    (target : AnisotropicBrownianTarget) {c : ℝ≥0} (hc : 0 < c)
    (hcov : target.covariance = (c : ℝ) • 1)
    (horth : ∀ O : Matrix (Fin 2) (Fin 2) ℝ, O.transpose * O = 1 →
      (target.standardLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map
        (linearImageBrownianPath O) = target.standardLaw) :
    (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) =
      (target.standardLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map
        (linearImageBrownianPath ((NNReal.sqrt c : ℝ) • 1)) := by
  set s : ℝ≥0 := NNReal.sqrt c with hs_def
  have hs : 0 < s := NNReal.sqrt_pos.2 hc
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hss : (s : ℝ) * s = c := by
    rw [hs_def, ← NNReal.coe_mul, NNReal.mul_self_sqrt]
  set A := target.factor with hA
  have hAA : A * A.transpose = (c : ℝ) • 1 := by
    rw [← hcov, target.covariance_eq]
    rfl
  set O : Matrix (Fin 2) (Fin 2) ℝ := (s : ℝ)⁻¹ • A with hO_def
  have hOO : O * O.transpose = 1 := by
    rw [hO_def, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul,
      smul_smul, ← hss]
    rw [show (s : ℝ)⁻¹ * (s : ℝ)⁻¹ * ((s : ℝ) * s) = 1 by field_simp, one_smul]
  have hO : O.transpose * O = 1 := mul_eq_one_comm.1 hOO
  have hfac : linearImageBrownianPath A =
      linearImageBrownianPath ((s : ℝ) • 1) ∘ linearImageBrownianPath O := by
    funext ω
    ext t i
    fin_cases i <;>
      simp [linearImageBrownianPath_apply, Fin.sum_univ_two, hO_def, Matrix.one_apply] <;>
      field_simp
  rw [AnisotropicBrownianTarget.pathLaw, anisotropicBrownianLaw, ProbabilityMeasure.toMeasure_map]
  change (target.standardLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map
      (linearImageBrownianPath A) = _
  rw [hfac, ← Measure.map_map (measurable_linearImageBrownianPath _)
    (measurable_linearImageBrownianPath _), horth O hO]

end
end LatticeProb
