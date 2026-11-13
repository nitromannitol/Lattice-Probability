/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.LogCovRadial at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.Symm
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVerPot

/-!
# Lateral and radial test functions are `logCov`-orthogonal

For test functions `φ, ψ` and their rotation averages `φ̄, ψ̄` (`symmTest`):

  `logCov(φ − φ̄, ψ̄) = 0` (`logCov_sub_symmTest_symmTest`).

Proof: `logCov(f, g) = ∫ f · u_g` with the log potential `u_g(x) = ∫ −log|x − y| g(y) dy` (LQGMetric
`MarkovGermVer.integral_mul_logPot`); `u_{ψ̄}` is smooth (`MarkovGermVer.contDiff_logPot`) and rotation invariant
(`isRotInv_logPot`: substitute `y ↦ e^{iα} y`, Lebesgue measure being rotation invariant), so `∫ φ u = ∫ φ̄ u`
(`Symm.integral_symmTest_mul`). In the language of DMS §4.1 (Lemma 4.2–4.4): the radial and lateral
subspaces of the Dirichlet space are orthogonal; here for the covariance kernel of the whole-plane GFF.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace MatedCRTHarmonic.GMCFacts

open LQGMetric

/-- The log potential of a rotation-invariant function is rotation invariant. -/
lemma isRotInv_logPot {g : ℂ → ℝ} (hg : IsRotInv g) : IsRotInv (MarkovGermVer.logPot g) := by
  intro α x
  simp only [MarkovGermVer.logPot]
  have h := integral_comp_mul_unit (norm_exp_ofReal_mul_I' α)
    (fun y => -Real.log ‖Complex.exp (α * Complex.I) * x - y‖ * g y)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [hg, ← mul_sub, norm_mul, norm_exp_ofReal_mul_I', one_mul]

/-- **Lateral ⟂ radial for `logCov`**: `logCov(φ − φ̄, ψ̄) = 0`. -/
theorem logCov_sub_symmTest_symmTest (φ ψ : TestC) :
    logCov (⇑(φ - symmTest φ)) (⇑(symmTest ψ)) = 0 := by
  set L := MarkovGermVer.logPot (⇑(symmTest ψ))
  have hcont : Continuous L := (MarkovGermVer.contDiff_logPot (symmTest ψ)).continuous
  have hrot : IsRotInv L := isRotInv_logPot (isRotInv_rotSymm ψ)
  rw [← MarkovGermVer.integral_mul_logPot]
  have hint1 : Integrable (fun x => φ x * L x) :=
    (φ.continuous.mul hcont).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hint2 : Integrable (fun x => symmTest φ x * L x) :=
    ((symmTest φ).continuous.mul hcont).integrable_of_hasCompactSupport
      (symmTest φ).hasCompactSupport.mul_right
  have e : (fun x => (φ - symmTest φ) x * L x) = fun x => φ x * L x - symmTest φ x * L x := by
    funext x
    rw [show (φ - symmTest φ) x = φ x - symmTest φ x from rfl, sub_mul]
  rw [e, integral_sub hint1 hint2, integral_symmTest_mul φ hrot hcont.locallyIntegrable, sub_self]

end MatedCRTHarmonic.GMCFacts
