/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MesoModel.RecAdmissible at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop210
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma34
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Consumers

/-!
# Deterministic test-pair admissibility for the recurrence adapter

The tests are the three functions in GMS3's Theorem 1.4 input. The inequalities below expose the
numerical margins needed by GMS4's Proposition 2.10 admissibility predicate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic.GMS3

/-- The constant and boundary-layer growth inequalities follow from the selected exponent. -/
theorem recMeshOneAndLayer {β' betaG4 C : ℝ}
    (hC : 1 ≤ C) (hbeta : 0 ≤ betaG4) (hβ' : β' ≤ betaG4) :
    (∀ k : ℕ, 1 ≤ k → 1 ≤ C * CellFamily.mesh k ^ (-betaG4)) ∧
    (∀ k : ℕ, 1 ≤ k →
      (CellFamily.mesh k ^ β')⁻¹ ≤ C * CellFamily.mesh k ^ (-betaG4)) := by
  constructor
  · intro k hk
    have hε := GMSLemma27.mesh_pos k
    have hε1 := (GMSLemma27.mesh_lt_one (by omega : k ≠ 0)).le
    have hpow : 1 ≤ CellFamily.mesh k ^ (-betaG4) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (neg_nonpos.mpr hbeta)
    calc
      (1 : ℝ) ≤ CellFamily.mesh k ^ (-betaG4) := hpow
      _ = 1 * CellFamily.mesh k ^ (-betaG4) := by ring
      _ ≤ C * CellFamily.mesh k ^ (-betaG4) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hε.le _)

  · intro k hk
    have hε := GMSLemma27.mesh_pos k
    have hε1 := (GMSLemma27.mesh_lt_one (by omega : k ≠ 0)).le
    calc
      (CellFamily.mesh k ^ β')⁻¹ = CellFamily.mesh k ^ (-β') :=
        (Real.rpow_neg hε.le β').symm
      _ ≤ CellFamily.mesh k ^ (-betaG4) :=
        Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
      _ = 1 * CellFamily.mesh k ^ (-betaG4) := by ring
      _ ≤ C * CellFamily.mesh k ^ (-betaG4) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hε.le _)

end MatedCRTHarmonic.MesoModel
