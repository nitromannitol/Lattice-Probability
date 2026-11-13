/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MesoModel.Annulus38Bad at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.Annulus38

/-!
# One-scale bad-event export

Expose the corrected Lemma 3.8 failure estimate in the outer-measure form consumed by the
mesoscopic cell-model bundle.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic

/-- Corrected [18] Lemma 3.8, exported as an outer-measure failure-event interface. -/
theorem lemma38AnnulusHitBad_of_oneScaleBadBound
    (F : CellFamily.RandomCellFamily) (ρ : ℝ)
    (hinput : Annulus38OneScaleBadBound F ρ) : CellFamily.Lemma38AnnulusHitBad F ρ :=
  annulus38_lemma38AnnulusHitBad_of_oneScaleBadBound F ρ hinput

end MatedCRTHarmonic.MesoModel
