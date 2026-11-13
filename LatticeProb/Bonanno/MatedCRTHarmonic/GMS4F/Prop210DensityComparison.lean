/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4F.Prop210DensityComparison at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop210Transfer
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Localized

/-!
# Algebraic part of the Proposition 2.10 density comparison

The geometric inputs are (4.5), the cell area/diameter ratio, and (4.7),
The multigraph degree versus localized inner and outer degree. This file
keeps those two inputs visible while proving their product comparison.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace MatedCRTHarmonic.GMS4F

open MatedCRTHarmonic.GMS3

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

theorem uCoef_eq_cellRatio_mul_degree
    (H : CellularEmbedding G o) (x : V) :
    uCoef H x =
      (ENNReal.ofReal (cellDiam H x ^ 2) / volume (H.cell x)) *
        (G.deg x : ENNReal) := by
  rw [uCoef, ENNReal.ofReal_mul (sq_nonneg _)]
  simp only [ENNReal.ofReal_natCast]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end MatedCRTHarmonic.GMS4F

