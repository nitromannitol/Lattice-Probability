/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48ThickLocal at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaLimit
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCore

/-!
# Thickened local-field reconstruction for Proposition 4.8

The selected area on `V` is read from a field on `thickening δ V`, matching
The dyadic GMC locality interface. The frozen S7 clause then reconstructs
The remaining local configuration from the independent IG data.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal

namespace MatedCRTHarmonic.GMS4

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.MoTPort.IG.GFFAbsCont

/-- The one remaining reconstruction input in its thickened-field shape: a Borel map from
The field on `thickening δ V` to the canonical GMC area restricted to `V`. -/
structure Prop48ThickLocalGMCFromFieldInput
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (h : Ω → MatedCRT.Field)
    (V : TopologicalSpace.Opens ℂ) (δ : ℝ) where
  reconstruct : LQGMetric.DistOn (GMS4c.thickOpen V δ) → Measure ℂ
  measurable_reconstruct : Measurable reconstruct
  ae_reconstruct : (fun ω => reconstruct
    (LQGMetric.restrictTo (GMS4c.thickOpen V δ) (h ω))) =ᵐ[P]
      fun ω => (MatedCRTHarmonic.CellScaling.lqgArea γ (h ω)).restrict V

end MatedCRTHarmonic.GMS4

