/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cS.WholePlaneFunctional at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.Data
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOArea
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4D
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOClock
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OBase

/-!
# Whole-plane field's area-time evaluation for [18] Lemma 4.9

The frozen curve `η₀` uses the zero-cone clock. Here the normalized
whole-plane field and the independent Lebesgue-time curve are passed through
The existing Borel inverse-clock functional. This supplies the exact random
function needed for the whole-plane version of the point observable. A proof
that this function has a continuous curve version is still required before
the `C(ℝ, ℂ)`-valued local geometry API can be applied.
-/

set_option autoImplicit false
-- The canonical field and coupling carry large reducible interfaces.
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4cS

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTPort

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The normalized whole-plane field remains independent of the full
imaginary-geometry data, including the random additive phase. -/
theorem indepFun_normalizedWholePlane_IGdata
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun (fun ω => Canon.normalizeWholePlane (X₀ ω))
      (fun ω => (hIG₀ ω, U ω)) P := by
  let pick : MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) ×
      MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → MatedCRT.Field :=
    fun q => q.2.2.2.1
  have hp : Measurable pick :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd))
  have hn : Measurable Canon.normalizeWholePlane := by
    apply LQGMetric.DFGPS.L219.measurable_addConst_of
    · exact measurable_id
    · exact (LQGMetric.measurable_circleAvg_left 1 0).neg
  simpa only [Function.comp_def, id_eq, pick, Canon.normalizeWholePlane] using
    (D.indep_curve.symm.comp (hn.comp hp) measurable_id)

end MatedCRTHarmonic.GMS4cS

