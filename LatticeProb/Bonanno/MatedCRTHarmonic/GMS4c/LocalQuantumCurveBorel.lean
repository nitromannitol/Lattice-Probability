/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalQuantumCurveBorel at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalQuantumInverse
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable

/-!
# Borel candidate for an entire quantum-time excursion

The rational-cut inverse is clamped at zero and at the total local mass.
The continuous-version operator supplies a Borel map into continuous curves;
on a correctly parametrized sample the remaining task is to identify it
with the actual clamped excursion.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.GMS4b

/-- Total mass swept out by one stored excursion after its entrance. -/
def localQuantumTotal {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (x : FiniteLocalConfiguration V) : ℝ :=
  (⨆ n : ℕ, localSegmentMass q 0 n x).toReal

theorem measurable_localQuantumTotal (V : TopologicalSpace.Opens ℂ)
    (q : ℚ × ℚ) : Measurable (localQuantumTotal (V := V) q) := by
  exact ENNReal.measurable_toReal.comp
    (Measurable.iSup fun n => measurable_localSegmentMass V q 0 n)

/-- A quantum-time evaluation clamped to the stored excursion's mass range. -/
def localQuantumEvalClamped {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (x : FiniteLocalConfiguration V) (t : ℝ) : ℂ :=
  if t ≤ 0 then finiteLocalSegment q x 0
  else if localQuantumTotal q x ≤ t then
    localQuantumEval q x (localQuantumTotal q x)
  else localQuantumEval q x t

theorem measurable_localQuantumEvalClamped
    (V : TopologicalSpace.Opens ℂ) (q : ℚ × ℚ) :
    Measurable fun p : FiniteLocalConfiguration V × ℝ =>
      localQuantumEvalClamped q p.1 p.2 := by
  unfold localQuantumEvalClamped
  refine Measurable.ite (measurableSet_le measurable_snd measurable_const) ?_ ?_
  · exact continuous_eval.measurable.comp
      (((measurable_finiteLocalSegment V q).comp measurable_fst).prodMk measurable_const)
  · refine Measurable.ite
      (measurableSet_le ((measurable_localQuantumTotal V q).comp measurable_fst)
        measurable_snd) ?_ (measurable_localQuantumEval V q)
    exact (measurable_localQuantumEval V q).comp
      (measurable_fst.prodMk
        ((measurable_localQuantumTotal V q).comp measurable_fst))

/-- Borel choice of a continuous curve from the clamped evaluations. -/
def localQuantumCurve {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (x : FiniteLocalConfiguration V) : C(ℝ, ℂ) :=
  contVersion (fun t => localQuantumEvalClamped q x t)

theorem measurable_localQuantumCurve (V : TopologicalSpace.Opens ℂ)
    (q : ℚ × ℚ) : Measurable (localQuantumCurve (V := V) q) := by
  apply measurable_contVersion.comp
  refine measurable_pi_iff.mpr fun t => ?_
  exact (measurable_localQuantumEvalClamped V q).comp
    (measurable_id.prodMk measurable_const)

end MatedCRTHarmonic.GMS4c

