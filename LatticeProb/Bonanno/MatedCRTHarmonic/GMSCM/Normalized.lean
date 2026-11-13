/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.Normalized at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.WholePlane
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Local Cameron–Martin comparison for a normalized whole-plane GFF

A deterministic test-function shift preserving the unit-circle normalization has
an L² density on every restricted-field space. This is the fixed-shift component
of [18] (4.16); the quantum-cone normalization change is separate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory LQGMetric LQGMetric.GM
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCM

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- The reverse fixed-shift comparison, with the unshifted normalized GFF
measured against the shifted field law. -/
theorem normalized_shift_restriction_comparison_reverse (hh : IsNormalizedWPGFF h P)
    (φ : TestC) (hφ : Real.circleAverage (testCont φ) 0 1 = 0)
    (V : TopologicalSpace.Opens ℂ) :
    ∃ M : DistOn V → ℝ≥0∞, Measurable M ∧
      P.map (fun ω => restrictTo V (h ω)) =
        (P.map fun ω => restrictTo V (addFun (h ω) (testCont φ))).withDensity M ∧
      ∫⁻ x, M x ^ (2 : ℝ) ∂
        (P.map fun ω => restrictTo V (addFun (h ω) (testCont φ))) < ⊤ := by
  obtain ⟨F, hF, hfix⟩ :=
    exists_sigma0_fix (measurable_circleAvg_left 1 0)
  have hFs : Measurable[MeasurableSpace.comap pair0 MeasurableSpace.pi] F := hF
  obtain ⟨G, hG, hFG⟩ := hFs.exists_eq_measurable_comp
  have hfh : ∀ᵐ ω ∂P, F (h ω) = h ω := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh.1, hh.2] with ω h1 h2
    exact hfix _ h1 h2
  have hfh' : ∀ᵐ ω ∂P,
      F (addFun (h ω) (testCont φ)) = addFun (h ω) (testCont φ) := by
    filter_upwards [ae_circleAvg_addFun hh.1 (testCont φ), hh.2] with ω h1 h2
    have h0' := h1 0
    rw [addConst_zero_eq, h2, hφ] at h0'
    refine hfix _ (fun c => ?_) (by rw [h0']; ring)
    rw [h1 c, h2, hφ, h0']; ring
  let observe : (TestC0 → ℝ) → DistOn V := restrictTo V ∘ G
  have hobserve : Measurable observe :=
    (measurable_restrictTo V).comp hG
  obtain ⟨M, hMm, hLaw, hM2⟩ :=
    cm_observation_comparison_reverse hh.1 φ observe hobserve
  have hbase : (lawPair0 h P).map observe =
      P.map (fun ω => restrictTo V (h ω)) := by
    rw [lawPair0, Measure.map_map hobserve (measurable_pair0_comp hh.1)]
    exact Measure.map_congr (hfh.mono fun ω hω => by
      change restrictTo V (G (pair0 (h ω))) = restrictTo V (h ω)
      simpa only [hFG, Function.comp_apply] using congrArg (restrictTo V) hω)
  have hshift :
      (lawPair0 (fun ω => addFun (h ω) (testCont φ)) P).map observe =
      P.map (fun ω => restrictTo V (addFun (h ω) (testCont φ))) := by
    rw [lawPair0, Measure.map_map hobserve (measurable_pair0_addFun hh.1 φ)]
    exact Measure.map_congr (hfh'.mono fun ω hω => by
      change restrictTo V (G (pair0 (addFun (h ω) (testCont φ)))) = _
      simpa only [hFG, Function.comp_apply] using congrArg (restrictTo V) hω)
  refine ⟨M, hMm, ?_, ?_⟩
  · rw [← hbase, ← hshift]
    exact hLaw
  · rw [← hshift]
    exact hM2

end MatedCRTHarmonic.GMSCM
