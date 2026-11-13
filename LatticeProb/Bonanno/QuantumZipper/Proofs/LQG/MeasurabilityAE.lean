/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.MeasurabilityAE at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryVague
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS

/-!
# AE-MEAS: almost-sure measurability of the LQG measures as random measures

If `X : Ω → FieldSample` has measurable coordinates and, almost surely, the approximations of
`X ω` converge vaguely to `qBoundaryMeasure γ (X ω)` (resp. to `qAreaMeasure γ (X ω)` on `ℍ`),
then `ω ↦ qBoundaryMeasure γ (X ω)` (resp. `qAreaMeasure`) is `AEMeasurable` into the Giry
`σ`-algebra. The measurable modification is the measure on a measurable full-measure subset of
the good event, and `0` elsewhere.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace LQGMeasAE

open LQGMeas

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- A measurable full-measure subset of an almost-sure event. -/
theorem exists_measurableSet_subset_ae {p : Ω → Prop} (hp : ∀ᵐ ω ∂P, p ω) :
    ∃ S : Set Ω, MeasurableSet S ∧ (∀ ω ∈ S, p ω) ∧ P Sᶜ = 0 := by
  refine ⟨(toMeasurable P {ω | ¬ p ω})ᶜ, (measurableSet_toMeasurable _ _).compl,
    fun ω hω => ?_, ?_⟩
  · by_contra h
    exact hω (subset_toMeasurable _ _ h)
  · rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 hp

/-! ## Boundary -/

/-! ## Area -/

/-! ## Free-field corollaries -/

end LQGMeasAE

end QuantumZipper
