/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase1.Representations at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase1.Case2Local
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop210
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410Rooting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.SmallRootMass
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Consumers
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.ProductRooting
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOClock

/-!
# Source representations of the Case 1/2 fields and the area-time curve

Source: [18, Proposition 4.10, Cases 1–2].

* `ae_rootedWPField_eq`: on the marked carrier, almost surely
  `h₁ = h₀ − γ log|·−z| + γ log max(|·|,1)` exactly as printed (the unit-circle renormalization in
  CANON's `rootedField` is a.s. trivial for `z ∈ 𝔻`; the rooting construction's `ProductRooting`).
* `ae_case2Field_eq`: almost surely `h₂ = h₀ − γ log|·−z|` ([18]), the representation used
  by the Case 3/4 laws (`GMSCase/*`).
* `rootedWPData_areaCurve_law`: the Case 1 joint law extended by the area-parametrized curve of
  the field, the area-scaling construction's measurable `JointScalingO.parMap γ (h, ηL)` (`= ηL` reparametrized by `μ_h`
  whenever such a parametrization exists, `JointScalingO.parEval_eq`): the whole-plane cell model
  `ηWP` is carried along by the rooting.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase1

open LQGMetric MatedCRTHarmonic.MatedCRT

/-- DMS's rooting shift minus `γ log max(|·|, 1)` is the source's `−γ log|· − z|`. -/
theorem logRootingShift_sub_logMax (γ : ℝ) (z : ℂ) :
    ConeLemmaA10.logRootingShift γ z - CellScaling.ofFunC (fun w => γ * Real.log (max ‖w‖ 1)) =
      CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z‖) := by
  have h₁ : LocallyIntegrableOn (fun w : ℂ => -γ * Real.log ‖w - z‖)
      ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) volume := by
    have h := ((ConeLemmaA10.locallyIntegrable_log_norm_sub z).smul (-γ)).congr
      (ae_of_all _ fun w => by simp : ∀ᵐ w ∂volume,
        ((-γ) • fun w : ℂ => Real.log ‖w - z‖) w = -γ * Real.log ‖w - z‖)
    simpa [locallyIntegrableOn_univ] using h
  have h₂ : LocallyIntegrableOn (fun w : ℂ => γ * Real.log (max ‖w‖ 1))
      ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) volume := by
    have h := (ConeLemmaA10.continuous_log_max_norm_one.locallyIntegrable (μ := volume)).smul γ
    have h' : LocallyIntegrable (fun w : ℂ => γ * Real.log (max ‖w‖ 1)) volume :=
      h.congr (ae_of_all _ fun w => by simp)
    simpa [locallyIntegrableOn_univ] using h'
  have e : ConeLemmaA10.logRootingShift γ z =
      CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z‖) +
        CellScaling.ofFunC (fun w => γ * Real.log (max ‖w‖ 1)) := by
    rw [ConeLemmaA10.logRootingShift, CellScaling.ofFunC, CellScaling.ofFunC,
      ← Distribution.ofFun_add h₁ h₂]
    rfl
  rw [e, add_sub_cancel_right]

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

theorem ae_rootMeasure_mem_ball : ∀ᵐ z ∂Canon.rootMeasure, z ∈ ball (0 : ℂ) 1 := by
  change ∀ᵐ z ∂(ENNReal.ofReal (Real.pi⁻¹) •
    (volume.restrict GMS4.GMSA.rootingDisk)), z ∈ ball (0 : ℂ) 1
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_ball) _

/-- **The Case 1 field as printed.** Almost surely on the marked carrier,
`h₁ = h₀ + (−γ log|·−z| + γ log max(|·|,1))`. -/
theorem ae_rootedWPField_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ v ∂Canon.rootedLaw P,
      rootedWPField γ X₀ v = wpField X₀ v.1 + ConeLemmaA10.logRootingShift γ v.2 := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact ConeLemmaA10.ae_normalizedRootingMap_eq_add_logRootingShift_prod
    (isNormalizedWPGFF_wpField D) γ ae_rootMeasure_mem_ball

/-- **The Case 2 field as printed** ([18] ): almost surely `h₂ = h₀ − γ log|·−z|`. -/
theorem ae_case2Field_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ v ∂Canon.rootedLaw P,
      Canon.case2Field γ (wpField X₀ v.1) v.2 =
        wpField X₀ v.1 + CellScaling.ofFunC (fun w => -γ * Real.log ‖w - v.2‖) := by
  filter_upwards [ae_rootedWPField_eq D] with v hv
  change rootedWPField γ X₀ v - _ = _
  rw [hv, add_sub_assoc, logRootingShift_sub_logMax]

/-! ## The area-time curve -/

end Coupling

end MatedCRTHarmonic.GMSCase1
