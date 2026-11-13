/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.BundleAdapter at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Theorem44
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# Adapter: [18]'s localized quantities at `ε = 1`, `z = 0` are the bundle's `[20]` quantities

The bundle (`MatedCRT.MatingOfTreesInput`) states [20] Propositions 4.4 and 4.6 in its field `cellMoments` with `MatedCRT.diamAreaSup`,
`MatedCRT.degInner`, `MatedCRT.degOuter` ([20] (4.12), Definition 4.5). On curves with
`η(0) = 0` they coincide with `locDA 1 · 0`, `locDegIn 1 · 0`, `locDegOut 1 · 0` (as in [20]: "the `DA(H₀)`, `B_0` and
`deg_in`/`deg_out` definitions are exactly [18]'s localised quantities at `ε = 1`, `z = 0`"), so the bundle field
produces `UnitCellMoments` (`unitCellMoments_of_cellMoments`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

theorem locWindow_one_zero (c : ℝ → ℂ) : locWindow 1 c 0 = c '' Icc (-1) 1 := by
  rw [locWindow]; norm_num

theorem locDA_one_zero_eq_diamAreaSup (c : C(ℝ, ℂ)) : locDA 1 c 0 = MatedCRT.diamAreaSup c := by
  simp only [locDA, segRatio, MatedCRT.diamAreaSup, zero_add]

theorem locBall_one_zero_eq_degBall (c : C(ℝ, ℂ)) (h0 : c 0 = 0) :
    locBall 1 c 0 = MatedCRT.degBall c := by
  rw [locBall, locWindow_one_zero, h0, MatedCRT.degBall]

theorem locDegIn_one_zero_eq_degInner (c : C(ℝ, ℂ)) (h0 : c 0 = 0) :
    locDegIn 1 c 0 = MatedCRT.degInner c := by
  simp only [locDegIn, IsDegInFamily, MatedCRT.degInner, locBall_one_zero_eq_degBall c h0,
    locWindow_one_zero]

theorem locDegOut_one_zero_eq_degOuter (c : C(ℝ, ℂ)) (h0 : c 0 = 0) :
    locDegOut 1 c 0 = MatedCRT.degOuter c := by
  simp only [locDegOut, IsDegOutFamily, MatedCRT.degOuter, locBall_one_zero_eq_degBall c h0,
    locWindow_one_zero]

/-- **The bundle field `cellMoments` gives `UnitCellMoments`** (for a curve with `η(0) = 0` a.s., as given by the
bundle fields `spaceFilling` and `areaParam₀`). -/
theorem unitCellMoments_of_cellMoments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {η : Ω → C(ℝ, ℂ)} (h0 : ∀ᵐ ω ∂P, η ω 0 = 0)
    (hcell : (∀ p : ℝ, 1 ≤ p → ∫⁻ ω, MatedCRT.diamAreaSup (η ω) ^ p ∂P < ⊤) ∧
      (∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∫⁻ ω, ((MatedCRT.degInner (η ω) : ℝ≥0∞)) ^ p ∂P < ⊤) ∧
      (∀ p : ℝ, 1 ≤ p → ∫⁻ ω, ((MatedCRT.degOuter (η ω) : ℝ≥0∞)) ^ p ∂P < ⊤)) :
    UnitCellMoments γ P η := by
  refine ⟨fun p hp => ?_, fun p hp hp' => ?_, fun p hp => ?_⟩
  · simpa only [locDA_one_zero_eq_diamAreaSup] using hcell.1 p hp
  · refine lt_of_eq_of_lt (lintegral_congr_ae ?_) (hcell.2.1 p hp hp')
    filter_upwards [h0] with ω hω
    rw [locDegIn_one_zero_eq_degInner (η ω) hω]
  · refine lt_of_eq_of_lt (lintegral_congr_ae ?_) (hcell.2.2 p hp)
    filter_upwards [h0] with ω hω
    rw [locDegOut_one_zero_eq_degOuter (η ω) hω]

end MatedCRTHarmonic.GMS4b
