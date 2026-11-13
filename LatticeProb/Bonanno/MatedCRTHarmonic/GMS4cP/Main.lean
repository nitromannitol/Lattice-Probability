/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.Main at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.IGHalf

/-!
# summary theorems

Source: [18] Lemmas 4.3, 4.6 and (4.16) (`1968–2019`,
`2070–2116`).

* `l43pZeroConeConfigInput_of_area`: the configuration form of measurable [18] Lemma 4.3 on the transfer's disks follows
  from its **area half** alone; the IG half is `l43pZeroConeIGInput_holds` (proved from the bundle).
* `l43p_zeroCone_innerDegreeBoundPolylog_of_area`: the polylogarithmic [18] Lemma 4.6 on the frozen zero-cone
  model from the transfer's (4.16) comparison and the area half.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : NNReal → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Measurable [18] Lemma 4.3 (configuration form) from its area half.** -/
theorem l43pZeroConeConfigInput_of_area
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ : ℝ} (hρ : ρ < 1) (w : ℂ)
    (hA : L43PZeroConeAreaInput D hγ ρ w) : L43PZeroConeConfigInput D hγ ρ w :=
  l43pZeroConeConfigInput_of_parts D hγ hρ w hA (l43pZeroConeIGInput_holds D hρ w)

end MatedCRTHarmonic.GMS4cP
