/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46TZeroVersion at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TTransfer
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TModel
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TZeroInputs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.AreaRecord
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48

/-!
# Measurable-version comparison for the raw zero-cone cell model

The local comparison compares measurable field representatives. Their almost-sure identities
transport the joint density and local event reconstruction to the raw coupling
without changing its inner-degree or Proposition 4.5 event.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.MatedCRT

/-- One global measurable representative of the frozen zero-cone field. -/
def l46tZeroConeFieldVersion
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm) :
    Ω → LQGMetric.DistC :=
  (GMS4.aemeasurable_prop48ZeroConeField D).mk
    (fun ω => coneField (X₀ ω)
      (coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω)))

theorem l46tZeroConeFieldVersion_measurable
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm) :
    Measurable (l46tZeroConeFieldVersion D) :=
  (GMS4.aemeasurable_prop48ZeroConeField D).measurable_mk

theorem l46tZeroConeFieldVersion_ae_eq_raw
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    (l46tZeroConeCellModel D hγ).field =ᵐ[P] l46tZeroConeFieldVersion D := by
  simpa only [l46tZeroConeCellModel, l46tZeroConeFieldVersion] using
    (GMS4.aemeasurable_prop48ZeroConeField D).ae_eq_mk

end MatedCRTHarmonic.GMS4b
