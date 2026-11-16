import LatticeProb.ReflectedGMS.GMS.DecodedDistanceAEMeasurable
import LatticeProb.Prob.CellConfigCodeInjective

/-! # Distances of almost-everywhere valid coded configurations -/

set_option autoImplicit false

open Set MeasureTheory
open scoped Classical

namespace ReflectedGMS.GMS.ValidCodeSet

open Code CellConfig

/-- Two almost-everywhere good codes have an almost-everywhere measurable distance. -/
theorem aemeasurable_dCC_decodeConfig_of_ae
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [SFinite μ] (x y : Ω → RawCode) (r₀ : RawCode)
    (h₀ : IsGoodCode r₀) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hgx : ∀ᵐ ω ∂μ, IsGoodCode (x ω)) (hgy : ∀ᵐ ω ∂μ, IsGoodCode (y ω)) :
    AEMeasurable (fun ω => dCC (decodeConfig (x ω)) (decodeConfig (y ω))) μ := by
  let X : Ω → RawCode := fun ω =>
    if IsGoodCode (hx.mk x ω) then hx.mk x ω else r₀
  let Y : Ω → RawCode := fun ω =>
    if IsGoodCode (hy.mk y ω) then hy.mk y ω else r₀
  have hX : Measurable X :=
    Measurable.ite (measurableSet_goodCodes.preimage hx.measurable_mk) hx.measurable_mk measurable_const
  have hY : Measurable Y :=
    Measurable.ite (measurableSet_goodCodes.preimage hy.measurable_mk) hy.measurable_mk measurable_const
  have hgX : ∀ ω, IsGoodCode (X ω) := by
    intro ω
    dsimp only [X]
    split <;> assumption
  have hgY : ∀ ω, IsGoodCode (Y ω) := by
    intro ω
    dsimp only [Y]
    split <;> assumption
  have hdist := aemeasurable_dCC_decodeConfig μ X Y hX hY hgX hgY
  apply hdist.congr
  filter_upwards [hx.ae_eq_mk, hy.ae_eq_mk, hgx, hgy] with ω ex ey gx gy
  simp only [X, Y, ← ex, ← ey, gx, gy, ↓reduceIte]

/-- A valid line-connected configuration is recovered from its canonical code. -/
theorem decodeConfig_code_eq (H : CellConfig) (hH : H.IsCellConfiguration)
    (hL : H.LineConnected) : decodeConfig H.code = H := by
  have hg := isGoodCode_code hH hL
  exact CellConfig.eq_of_code_eq hg.isCellConfiguration hH hg.decodeConfig_code

/-- The distance to a fixed line-connected configuration has a measurable version. -/
theorem aemeasurable_dCC_of_ae_code
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [SFinite μ] (H : Ω → CellConfig) (H₀ : CellConfig)
    (h₀ : H₀.IsCellConfiguration) (hL₀ : H₀.LineConnected)
    (hcode : AEMeasurable (fun ω => (H ω).code) μ)
    (hvalid : ∀ᵐ ω ∂μ, (H ω).IsCellConfiguration ∧ (H ω).LineConnected) :
    AEMeasurable (fun ω => dCC (H ω) H₀) μ := by
  have hgood : ∀ᵐ ω ∂μ, IsGoodCode ((H ω).code) := by
    filter_upwards [hvalid] with ω h
    exact isGoodCode_code h.1 h.2
  have hd := aemeasurable_dCC_decodeConfig_of_ae μ (fun ω => (H ω).code)
    (fun _ => H₀.code) H₀.code (isGoodCode_code h₀ hL₀) hcode
    measurable_const.aemeasurable hgood (Filter.Eventually.of_forall fun _ => isGoodCode_code h₀ hL₀)
  apply hd.congr
  filter_upwards [hvalid] with ω h
  rw [decodeConfig_code_eq (H ω) h.1 h.2, decodeConfig_code_eq H₀ h₀ hL₀]

end ReflectedGMS.GMS.ValidCodeSet
