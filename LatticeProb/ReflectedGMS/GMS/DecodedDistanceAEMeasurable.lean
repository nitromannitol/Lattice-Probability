import LatticeProb.ReflectedGMS.GMS.DistortionInfimumInversePairs

/-! # Almost-everywhere measurability of decoded configuration distances -/

set_option autoImplicit false

open Set MeasureTheory
open scoped Classical Topology ENNReal

namespace ReflectedGMS.GMS.ValidCodeSet

open Code CellConfig

/-- The distance between two measurable families of good codes has a measurable version. -/
theorem aemeasurable_dCC_decodeConfig
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [SFinite μ] (x y : Ω → RawCode)
    (hx : Measurable x) (hy : Measurable y)
    (hgx : ∀ ω, IsGoodCode (x ω)) (hgy : ∀ ω, IsGoodCode (y ω)) :
    AEMeasurable (fun ω => dCC (decodeConfig (x ω)) (decodeConfig (y ω))) μ := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let D : Ω × ℝ → ℝ≥0∞ := fun p =>
    ⨅ (g : Plane ≃ₜ Plane)
      (_ : AdmissibleAt (decodeConfig (x p.1)) (decodeConfig (y p.1)) p.2 g),
        distortion (decodeConfig (x p.1)) (decodeConfig (y p.1)) p.2 g
  have hD : NullMeasurable D (μ.prod ν) := by
    change @Measurable (NullMeasurableSpace (Ω × ℝ) (μ.prod ν)) ℝ≥0∞ _ _ D
    apply measurable_of_Iio
    intro t
    exact (universallyMeasurableSet_distortion_iInf_lt_of_goodCodes
      Prod.snd (x ∘ Prod.fst) (y ∘ Prod.fst) (fun _ => t)
      measurable_snd (hx.comp measurable_fst) (hy.comp measurable_fst) measurable_const
      (fun p => hgx p.1) (fun p => hgy p.1)).nullMeasurableSet (μ.prod ν)
  have hweight : Measurable (fun p : Ω × ℝ => ENNReal.ofReal (Real.exp (-p.2))) := by
    fun_prop
  have h := (hweight.aemeasurable.min hD.aemeasurable).lintegral_prod_right'
  simpa only [dCC, D, ν] using h

end ReflectedGMS.GMS.ValidCodeSet
