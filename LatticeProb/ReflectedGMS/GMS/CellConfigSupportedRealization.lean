import LatticeProb.ReflectedGMS.GMS.CellConfigSupportBasis
import LatticeProb.ReflectedGMS.GMS.AEDecodedDistance

/-! # Measurable realizations supported on line-connected configurations -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace ReflectedGMS.GMS

/-- An almost-everywhere coded configuration has a measurable version when it is
almost surely supported on a second-countable family of line-connected configurations. -/
theorem exists_measurable_ae_eq_of_lineConnected_support
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [SFinite μ] (H : Ω → GMSSpace)
    (T : Set GMSSpace) [SecondCountableTopology T] (H₀ : T)
    (hT : ∀ᵐ ω ∂μ, H ω ∈ T)
    (hL : ∀ K ∈ T, K.1.LineConnected)
    (hcode : AEMeasurable (fun ω => (H ω).1.code) μ) :
    ∃ F : Ω → GMSSpace, Measurable F ∧ F =ᵐ[μ] H := by
  classical
  let G : Ω → T := fun ω => if h : H ω ∈ T then ⟨H ω, h⟩ else H₀
  let : MeasurableSpace T := borel T
  let : BorelSpace T := ⟨rfl⟩
  obtain ⟨B, hBcount, hB, hbasis⟩ := exists_countable_dCC_support_basis T
  have hG : NullMeasurable G μ := by
    change @Measurable (NullMeasurableSpace Ω μ) T _ _ G
    apply (measurable_generateFrom ?_).mono le_rfl hbasis.borel_eq_generateFrom.le
    intro U hU
    obtain ⟨K, ε, hε, rfl⟩ := hB U hU
    have hg : ∀ᵐ ω ∂μ, ValidCodeSet.IsGoodCode ((H ω).1.code) := by
      filter_upwards [hT] with ω hω
      exact ValidCodeSet.isGoodCode_code (H ω).2 (hL (H ω) hω)
    have hK : ValidCodeSet.IsGoodCode K.1.1.code :=
      ValidCodeSet.isGoodCode_code K.1.2 (hL K.1 K.2)
    have hd := ValidCodeSet.aemeasurable_dCC_decodeConfig_of_ae μ
      (fun _ => K.1.1.code) (fun ω => (H ω).1.code) K.1.1.code hK
      measurable_const.aemeasurable hcode (Filter.Eventually.of_forall fun _ => hK) hg
    have hd' : AEMeasurable (fun ω => CellConfig.dCC K.1.1 (H ω).1) μ := by
      apply hd.congr
      filter_upwards [hT] with ω hω
      rw [ValidCodeSet.decodeConfig_code_eq K.1.1 K.1.2 (hL K.1 K.2),
        ValidCodeSet.decodeConfig_code_eq (H ω).1 (H ω).2 (hL (H ω) hω)]
    have hm := hd'.nullMeasurable (measurableSet_Iio : MeasurableSet (Iio ε))
    apply hm.congr
    filter_upwards [hT] with ω hω
    change (CellConfig.dCC K.1.1 (H ω).1 < ε) =
      (CellConfig.dCC K.1.1 (G ω).1.1 < ε)
    simp [G, hω]
  have hGae := hG.aemeasurable
  refine ⟨fun ω => (hGae.mk G ω).1, ?_, ?_⟩
  · exact continuous_subtype_val.measurable.comp hGae.measurable_mk
  · filter_upwards [hGae.ae_eq_mk, hT] with ω heq hω
    simpa [G, hω] using congrArg Subtype.val heq.symm

end ReflectedGMS.GMS
