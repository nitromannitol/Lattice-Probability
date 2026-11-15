import LatticeProb.Bonanno.ReflectedGMS.GMS.ValidCodeSet
import LatticeProb.Prob.CellConfigCodeInjective

/-! # Codes of line-connected cell configurations -/

set_option autoImplicit false

open Set

namespace ReflectedGMS.GMS

/-- The configuration canonically decoded from a good code. -/
noncomputable def goodCodeConfig (r : goodCodes) : GMSSpace :=
  ⟨ValidCodeSet.decodeConfig r.1, r.2.isCellConfiguration⟩

/-- Decoding a good code yields a line-connected configuration. -/
theorem goodCodeConfig_lineConnected (r : goodCodes) :
    (goodCodeConfig r).1.LineConnected :=
  r.2.lineConnected_decodeConfig

/-- Encoding the configuration decoded from a good code recovers the code. -/
theorem codeMap_goodCodeConfig (r : goodCodes) : codeMap (goodCodeConfig r) = r.1 :=
  r.2.decodeConfig_code

/-- Good codes are exactly the codes of line-connected configurations. -/
theorem codeMap_mem_goodCodes_iff (H : GMSSpace) :
    codeMap H ∈ goodCodes ↔ H.1.LineConnected := by
  constructor
  · intro h
    have heq : goodCodeConfig ⟨codeMap H, h⟩ = H :=
      codeMap_injective (codeMap_goodCodeConfig ⟨codeMap H, h⟩)
    rw [← heq]
    exact goodCodeConfig_lineConnected ⟨codeMap H, h⟩
  · exact code_mem_goodCodes H.2

/-- Good codes are the image of all line-connected configurations. -/
theorem range_lineConnected_codeMap :
    Set.range (fun H : {H : GMSSpace // H.1.LineConnected} => codeMap H.1) = goodCodes := by
  ext r
  constructor
  · rintro ⟨H, rfl⟩
    exact code_mem_goodCodes H.1.2 H.2
  · intro hr
    exact ⟨⟨goodCodeConfig ⟨r, hr⟩, goodCodeConfig_lineConnected ⟨r, hr⟩⟩,
      codeMap_goodCodeConfig ⟨r, hr⟩⟩

/-- Encoding and decoding are inverse bijections on line-connected configurations. -/
noncomputable def lineConnectedCodeEquiv :
    {H : GMSSpace // H.1.LineConnected} ≃ goodCodes where
  toFun H := ⟨codeMap H.1, code_mem_goodCodes H.1.2 H.2⟩
  invFun r := ⟨goodCodeConfig r, goodCodeConfig_lineConnected r⟩
  left_inv H := by
    apply Subtype.ext
    exact codeMap_injective (codeMap_goodCodeConfig _)
  right_inv r := Subtype.ext (codeMap_goodCodeConfig r)

end ReflectedGMS.GMS
