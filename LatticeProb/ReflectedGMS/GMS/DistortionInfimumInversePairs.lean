import LatticeProb.ReflectedGMS.GMS.DistortionInfimumUniversal
import LatticeProb.Topology.PolishInversePairs

/-! # Universal measurability of distortion infima -/

set_option autoImplicit false

open Set MeasureTheory
open scoped Classical Topology

namespace ReflectedGMS.GMS.ValidCodeSet

open Code CellConfig

/-- Strict sublevels of the admissible distortion infimum are universally measurable. -/
theorem universallyMeasurableSet_distortion_iInf_lt_of_goodCodes
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (r : Ω → ℝ) (x y : Ω → RawCode) (t : Ω → ENNReal)
    (hr : Measurable r) (hx : Measurable x) (hy : Measurable y) (ht : Measurable t)
    (hgx : ∀ ω, IsGoodCode (x ω)) (hgy : ∀ ω, IsGoodCode (y ω)) :
    LQGMetric.UMeasurableSet {ω |
      (⨅ (g : Plane ≃ₜ Plane)
        (_ : AdmissibleAt (decodeConfig (x ω)) (decodeConfig (y ω)) (r ω) g),
          distortion (decodeConfig (x ω)) (decodeConfig (y ω)) (r ω) g) < t ω} := by
  let : PolishSpace (LatticeProb.inversePairs (X := Plane)) :=
    LatticeProb.polishSpace_inversePairs
  let : MeasurableSpace (LatticeProb.inversePairs (X := Plane)) := borel _
  let : BorelSpace (LatticeProb.inversePairs (X := Plane)) := ⟨rfl⟩
  apply universallyMeasurableSet_distortion_iInf_lt r x y t
    LatticeProb.inversePairHomeomorph hr hx hy ht
  · exact (continuous_fst.comp continuous_subtype_val).measurable
  · exact (continuous_snd.comp continuous_subtype_val).measurable
  · intro g
    refine ⟨LatticeProb.homeomorphInversePair g, ?_⟩
    ext z
    rfl
  · exact hgx
  · exact hgy

end ReflectedGMS.GMS.ValidCodeSet
