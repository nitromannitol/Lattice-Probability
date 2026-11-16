import LatticeProb.ReflectedGMS.GMS.AdmissibleDistortionMeasurable
import LatticeProb.Bonanno.LQGMetric.Meas.UM

/-! # Universal measurability of admissible distortion infima -/

set_option autoImplicit false

open Set MeasureTheory
open scoped Classical

namespace ReflectedGMS.GMS.ValidCodeSet

open Code CellConfig

/-- Strict sublevels of the infimum over admissible homeomorphisms are universally
measurable when the homeomorphisms have a surjective standard Borel parametrization. -/
theorem universallyMeasurableSet_distortion_iInf_lt
    {Ω W : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace W] [StandardBorelSpace W]
    (r : Ω → ℝ) (x y : Ω → RawCode) (t : Ω → ENNReal)
    (f : W → Plane ≃ₜ Plane)
    (hr : Measurable r) (hx : Measurable x) (hy : Measurable y) (ht : Measurable t)
    (hf : Measurable fun w => (⟨f w, (f w).continuous⟩ : C(Plane, Plane)))
    (hfi : Measurable fun w => (⟨(f w).symm, (f w).symm.continuous⟩ : C(Plane, Plane)))
    (hsurj : Function.Surjective f)
    (hgx : ∀ ω, IsGoodCode (x ω)) (hgy : ∀ ω, IsGoodCode (y ω)) :
    LQGMetric.UMeasurableSet {ω |
      (⨅ (g : Plane ≃ₜ Plane)
        (_ : AdmissibleAt (decodeConfig (x ω)) (decodeConfig (y ω)) (r ω) g),
          distortion (decodeConfig (x ω)) (decodeConfig (y ω)) (r ω) g) < t ω} := by
  classical
  let A : Set (Ω × W) := {p |
    AdmissibleAt (decodeConfig (x p.1)) (decodeConfig (y p.1)) (r p.1) (f p.2)}
  have hA : MeasurableSet A :=
    measurableSet_admissibleAt_decodeConfig_variable_radius
      (r ∘ Prod.fst) (x ∘ Prod.fst) (y ∘ Prod.fst) (f ∘ Prod.snd)
      (hx.comp measurable_fst) (hy.comp measurable_fst) (hr.comp measurable_fst)
      (fun p => hgx p.1) (fun p => hgy p.1)
      (hf.comp measurable_snd) (hfi.comp measurable_snd)
  have hd := measurable_admissible_decoded_distortion
      (r ∘ Prod.fst) (x ∘ Prod.fst) (y ∘ Prod.fst) (f ∘ Prod.snd)
      (hr.comp measurable_fst) (hx.comp measurable_fst) (hy.comp measurable_fst)
      (hf.comp measurable_snd) (hfi.comp measurable_snd)
      (fun p => hgx p.1) (fun p => hgy p.1)
  let B : Set (Ω × W) := A ∩ {p |
    (if p ∈ A then distortion (decodeConfig (x p.1)) (decodeConfig (y p.1))
      (r p.1) (f p.2) else 0) < t p.1}
  have hB : MeasurableSet B := hA.inter (measurableSet_lt hd (ht.comp measurable_fst))
  have hp := LQGMetric.UMeasurableSet.setOf_exists hB
  convert hp using 1
  ext ω
  simp only [mem_ofPred_eq, iInf_lt_iff, B, mem_inter_iff, A]
  constructor
  · rintro ⟨g, hg, hlt⟩
    obtain ⟨w, rfl⟩ := hsurj g
    exact ⟨w, hg, by simpa [hg] using hlt⟩
  · rintro ⟨w, hw, hlt⟩
    exact ⟨f w, hw, by simpa [hw] using hlt⟩

end ReflectedGMS.GMS.ValidCodeSet
