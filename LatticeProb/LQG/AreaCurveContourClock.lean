import LatticeProb.LQG.DirectRelTimeChange
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-! # Contour identifications for coupled area parametrizations -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- Almost surely the two area-parametrized curves have a common increasing
clock, and the contour identifications transfer along that clock. -/
theorem ae_zeroCone_curve_contour_clock
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (hC : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
      (∀ t, η₀ ω t = η ω (ψ t)) ∧
      (∀ s t, (DirectRel (fun u => lrCoord 0 (ψ u) (bm ω)) s t ∨
        DirectRel (fun u => lrCoord 1 (ψ u) (bm ω)) s t) → η₀ ω s = η₀ ω t) ∧
      (∀ s t, η₀ ω s = η₀ ω t →
        Relation.EqvGen (fun a b => DirectRel (fun u => lrCoord 0 (ψ u) (bm ω)) a b ∨
          DirectRel (fun u => lrCoord 1 (ψ u) (bm ω)) a b) s t) := by
  filter_upwards [hC.areaParam, hC.areaParam₀, hC.merge, hC.onlyMerge] with ω hγ hzero hm ho
  obtain ⟨⟨φ, hφ0, hφ⟩, _⟩ := hγ
  obtain ⟨⟨φ₀, hφ₀0, hφ₀⟩, _⟩ := hzero
  let ψ := φ₀.trans φ.symm
  have hψ0 : ψ 0 = 0 := by
    change φ.symm (φ₀ 0) = 0
    simpa only [hφ₀0, hφ0] using φ.symm_apply_apply 0
  have hcurve : ∀ t, η₀ ω t = η ω (ψ t) := by
    intro t
    rw [hφ₀ t, hφ (ψ t)]
    change ηL ω (φ₀ t) = ηL ω (φ (φ.symm (φ₀ t)))
    rw [φ.apply_symm_apply]
  refine ⟨ψ, hψ0, hcurve, ?_, ?_⟩
  · intro s t hst
    rw [hcurve s, hcurve t]
    exact merge_comp_orderIso (fun u => lrCoord 0 u (bm ω))
      (fun u => lrCoord 1 u (bm ω)) (η ω) ψ hm s t hst
  · intro s t hst
    apply onlyMerge_comp_orderIso (fun u => lrCoord 0 u (bm ω))
      (fun u => lrCoord 1 u (bm ω)) (η ω) ψ ho s t
    simpa only [← hcurve s, ← hcurve t] using hst

end LatticeProb
