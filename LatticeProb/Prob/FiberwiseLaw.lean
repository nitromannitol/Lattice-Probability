import Mathlib.MeasureTheory.Measure.Prod

/-! # Integration of parameter-dependent laws -/

set_option autoImplicit false

namespace LatticeProb

open MeasureTheory

/-- Equal laws in every measurable parameter fiber give equal joint laws when the
parameter is sampled independently. The parameter remains in the joint output. -/
theorem map_prod_fiber_eq_of_map_eq
    {T Ω Ω' E : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace E]
    (Q : Measure T) (μ : Measure Ω) (ν : Measure Ω')
    [SFinite Q] [SFinite μ] [SFinite ν]
    (F : T × Ω → E) (G : T × Ω' → E)
    (hF : Measurable F) (hG : Measurable G)
    (h : ∀ t, μ.map (fun ω => F (t, ω)) = ν.map (fun ω => G (t, ω))) :
    (Q.prod μ).map (fun p => (p.1, F p)) =
      (Q.prod ν).map (fun p => (p.1, G p)) := by
  have hFm : Measurable (fun p : T × Ω => (p.1, F p)) := measurable_fst.prodMk hF
  have hGm : Measurable (fun p : T × Ω' => (p.1, G p)) := measurable_fst.prodMk hG
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hFm hA, Measure.map_apply hGm hA,
    Measure.prod_apply (hFm hA), Measure.prod_apply (hGm hA)]
  refine lintegral_congr fun t => ?_
  have hAt : MeasurableSet (Prod.mk t ⁻¹' A) := measurable_prodMk_left hA
  have hFt : Measurable (fun ω => F (t, ω)) := hF.comp measurable_prodMk_left
  have hGt : Measurable (fun ω => G (t, ω)) := hG.comp measurable_prodMk_left
  change μ ((fun ω => F (t, ω)) ⁻¹' (Prod.mk t ⁻¹' A)) =
    ν ((fun ω => G (t, ω)) ⁻¹' (Prod.mk t ⁻¹' A))
  rw [← Measure.map_apply hFt hAt, ← Measure.map_apply hGt hAt, h t]

end LatticeProb
