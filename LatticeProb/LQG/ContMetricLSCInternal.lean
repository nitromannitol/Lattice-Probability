import LatticeProb.LQG.ContMetricLSC
import LatticeProb.Bonanno.LQGMetric.Metric.LengthSpace
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricIsLengthSpace
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricInternal

/-!
# Length spaces and internal metrics of continuous metrics as extended metrics

For a continuous metric `D` on `ℂ` and its lower semicontinuous extended metric
`contToLSCMetric D`:

* `isLengthSpace_contToLSCMetric`: if `(ℂ, D)` is a length space, so is `(ℂ, contToLSCMetric D)`
  (Ding-Gwynne's curve form: curves of length at most `D(x, y) + ε`).
* `internal_contToLSCMetric`: the internal metric `D(·, ·; U)` (infimum of lengths of paths in
  `U`) is the same in both settings, for every `U ⊆ ℂ`.
* `measurable_uncurry_subtype`: a measurable family of kernels `ℂ → ℂ → [0, ∞]` restricts to a
  measurable family of functions on `U × U`; this transfers the locality axiom.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace LatticeProb.LQG

/-- **Length spaces transfer**: if `(ℂ, D)` is a length space, then `contToLSCMetric D` is a
length space in the curve form of Ding-Gwynne. -/
theorem isLengthSpace_contToLSCMetric {D : LQGMetric.ContMetric} (hD : D.IsLength) :
    (contToLSCMetric D).IsLengthSpace := by
  intro x y _ ε hε
  obtain ⟨P, a, b, hab, hc, ha, hb, hlen⟩ :=
    (LQGMetric.MetricGeometry.isLengthSpace_iff_curves.mp hD) (D.pt x) (D.pt y) ε hε
  refine ⟨P, a, b, (isCurve_contToLSCMetric_iff D P a b).2 ⟨hab, hc⟩, ha, hb, ?_⟩
  exact (len_contToLSCMetric D P a b).trans_le hlen

/-- **Internal metrics agree**: for every `U ⊆ ℂ` and `z, w ∈ U`, the internal metric of
`contToLSCMetric D` on `U` (infimum of lengths of curves in `U`) equals the internal metric
`D(z, w; U)` of the continuous metric `D` (infimum of lengths of paths in `U`). -/
theorem internal_contToLSCMetric (D : LQGMetric.ContMetric) (U : Set ℂ) (p : U × U) :
    (contToLSCMetric D).internal U p = D.internal U p.1 p.2 := by
  apply le_antisymm
  · unfold LQGMetric.ContMetric.internal LQGMetric.MetricGeometry.internalEDist
    refine le_iInf fun γ => ?_
    have hc : ContinuousOn (D.pt ∘ γ.1.extend) (Icc 0 1) := γ.1.continuous_extend.continuousOn
    refine iInf_le_of_le γ.1.extend <| iInf_le_of_le 0 <| iInf_le_of_le 1 <|
      iInf_le_of_le ⟨zero_le_one, (continuousOn_contToLSCMetric_iff D _ _).2 hc⟩ <|
      iInf_le_of_le (fun t ht => ?_) <| iInf_le_of_le (Path.extend_zero γ.1) <|
      iInf_le_of_le (Path.extend_one γ.1) (len_contToLSCMetric D _ 0 1).le
    obtain ⟨u, hu, hu'⟩ := γ.2 ⟨t, ht⟩
    rw [Path.extend_apply γ.1 ht, ← hu']
    exact hu
  · unfold SupercriticalLQGUniqueness.LSCMetric.internal
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hY => le_iInf fun ha => le_iInf fun hb => ?_
    have h := LQGMetric.MetricGeometry.internalEDist_le_curveLength (Y := D.pt '' U) hP.1
      ((continuousOn_contToLSCMetric_iff D P _).1 hP.2) (fun t ht => ⟨P t, hY t ht, rfl⟩)
    rw [Function.comp_apply, Function.comp_apply, ha, hb] at h
    exact h.trans_eq (len_contToLSCMetric D P a b).symm

/-- The internal metric of `contToLSCMetric D` on `U`, as a function on `U × U`. -/
theorem internal_contToLSCMetric_fun (D : LQGMetric.ContMetric) (U : Set ℂ) :
    (contToLSCMetric D).internal U = fun p : U × U => D.internal U p.1 p.2 :=
  funext (internal_contToLSCMetric D U)

/-- A measurable family of kernels `F g : ℂ → ℂ → [0, ∞]` gives a measurable family of their
restrictions `(z, w) ↦ F g z w` to `U × U`. -/
theorem measurable_uncurry_subtype {α : Type*} [MeasurableSpace α] (U : Set ℂ)
    {F : α → ℂ → ℂ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun (g : α) (p : U × U) => F g p.1 p.2) :=
  measurable_pi_iff.mpr fun _ => (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hF)

end LatticeProb.LQG
