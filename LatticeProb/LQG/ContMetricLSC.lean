import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.WeylScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricLen
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Support.LSCMetricInstCoeFun

/-!
# Continuous metrics as lower semicontinuous extended metrics

A continuous metric `D` on `ℂ` (`LQGMetric.ContMetric`, the setting of Gwynne-Miller) defines a lower
semicontinuous extended metric `(z, w) ↦ D(z, w) ∈ [0, ∞)` on `ℂ` (`LSCMetric`, the setting of
Ding-Gwynne's weak LQG metrics for all `ξ > 0`). The identity of `ℂ` is an isometry between the two
metric spaces, so curves, lengths, unit-speed parametrizations and Weyl scalings agree.

## Main results

* `contToLSCMetric D`: the extended metric `(z, w) ↦ D(z, w)`, lower semicontinuous since `D` is
  continuous.
* `len_contToLSCMetric`, `isCurve_contToLSCMetric_iff`, `hasUnitSpeedOn_contToLSCMetric_iff`: lengths,
  curves and unit-speed curves are the same for `D` and `contToLSCMetric D`.
* `weylScale_contToLSCMetric`: the Weyl scaling `e^{ξ f} · D` (infimum of `∫₀ᴸ e^{ξ f(P t)} dt` over
  unit-speed curves) is the same in both settings.
* `weylScale_contToLSCMetric_eq`: Weyl scaling identities `e^{ξ f} · D = D'` transfer to the extended
  metrics.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace LatticeProb.LQG

/-- A continuous metric `D` on `ℂ` as a lower semicontinuous extended metric: `(z, w) ↦ D(z, w)`. -/
def contToLSCMetric (D : LQGMetric.ContMetric) : SupercriticalLQGUniqueness.LSCMetric :=
  ⟨fun p => edist (D.pt p.1) (D.pt p.2),
    ⟨fun _ => edist_self _, fun x y h => by
        have h' : edist (D.pt x) (D.pt y) = 0 := h
        have h'' : D.pt x = D.pt y := edist_eq_zero.mp h'
        exact h'',
      fun _ _ => edist_comm _ _, fun _ _ _ => edist_triangle _ _ _⟩,
    (continuous_edist.comp ((D.continuous_pt.comp continuous_fst).prodMk
        (D.continuous_pt.comp continuous_snd))).lowerSemicontinuous⟩

@[simp] theorem contToLSCMetric_apply (D : LQGMetric.ContMetric) (p : ℂ × ℂ) :
    contToLSCMetric D p = ENNReal.ofReal (D.1 p) :=
  D.edist_pt p.1 p.2

theorem edist_contToLSCMetric_pt (D : LQGMetric.ContMetric) (x y : ℂ) :
    edist ((contToLSCMetric D).pt x) ((contToLSCMetric D).pt y) = edist (D.pt x) (D.pt y) :=
  rfl

/-- The identity of `ℂ` is an isometry from `(ℂ, D)` to `(ℂ, contToLSCMetric D)`. -/
theorem isometry_contToLSCMetric (D : LQGMetric.ContMetric) :
    Isometry (fun x : D.Space => (contToLSCMetric D).pt x) :=
  fun x y => edist_contToLSCMetric_pt D x y

theorem continuousOn_contToLSCMetric_iff (D : LQGMetric.ContMetric) (P : ℝ → ℂ) (S : Set ℝ) :
    ContinuousOn ((contToLSCMetric D).pt ∘ P) S ↔ ContinuousOn (D.pt ∘ P) S :=
  (isometry_contToLSCMetric D).comp_continuousOn_iff (g := D.pt ∘ P) (s := S)

theorem eVariationOn_contToLSCMetric (D : LQGMetric.ContMetric) (P : ℝ → ℂ) (S : Set ℝ) :
    eVariationOn ((contToLSCMetric D).pt ∘ P) S = eVariationOn (D.pt ∘ P) S :=
  (LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
    (F := (contToLSCMetric D).pt ∘ P) (G := D.pt ∘ P) (c := 1)
    (fun s t => by rw [one_mul]; exact edist_contToLSCMetric_pt D (P s) (P t)) S).trans
    (one_mul _)

theorem len_contToLSCMetric (D : LQGMetric.ContMetric) (P : ℝ → ℂ) (a b : ℝ) :
    (contToLSCMetric D).len P a b = D.len P a b :=
  eVariationOn_contToLSCMetric D P (Icc a b)

theorem isCurve_contToLSCMetric_iff (D : LQGMetric.ContMetric) (P : ℝ → ℂ) (a b : ℝ) :
    (contToLSCMetric D).IsCurve P a b ↔ a ≤ b ∧ ContinuousOn (D.pt ∘ P) (Icc a b) :=
  and_congr Iff.rfl (continuousOn_contToLSCMetric_iff D P (Icc a b))

theorem hasUnitSpeedOn_contToLSCMetric_iff (D : LQGMetric.ContMetric) (P : ℝ → ℂ) (S : Set ℝ) :
    HasUnitSpeedOn ((contToLSCMetric D).pt ∘ P) S ↔ HasUnitSpeedOn (D.pt ∘ P) S := by
  constructor
  · intro hu x hx y hy
    exact (eVariationOn_contToLSCMetric D P _).symm.trans (hu hx hy)
  · intro hu x hx y hy
    exact (eVariationOn_contToLSCMetric D P _).trans (hu hx hy)

/-- **Weyl scaling agrees**: `(e^{ξ f} · D)(z, w)` computed for the extended metric
`contToLSCMetric D` (Ding-Gwynne) equals the Weyl scaling of the continuous metric `D`
(Gwynne-Miller (1.6)). -/
theorem weylScale_contToLSCMetric (ξ : ℝ) (f : C(ℂ, ℝ)) (D : LQGMetric.ContMetric) (z w : ℂ) :
    SupercriticalLQGUniqueness.weylScale ξ f (contToLSCMetric D) (z, w) =
      LQGMetric.weylScale ξ f D z w := by
  apply le_antisymm
  · unfold LQGMetric.weylScale
    refine le_iInf fun L => le_iInf fun P => le_iInf fun hL =>
      le_iInf fun _ => le_iInf fun hu => le_iInf fun h0 => le_iInf fun h1 => ?_
    have hu' := (hasUnitSpeedOn_contToLSCMetric_iff D P (Icc 0 L)).2 hu
    exact iInf_le_of_le P <| iInf_le_of_le L <|
      iInf_le_of_le (show (contToLSCMetric D).IsCurve P 0 L from
        ⟨hL, LQGMetric.MetricGeometry.continuousOn_of_hasUnitSpeedOn hu'⟩) <|
      iInf_le_of_le hu' <| iInf_le_of_le h0 <| iInf_le_of_le h1 le_rfl
  · unfold SupercriticalLQGUniqueness.weylScale
    refine le_iInf fun P => le_iInf fun L => le_iInf fun hP =>
      le_iInf fun hu => le_iInf fun h0 => le_iInf fun h1 => ?_
    have hu' := (hasUnitSpeedOn_contToLSCMetric_iff D P (Icc 0 L)).1 hu
    exact iInf_le_of_le L <| iInf_le_of_le P <|
      iInf_le_of_le hP.1 <|
      iInf_le_of_le (LQGMetric.MetricGeometry.continuousOn_of_hasUnitSpeedOn hu') <|
      iInf_le_of_le hu' <| iInf_le_of_le h0 <| iInf_le_of_le h1 le_rfl

/-- A Weyl scaling identity `e^{ξ f} · D = D'` of continuous metrics gives the same identity of
the extended metrics `contToLSCMetric D`, `contToLSCMetric D'` (as functions on `ℂ × ℂ`). -/
theorem weylScale_contToLSCMetric_eq {ξ : ℝ} {f : C(ℂ, ℝ)} {D D' : LQGMetric.ContMetric}
    (h : ∀ z w : ℂ, LQGMetric.weylScale ξ f D z w = ENNReal.ofReal (D'.1 (z, w))) :
    SupercriticalLQGUniqueness.weylScale ξ f (contToLSCMetric D) = (contToLSCMetric D').1 := by
  funext ⟨z, w⟩
  rw [weylScale_contToLSCMetric, h]
  exact (contToLSCMetric_apply D' (z, w)).symm

end LatticeProb.LQG
