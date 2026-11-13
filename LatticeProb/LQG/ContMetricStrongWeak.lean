import LatticeProb.LQG.ContMetricLSCCoordChange
import LatticeProb.LQG.ContMetricInternalFinite
import LatticeProb.LQG.ContMetricLSCInternal
import LatticeProb.LQG.ContMetricLSCMeasurable
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Bridge

/-!
# A γ-LQG metric as a strong and weak LQG metric with lower semicontinuous values

A (strong) γ-LQG metric in the sense of Gwynne and Miller (arXiv:1905.00383, Section 1.2) is a
measurable map `h ↦ D_h` from distributions to continuous metrics on `ℂ` satisfying the length
space, locality, Weyl scaling and coordinate change axioms whenever `h` is a whole-plane GFF plus a
continuous function. Ding and Gwynne (arXiv:2110.00177, Section 1.2) state the axioms of a strong
LQG metric with parameter `ξ > 0` and exponent `Q` for maps into lower semicontinuous metrics; their
Axiom V asks that internal distances between compact connected nontrivial sets in a connected open
set are finite.

* `isStrongLQGMetric_contToLSCMetric`: for `γ > 0`, a Gwynne-Miller γ-LQG metric `D`, viewed as a
  lower semicontinuous metric (`contToLSCMetric ∘ D`), is a strong LQG metric with parameter
  `ξ_γ = γ / d_γ` and exponent `Q_γ = 2/γ + γ/2`;
* `isWeakLQGMetric_contToLSCMetric`: it is therefore a weak LQG metric with these parameters.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.LQG

/-- **Axiom V for continuous length metrics.** For a connected open `U` and nonempty `K₁, K₂ ⊆ U`,
the internal set distance of `contToLSCMetric D` between `K₁` and `K₂` in `U` is finite whenever `D`
is a length metric. -/
theorem internalSetDist_contToLSCMetric_lt_top (D : LQGMetric.ContMetric) (hD : D.IsLength)
    {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {K₁ K₂ : Set ℂ} (h₁ : K₁.Nonempty)
    (h₂ : K₂.Nonempty) (hs₁ : K₁ ⊆ U) (hs₂ : K₂ ⊆ U) :
    (contToLSCMetric D).internalSetDist U (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) < ∞ := by
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨y, hy⟩ := h₂
  exact iInf_internal_contToLSCMetric_lt_top D hD hU hc
    (K₁ := Subtype.val ⁻¹' K₁) (K₂ := Subtype.val ⁻¹' K₂)
    ⟨⟨x, hs₁ hx⟩, hx⟩ ⟨⟨y, hs₂ hy⟩, hy⟩

/-- **A γ-LQG metric is a strong LQG metric with lower semicontinuous values.** For `γ > 0` and a
Gwynne-Miller γ-LQG metric `D`, the map `h ↦ contToLSCMetric (D h)` satisfies the Ding-Gwynne axioms
of a strong LQG metric with parameter `ξ_γ = γ / d_γ` and exponent `Q_γ`. -/
theorem isStrongLQGMetric_contToLSCMetric {γ : ℝ} (hγ : 0 < γ)
    {D : LQGMetric.DistC → LQGMetric.ContMetric} (hD : LQGMetric.IsStrongLQGMetric γ D) :
    SupercriticalLQGUniqueness.IsStrongLQGMetric
      ⟨LQGMetric.xiGamma γ, LQGMetric.DG.xiGamma_pos hγ⟩ (LQGMetric.Q γ)
      (fun h => contToLSCMetric (D h)) := by
  refine ⟨measurable_contToLSCMetric.comp hD.measurable, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω _ P _ h hh
    filter_upwards [hD.length P h hh] with ω hω
    exact isLengthSpace_contToLSCMetric hω
  · intro Ω _ P _ h hh U
    obtain ⟨F, hF, hae⟩ := hD.locality P h hh U
    refine ⟨fun g p => F g p.1 p.2, measurable_uncurry_subtype (U : Set ℂ) hF, ?_⟩
    filter_upwards [hae] with ω hω
    rw [internal_contToLSCMetric_fun]
    funext p
    exact hω p.1 p.1.2 p.2 p.2.2
  · intro Ω _ P _ h hh
    filter_upwards [hD.weyl P h hh] with ω hω f
    exact weylScale_contToLSCMetric_eq (hω f)
  · intro Ω _ P _ h hh r z
    simp only [SupercriticalLQGUniqueness.B2.Strong.scaleTranslateDist_eq_affineComp]
    exact coordChange_contToLSCMetric_of_coord hD.coord P h hh r z
  · intro Ω _ P _ h hh U hUc K₁ K₂ _ _ _ _ hn₁ hn₂ hs₁ hs₂ _
    filter_upwards [hD.length P h hh] with ω hω
    exact internalSetDist_contToLSCMetric_lt_top (D (h ω)) hω U.isOpen hUc hn₁.nonempty
      hn₂.nonempty hs₁ hs₂

/-- **A γ-LQG metric is a weak LQG metric with lower semicontinuous values.** For `γ > 0` and a
Gwynne-Miller γ-LQG metric `D`, the map `h ↦ contToLSCMetric (D h)` is a Ding-Gwynne weak LQG metric
with parameter `ξ_γ = γ / d_γ` and exponent `Q_γ`. -/
theorem isWeakLQGMetric_contToLSCMetric {γ : ℝ} (hγ : 0 < γ)
    {D : LQGMetric.DistC → LQGMetric.ContMetric} (hD : LQGMetric.IsStrongLQGMetric γ D) :
    SupercriticalLQGUniqueness.IsWeakLQGMetric
      ⟨LQGMetric.xiGamma γ, LQGMetric.DG.xiGamma_pos hγ⟩ (LQGMetric.Q γ)
      (fun h => contToLSCMetric (D h)) :=
  SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric
    (isStrongLQGMetric_contToLSCMetric hγ hD)

end LatticeProb.LQG
