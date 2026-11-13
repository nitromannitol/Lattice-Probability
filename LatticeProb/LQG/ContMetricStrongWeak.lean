import LatticeProb.LQG.ContMetricLSCCoordChange
import LatticeProb.LQG.ContMetricInternalFinite
import LatticeProb.LQG.ContMetricLSCInternal
import LatticeProb.LQG.ContMetricLSCMeasurable
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Bridge
import LatticeProb.LQG.DistExpXiGamma

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
* `isStrongLQGMetric_contToLSCMetric_of_axioms`, `isWeakLQGMetric_contToLSCMetric_of_axioms`: the
  same for a map satisfying the Gwynne-Miller axioms with an arbitrary Weyl exponent `ξ > 0` and an
  arbitrary exponent `Q` in the coordinate change axiom.
* `eq_xiGamma_of_axioms`: for `γ ∈ (0, 2)`, the Weyl exponent `ξ > 0` of a map satisfying these
  axioms with `Q = Q_γ` is `ξ_γ`, given Pfeffer's Proposition 1.9 (arXiv:2104.04020, p. 7) in the
  form: every weak LQG metric with parameter `ξ` and exponent `Q` has `Q = Q(ξ)`, the LFPP distance
  exponent of `ξ`.
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

/-- **The Gwynne-Miller axioms give a strong LQG metric with lower semicontinuous values.** Let
`ξ > 0` and `Q ∈ ℝ`. If a measurable map `D` from distributions to continuous metrics satisfies, whenever
`h` is a whole-plane GFF plus a continuous function, the length space, locality, Weyl scaling (with
exponent `ξ`) and coordinate change (with exponent `Q`) axioms of Gwynne-Miller (arXiv:1905.00383,
Section 1.2), then `h ↦ contToLSCMetric (D h)` satisfies the Ding-Gwynne axioms of a strong LQG
metric with parameter `ξ` and exponent `Q`. -/
theorem isStrongLQGMetric_contToLSCMetric_of_axioms {ξ : ℝ} (hξ : 0 < ξ) {Q' : ℝ}
    {D : LQGMetric.DistC → LQGMetric.ContMetric} (hm : Measurable D)
    (hlen : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLength)
    (hloc : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
        ∃ F : LQGMetric.DistOn U → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
          ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
            (D (h ω)).internal U z w = F (LQGMetric.restrictTo U (h ω)) z w)
    (hweyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ),
        ∀ z w : ℂ, LQGMetric.weylScale ξ f (D (h ω)) z w =
          ENNReal.ofReal ((D (LQGMetric.addFun (h ω) f)).1 (z, w)))
    (hcoord : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (r * u + z, r * v + z) =
          (D (LQGMetric.addConst (LQGMetric.affineComp r z (h ω)) (Q' * Real.log r))).1 (u, v)) :
    SupercriticalLQGUniqueness.IsStrongLQGMetric ⟨ξ, hξ⟩ Q' (fun h => contToLSCMetric (D h)) := by
  refine ⟨measurable_contToLSCMetric.comp hm, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω _ P _ h hh
    filter_upwards [hlen P h hh] with ω hω
    exact isLengthSpace_contToLSCMetric hω
  · intro Ω _ P _ h hh U
    obtain ⟨F, hF, hae⟩ := hloc P h hh U
    refine ⟨fun g p => F g p.1 p.2, measurable_uncurry_subtype (U : Set ℂ) hF, ?_⟩
    filter_upwards [hae] with ω hω
    rw [internal_contToLSCMetric_fun]
    funext p
    exact hω p.1 p.1.2 p.2 p.2.2
  · intro Ω _ P _ h hh
    filter_upwards [hweyl P h hh] with ω hω f
    exact weylScale_contToLSCMetric_eq (hω f)
  · intro Ω _ P _ h hh r z
    simp only [SupercriticalLQGUniqueness.B2.Strong.scaleTranslateDist_eq_affineComp]
    exact coordChange_contToLSCMetric_of_coord hcoord P h hh r z
  · intro Ω _ P _ h hh U hUc K₁ K₂ _ _ _ _ hn₁ hn₂ hs₁ hs₂ _
    filter_upwards [hlen P h hh] with ω hω
    exact internalSetDist_contToLSCMetric_lt_top (D (h ω)) hω U.isOpen hUc hn₁.nonempty
      hn₂.nonempty hs₁ hs₂

/-- **The Gwynne-Miller axioms give a weak LQG metric with lower semicontinuous values.** Under the
hypotheses of `isStrongLQGMetric_contToLSCMetric_of_axioms`, `h ↦ contToLSCMetric (D h)` is a
Ding-Gwynne weak LQG metric with parameter `ξ` and exponent `Q`. -/
theorem isWeakLQGMetric_contToLSCMetric_of_axioms {ξ : ℝ} (hξ : 0 < ξ) {Q' : ℝ}
    {D : LQGMetric.DistC → LQGMetric.ContMetric} (hm : Measurable D)
    (hlen : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLength)
    (hloc : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
        ∃ F : LQGMetric.DistOn U → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
          ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
            (D (h ω)).internal U z w = F (LQGMetric.restrictTo U (h ω)) z w)
    (hweyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ),
        ∀ z w : ℂ, LQGMetric.weylScale ξ f (D (h ω)) z w =
          ENNReal.ofReal ((D (LQGMetric.addFun (h ω) f)).1 (z, w)))
    (hcoord : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (r * u + z, r * v + z) =
          (D (LQGMetric.addConst (LQGMetric.affineComp r z (h ω)) (Q' * Real.log r))).1 (u, v)) :
    SupercriticalLQGUniqueness.IsWeakLQGMetric ⟨ξ, hξ⟩ Q' (fun h => contToLSCMetric (D h)) :=
  SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric
    (isStrongLQGMetric_contToLSCMetric_of_axioms hξ hm hlen hloc hweyl hcoord)

/-- **A γ-LQG metric is a strong LQG metric with lower semicontinuous values.** For `γ > 0` and a
Gwynne-Miller γ-LQG metric `D`, the map `h ↦ contToLSCMetric (D h)` satisfies the Ding-Gwynne axioms
of a strong LQG metric with parameter `ξ_γ = γ / d_γ` and exponent `Q_γ`. -/
theorem isStrongLQGMetric_contToLSCMetric {γ : ℝ} (hγ : 0 < γ)
    {D : LQGMetric.DistC → LQGMetric.ContMetric} (hD : LQGMetric.IsStrongLQGMetric γ D) :
    SupercriticalLQGUniqueness.IsStrongLQGMetric
      ⟨LQGMetric.xiGamma γ, LQGMetric.DG.xiGamma_pos hγ⟩ (LQGMetric.Q γ)
      (fun h => contToLSCMetric (D h)) :=
  isStrongLQGMetric_contToLSCMetric_of_axioms _ hD.measurable hD.length hD.locality hD.weyl
    hD.coord

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

/-- **The Weyl exponent of an LQG metric with exponent `Q_γ`.** Let `γ ∈ (0, 2)` and `ξ > 0`. Assume
Pfeffer's Proposition 1.9 (arXiv:2104.04020, p. 7: the scaling constants of a weak LQG metric with
parameter `ξ` satisfy `c_{δ r} / c_r = δ^{ξ Q(ξ) + o(1)}`) in the form `hexp`: every weak LQG metric
with parameter `ξ` and exponent `Q` (scaling constants `c_r = r^{ξ Q}`) has `Q = Q(ξ)`, the LFPP
distance exponent `distExp 2 ξ`. If a measurable map `D` from distributions to continuous metrics
satisfies the Gwynne-Miller axioms with Weyl exponent `ξ` and exponent `Q_γ = 2/γ + γ/2`, then
`ξ = ξ_γ = γ / d_γ`. -/
theorem eq_xiGamma_of_axioms {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ : ℝ} (hξ : 0 < ξ)
    {D : LQGMetric.DistC → LQGMetric.ContMetric} (hm : Measurable D)
    (hlen : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLength)
    (hloc : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
        ∃ F : LQGMetric.DistOn U → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
          ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
            (D (h ω)).internal U z w = F (LQGMetric.restrictTo U (h ω)) z w)
    (hweyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ),
        ∀ z w : ℂ, LQGMetric.weylScale ξ f (D (h ω)) z w =
          ENNReal.ofReal ((D (LQGMetric.addFun (h ω) f)).1 (z, w)))
    (hcoord : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (r * u + z, r * v + z) =
          (D (LQGMetric.addConst (LQGMetric.affineComp r z (h ω)) (LQGMetric.Q γ * Real.log r))).1 (u, v))
    (hexp : ∀ (ξ' : Set.Ioi (0 : ℝ)) (Q : ℝ)
      (D' : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric),
      SupercriticalLQGUniqueness.IsWeakLQGMetric ξ' Q D' → HigherDimLQGMetric.distExp 2 ξ' = Q) :
    ξ = LQGMetric.xiGamma γ :=
  (distExp_two_eq_Q_iff hγ hγ2 hξ).1
    (hexp ⟨ξ, hξ⟩ _ _ (isWeakLQGMetric_contToLSCMetric_of_axioms hξ hm hlen hloc hweyl hcoord))

end LatticeProb.LQG
