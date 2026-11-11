import Mathlib
import LatticeProb.LQG.LQGMetric
import LatticeProb.LQG.LQGMassInner
import LatticeProb.LQG.LQGMetricMeasurable

/-!
# Inner measurability of the LQG metric (PointwiseAE and internal diameter)

second half of the measurability argument. The two statements below are derived from the single literature input
`LQGMetricFieldAxioms` (Fact 2.2 I-II):

* `LatticeProb.LQG.LQGMetricPointwiseAEMeasurableLP`: pointwise a.e. measurability of the LQG metric, with the binders and
  conclusion of the source; proof `lqgMetricPointwiseAEMeasurable_lp`.
* `LatticeProb.LQG.LQGInternalDiamInnerMeasurableLP`: measurability of the inner internal diameter of an LQG metric set;
  proof `lqgInternalDiamInnerMeasurable_lp`.

The only hypothesis of each proof is the LP input `LQGMetricFieldAxioms` (`LatticeProb/LQG/LQGMetric.lean`), quantified
over the carriers. The deterministic inputs are `LatticeProb/LQG/LQGMetricMeasurable.lean` (continuity of
the internal metric on `O × O`) and `LatticeProb/LQG/LQGMassInner.lean` (monotonicity of the field σ-algebra in the open set).
Terminology: LQG metric, internal metric, internal diameter (Gwynne-Miller arXiv:1905.00383 Sec. 1.2; Bou-Rabee-Gwynne
arXiv:2208.11795 Fact 2.2).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal
open LatticeProb.Gauss

namespace LatticeProb.LQG

universe u

/-- Reduction of a supremum over a compact set to a countable dense subset: if `F` is continuous on `A × A`
(`A` compact, `Q ⊆ A` countable and dense in `A`), then `sup_{x ∈ A} sup_{y ∈ A} F x y = sup_{x ∈ Q} sup_{y ∈ Q} F x y`.
Proof: the set where `F ≤ b` (`b` the right-hand side) is relatively closed in `A × A` and contains `Q × Q`, hence
`A × A`. -/
theorem iSup_iSup_compact_eq_countable {F : ℂ → ℂ → ℝ≥0∞} {A Q : Set ℂ} (hA : IsCompact A)
    (hQA : Q ⊆ A) (hAQ : A ⊆ closure Q)
    (hF : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (A ×ˢ A)) :
    (⨆ x ∈ A, ⨆ y ∈ A, F x y) = ⨆ x : Q, ⨆ y : Q, F x y := by
  apply le_antisymm
  · have hclosed : IsClosed ((A ×ˢ A) ∩ (fun p : ℂ × ℂ => F p.1 p.2) ⁻¹' Iic (⨆ x : Q, ⨆ y : Q, F x y)) :=
      hF.preimage_isClosed_of_isClosed (hA.isClosed.prod hA.isClosed) isClosed_Iic
    have hQQ : Q ×ˢ Q ⊆
        (A ×ˢ A) ∩ (fun p : ℂ × ℂ => F p.1 p.2) ⁻¹' Iic (⨆ x : Q, ⨆ y : Q, F x y) := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      refine ⟨⟨hQA hx, hQA hy⟩, ?_⟩
      show F x y ≤ ⨆ x' : Q, ⨆ y' : Q, F x' y'
      exact le_iSup_of_le (⟨x, hx⟩ : Q) (le_iSup_of_le (⟨y, hy⟩ : Q) le_rfl)
    have hsub : A ×ˢ A ⊆ closure (Q ×ˢ Q) := by
      rw [closure_prod_eq]
      exact prod_mono hAQ hAQ
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    have hmem : (x, y) ∈ closure (Q ×ˢ Q) := hsub (show (x, y) ∈ A ×ˢ A from ⟨hx, hy⟩)
    exact (closure_minimal hQQ hclosed hmem).2
  · refine iSup_le fun x => iSup_le fun y => ?_
    exact le_iSup₂_of_le (x : ℂ) (hQA x.2) (le_iSup₂_of_le (y : ℂ) (hQA y.2) le_rfl)

/-- Pointwise a.e. measurability of the LQG metric: for a whole-plane
GFF realization `(hC, hcirc)` with `γ ∈ (0, 2)` and a realized LQG metric `D` of the field with zero exponent
(`IsLQGMetricOfField P γ ξ 0 hC D`), every evaluation `ω ↦ D ω x y` is almost everywhere measurable. -/
def LQGMetricPointwiseAEMeasurableLP : Prop :=
  ∀ (γ ξ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → IsLQGMetricOfField P γ ξ 0 hC D →
    ∀ x y : ℂ, AEMeasurable (fun ω => D ω x y) P

/-- Measurability of the inner internal diameter: for
`O = thickening δ A` with `A` compact, the internal diameter `internalDiam (D ω) δ A` is almost surely equal to a random
variable measurable for `fieldSigmaAlgebra α₀ hC O`. -/
def LQGInternalDiamInnerMeasurableLP : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMetricOfField P γ ξ α₀ hC D →
    ∀ (δ : ℝ) (A : Set ℂ), 0 < δ → IsCompact A →
    ∃ g : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC (thickening δ A)] g ∧
      ∀ᵐ ω ∂P, internalDiam (D ω) δ A = g ω

/-- **LP proof of `LQGMetricPointwiseAEMeasurableLP`.** Input: `hFA`, the LP input `LQGMetricFieldAxioms`
(Fact 2.2 I-II) in its universally quantified form. Written argument:
the metric `D_h` is finite a.s. (I); locality (II) with `U = ℂ` gives `G ω x y`, measurable for `σ(h|_ℂ)`, a.s. equal to
the internal metric of `D_h` over `ℂ`; a length metric satisfies `ofReal D = internalMetric D univ`, so `D_h = G` a.s.;
the pairings are measurable, so `σ(h|_ℂ)` lies in the ambient σ-algebra. -/
theorem lqgMetricPointwiseAEMeasurable_lp
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    LQGMetricPointwiseAEMeasurableLP := by
  intro γ ξ Ω mΩ P _ hC hcirc D hGFF hγ hγ2 hD x y
  obtain ⟨𝔇, hM, hae⟩ := hD
  have hα : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    exact add_pos (div_pos two_pos hγ) (half_pos hγ)
  obtain ⟨hI, hII, -, -⟩ := hFA γ ξ 0 Ω P hC hcirc hGFF hγ hγ2 hα 𝔇 hM
  obtain ⟨G, hGm, hG⟩ := hII Set.univ isOpen_univ
  have hle : fieldSigmaAlgebra 0 hC Set.univ ≤ mΩ := by
    unfold fieldSigmaAlgebra
    refine iSup₂_le fun φ hφ => ?_
    refine Measurable.comap_le ?_
    simpa [fieldPairing] using hGFF.measurable_pairing φ hφ
  have hGmeas : Measurable (fun ω => G ω x y) := (hGm x y).mono hle le_rfl
  have hEq : (fun ω => D ω x y) =ᵐ[P] (fun ω => (G ω x y).toReal) := by
    filter_upwards [hae, hI, hG] with ω hωae hωI hωG
    have hωD := hωae x y
    have h1 : ENNReal.ofReal (D ω x y) = G ω x y := by
      rw [hωD.2, ← hωG x (mem_univ x) y (mem_univ y), ← hωI.2.ofReal_eq_internalMetric x y,
        ENNReal.ofReal_toReal (hωI.1 x y).ne]
    rw [← h1, ENNReal.toReal_ofReal hωD.1]
  exact hGmeas.ennreal_toReal.aemeasurable.congr hEq.symm

/-- **LP proof of `LQGInternalDiamInnerMeasurableLP`.** Input: `hFA`, the LP input `LQGMetricFieldAxioms` (Fact 2.2 I-II).
Written argument: the internal metric over `O = thickening δ A` is a.s.
given by a family `G` of `σ(h|_O)`-measurable functions (II); `D` is a.s. a Euclidean length metric, whose internal metric
is continuous on `O × O` (`IsEuclideanLengthMetric.continuousOn_internalMetric_pair`); so `internalDiam D δ A` is a.s. the
supremum of `G` over a countable dense subset of `A`, which is `σ(h|_O)`-measurable. -/
theorem lqgInternalDiamInnerMeasurable_lp
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    LQGInternalDiamInnerMeasurableLP.{u} := by
  intro γ ξ α₀ Ω _ P _ hC hcirc D hW h0 h1 h2 hD δ A hδ hA
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  obtain ⟨hI, hII, -, -⟩ := hFA γ ξ α₀ Ω P hC hcirc hW h0 h1 h2 𝔇 h𝔇
  have hO : IsOpen (thickening δ A) := isOpen_thickening
  have hAO : A ⊆ thickening δ A := self_subset_thickening hδ A
  obtain ⟨G, hGm, hGae⟩ := hII (thickening δ A) hO
  obtain ⟨Q, hQc, hQA, hAQ⟩ := TopologicalSpace.exists_countable_dense_subset A
  have : Countable Q := hQc.to_subtype
  refine ⟨fun ω => ⨆ x : Q, ⨆ y : Q, G ω x y, ?_, ?_⟩
  · exact Measurable.iSup fun x => Measurable.iSup fun y => hGm x y
  · filter_upwards [hI, hGae, hDae] with ω hIω hGω hDω
    have hDeq : ∀ u v, D ω u v = (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      intro u v
      obtain ⟨h0', h1'⟩ := hDω u v
      rw [← h1', ENNReal.toReal_ofReal h0']
    have hfun : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal :=
      funext fun u => funext fun v => hDeq u v
    have hnn : ∀ x y, 0 ≤ D ω x y := fun x y => by rw [hDeq x y]; exact ENNReal.toReal_nonneg
    have hIE : IsEuclideanLengthMetric (D ω) := by
      rw [hfun]
      exact hIω.2
    have hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric (D ω) (thickening δ A) p.1 p.2) (A ×ˢ A) :=
      (hIE.continuousOn_internalMetric_pair hnn hO).mono (prod_mono hAO hAO)
    have hred := iSup_iSup_compact_eq_countable (F := internalMetric (D ω) (thickening δ A)) hA hQA hAQ hcont
    rw [internalDiam, hred, hfun]
    exact iSup_congr fun x => iSup_congr fun y => hGω x.1 (hAO (hQA x.2)) y.1 (hAO (hQA y.2))

end LatticeProb.LQG
