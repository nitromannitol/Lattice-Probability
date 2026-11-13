/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase.JointLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.Defs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA1A2
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Dilate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.WeakStrong

/-!
# The Case 3 and Case 4 laws of [18] Proposition 4.10

Source: (`[18]:N`), Proposition 4.10, Cases 3–4,
`[18]`; Appendix A, Lemma A.2, `[18]`.

Setting: a whole-plane GFF `h` normalized by `h_1(0) = 0`, and an independent random observation
`Y : Ω → 𝒴` together with a jointly measurable family `τ z₀ : 𝒴 → 𝒴` of Case 4 transformations
whose action preserves the law of `Y`. For the frozen bundle, `Y = ((hIG₀, U), ηL)` is the **full
imaginary-geometry data** (field, phase and curve) and `τ z₀` is the Case 4
transformation of the IG field and phase together with `case4Curve z₀` (`GMSCase/IGData.lean`).
The root `z₀` is either fixed or sampled independently.

* `map_case4_pair` (Case 4, fixed root): `(h(·/2 + z₀) − h_{1/2}(z₀), τ z₀ Y)` has the law of
  `(h, Y)`, a product.
* `map_case4_marked` (Case 4, independent root): with `z₀ ∼ λ` independent, the triple
  `(z₀, h(·/2 + z₀) − h_{1/2}(z₀), τ z₀ Y)` has law `λ ⊗ law(h) ⊗ law(Y)`.
* `indepFun_halfAvg_case4Local` (Case 3, fixed root with `B̄_{1/2}(z₀) ⊆ B̄_1(0)`): the Case 3
  index `h_{1/2}(z₀)` is **independent** of the Case 4 field restricted to the unit disk and of
  `τ z₀ Y`. This is the exact form of [18]'s Case 3 comparison: the conditional law of
  `h³|_{B_{1/2}(z₀)}` given `{h²_{1/2}(z₀) = a}` is its unconditional law (Radon–Nikodym
  derivative `M_{a,z₀} ≡ 1`; the analytic construction's `lemmaA2_indepFun`), so no Hölder step is needed in Case 3.
* `map_case3_marked`: with an independent root `z₀ ∼ λ` supported where
  `B̄_{1/2}(z₀) ⊆ B̄_1(0)`, the law of `((z₀, h_{1/2}(z₀)), (restricted Case 4 field, τ z₀ Y))`
  is the product of the law of `(z₀, h_{1/2}(z₀))` and of the law of `(restricted h, Y)` — the
  disintegration of the Case 2 law over the sampled average is the constant kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCase

open LQGMetric LQGMetric.Blueprint

/-! ## A three-variable independence lemma -/

/-- If `X ⟂ Y` and `(X, Y) ⟂ Z`, then `X ⟂ (Y, Z)`. -/
theorem indepFun_prodMk_of_indepFun {Ω α β δ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace δ] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → δ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXY : IndepFun X Y P) (hXYZ : IndepFun (fun ω => (X ω, Y ω)) Z P) :
    IndepFun X (fun ω => (Y ω, Z ω)) P := by
  have hXYm : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hYZm : Measurable fun ω => (Y ω, Z ω) := hY.prodMk hZ
  have hXYZm : Measurable fun ω => ((X ω, Y ω), Z ω) := hXYm.prodMk hZ
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hYZm.aemeasurable]
  have hYZ : IndepFun Y Z P := hXYZ.comp measurable_snd measurable_id
  have h1 : P.map (fun ω => ((X ω, Y ω), Z ω)) =
      (P.map fun ω => (X ω, Y ω)).prod (P.map Z) :=
    hXYZ.map_prod_eq_prod_map_map hXYm.aemeasurable hZ.aemeasurable
  have h2 : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have h3 : P.map (fun ω => (Y ω, Z ω)) = (P.map Y).prod (P.map Z) :=
    hYZ.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable
  have hmap : P.map (fun ω => (X ω, (Y ω, Z ω))) =
      (P.map fun ω => ((X ω, Y ω), Z ω)).map MeasurableEquiv.prodAssoc := by
    rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable hXYZm]
    rfl
  rw [hmap, h1, h2, Measure.prodAssoc_prod, h3]

/-! ## Case 4: the joint law at a fixed root -/

section Law

variable {Ω 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒴] {P : Measure Ω}
  {h : Ω → DistC} {Y : Ω → 𝒴} {τ : ℂ → 𝒴 → 𝒴}

theorem measurable_transform_right (hτ : Measurable fun p : ℂ × 𝒴 => τ p.1 p.2) (z₀ : ℂ) :
    Measurable fun y : 𝒴 => τ z₀ y := by
  have hpair : Measurable fun y : 𝒴 => ((z₀, y) : ℂ × 𝒴) :=
    measurable_const.prodMk measurable_id
  have h := hτ.comp (g := fun p : ℂ × 𝒴 => τ p.1 p.2)
    (f := fun y : 𝒴 => ((z₀, y) : ℂ × 𝒴)) hpair
  exact h

/-! ## Case 4: an independent root -/

/-! ## Case 3: independence of the sampled average -/

end Law

end MatedCRTHarmonic.GMSCase
