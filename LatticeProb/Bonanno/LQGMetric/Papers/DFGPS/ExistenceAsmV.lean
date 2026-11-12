/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.ExistenceAsmV at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20TranslB
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20BilipMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2, Axiom V for the limiting metric (part of the T1.2 assembly)

DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2, Step 1
(T:1356): "By Lemma 2.13, also Axiom V holds." Lemma 2.13 (`Lem2_13`) is stated for the
normalized field `h − h_1(0)` coupled with its limit metric; Axiom V (`TightAcrossScales`) is
about every whole-plane GFF. `tightAcrossScales_of_ref`: if `D` is measurable, satisfies Weyl
scaling by the constant `−h_1(0)` for whole-plane GFFs, and the conclusion of Lemma 2.13 holds for
`D ∘ h₀` with one normalized whole-plane GFF `h₀`, then Axiom V holds. Proof: the rescaled metric
`𝔠_r⁻¹ e^{−ξ h_r(0)} D_h(r·, r·)` is unchanged by `h ↦ h − h_1(0)` (constants cancel), and the law
of `h − h_1(0)` does not depend on the whole-plane GFF (`GM.Tight.map_normalize_eq`), as in
`GM.Tight.ae_scaledField_normalize` for weak metrics. Own bookkeeping (DEVIATIONS DFB12-5).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint GM.Tight

namespace ExistenceAsm

/-- the rescaled metric `𝔠_r⁻¹ e^{−ξ g_r(0)} D_g(r·, r·)` as a function of the field -/
def scaledAt0 (ξ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (r : ℝ) (g : DistC) :
    C(ℂ × ℂ, ℝ) :=
  ((c r)⁻¹ * Real.exp (-ξ * circleAvg g r 0)) • (D g).1.comp (scaleArgs r)

lemma measurable_scaledAt0 {ξ : ℝ} {D : DistC → ContMetric} (hD : Measurable D) (c : ℝ → ℝ)
    (r : ℝ) : Measurable (scaledAt0 ξ D c r) := by
  have h1 : Measurable fun g : DistC => (D g).1.comp (scaleArgs r) :=
    (ContinuousMap.continuous_precomp (scaleArgs r)).measurable.comp
      (measurable_subtype_coe.comp hD)
  have h2 : Measurable fun g : DistC => (c r)⁻¹ * Real.exp (-ξ * circleAvg g r 0) :=
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_circleAvg_left r 0)))
  exact h2.smul h1

/-- the rescaled metric does not see the normalization `h ↦ h − h_1(0)` -/
lemma ae_scaledAt0_normalize {ξ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hweyl : ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (addConst (h ω) (-circleAvg (h ω) 1 0))).1 (u, v) =
      Real.exp (-ξ * circleAvg (h ω) 1 0) * (D (h ω)).1 (u, v)) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, scaledAt0 ξ D c r (addConst (h ω) (-circleAvg (h ω) 1 0)) =
      scaledAt0 ξ D c r (h ω) := by
  filter_upwards [hweyl, CircleAvg.ae_circleAvg_addConst hh 0 hr] with ω hw hca
  ext p
  simp only [scaledAt0, ContinuousMap.smul_apply, ContinuousMap.comp_apply, smul_eq_mul]
  rw [hca, hw]
  have hx : Real.exp (-ξ * (circleAvg (h ω) r 0 + -circleAvg (h ω) 1 0)) *
      Real.exp (-ξ * circleAvg (h ω) 1 0) = Real.exp (-ξ * circleAvg (h ω) r 0) := by
    rw [← Real.exp_add]; ring_nf
  calc (c r)⁻¹ * Real.exp (-ξ * (circleAvg (h ω) r 0 + -circleAvg (h ω) 1 0)) *
        (Real.exp (-ξ * circleAvg (h ω) 1 0) * (D (h ω)).1 (scaleArgs r p))
      = (c r)⁻¹ * (Real.exp (-ξ * (circleAvg (h ω) r 0 + -circleAvg (h ω) 1 0)) *
        Real.exp (-ξ * circleAvg (h ω) 1 0)) * (D (h ω)).1 (scaleArgs r p) := by ring
    _ = _ := by rw [hx]

/-- the law of the rescaled metric is the same for every whole-plane GFF -/
lemma map_scaledAt0_eq {ξ : ℝ} {D : DistC → ContMetric} (hD : Measurable D) (c : ℝ → ℝ)
    (hweyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (D (addConst (h ω) (-circleAvg (h ω) 1 0))).1 (u, v) =
          Real.exp (-ξ * circleAvg (h ω) 1 0) * (D (h ω)).1 (u, v))
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsWholePlaneGFF h P) (hh' : IsWholePlaneGFF h' P') {r : ℝ} (hr : 0 < r) :
    P.map (fun ω => scaledAt0 ξ D c r (h ω)) = P'.map (fun ω => scaledAt0 ξ D c r (h' ω)) := by
  have hN := measurable_circleAvg_left 1 0
  have hm : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁} {h₁ : Ω₁ → DistC},
      IsWholePlaneGFF h₁ P₁ → Measurable fun ω => addConst (h₁ ω) (-circleAvg (h₁ ω) 1 0) :=
    fun hh₁ => (hh₁.addConst (hN.comp hh₁.measurable).neg).measurable
  have hF := measurable_scaledAt0 (ξ := ξ) hD c r
  calc P.map (fun ω => scaledAt0 ξ D c r (h ω))
      = P.map (scaledAt0 ξ D c r ∘ fun ω => addConst (h ω) (-circleAvg (h ω) 1 0)) :=
        Measure.map_congr ((ae_scaledAt0_normalize hh (hweyl P h hh) hr).mono fun ω hω => hω.symm)
    _ = (P.map fun ω => addConst (h ω) (-circleAvg (h ω) 1 0)).map (scaledAt0 ξ D c r) :=
        (Measure.map_map hF (hm hh)).symm
    _ = (P'.map fun ω => addConst (h' ω) (-circleAvg (h' ω) 1 0)).map (scaledAt0 ξ D c r) := by
        rw [map_normalize_eq hh hh']
    _ = P'.map (scaledAt0 ξ D c r ∘ fun ω => addConst (h' ω) (-circleAvg (h' ω) 1 0)) :=
        Measure.map_map hF (hm hh')
    _ = _ := Measure.map_congr (ae_scaledAt0_normalize hh' (hweyl P' h' hh') hr)

end ExistenceAsm

open ExistenceAsm in
/-- **Axiom V for the limiting metric** (T:1356, "by Lemma 2.13"): from the conclusion of Lemma
2.13 for one normalized whole-plane GFF, measurability and Weyl scaling by constants. -/
theorem tightAcrossScales_of_ref {γ : ℝ} {D : DistC → ContMetric} (hD : Measurable D)
    {c : ℝ → ℝ} {Λ : ℝ} (hc : ∀ r, 0 < r → 0 < c r) (hΛ : 1 < Λ)
    (hb : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
      Λ⁻¹ * δ ^ Λ ≤ c (δ * r) / c r ∧ c (δ * r) / c r ≤ Λ * δ ^ (-Λ))
    (hweyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (D (addConst (h ω) (-circleAvg (h ω) 1 0))).1 (u, v) =
          Real.exp (-xiGamma γ * circleAvg (h ω) 1 0) * (D (h ω)).1 (u, v))
    {Ω₀ : Type} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (h₀ : Ω₀ → DistC) (hh₀ : IsWholePlaneGFF h₀ P₀)
    (htight : IsTightMeasureSet {μ | ∃ r : ℝ, 0 < r ∧
      μ = P₀.map (fun ω => scaledAt0 (xiGamma γ) D c r (h₀ ω))})
    (hcl : ∀ μ : ProbabilityMeasure C(ℂ × ℂ, ℝ),
      μ ∈ closure {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) | ∃ r : ℝ, 0 < r ∧
        (ν : Measure C(ℂ × ℂ, ℝ)) = P₀.map (fun ω => scaledAt0 (xiGamma γ) D c r (h₀ ω))} →
      ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), IsContinuousMetric d) :
    TightAcrossScales (xiGamma γ) D c := by
  refine ⟨hc, ⟨Λ, hΛ, hb⟩, ?_⟩
  intro Ω _ P _ h hh
  have hlaw : ∀ r, 0 < r → P.map (fun ω => scaledAt0 (xiGamma γ) D c r (h ω)) =
      P₀.map (fun ω => scaledAt0 (xiGamma γ) D c r (h₀ ω)) := fun r hr =>
    map_scaledAt0_eq hD c hweyl hh hh₀ hr
  have hS : {μ | ∃ r : ℝ, 0 < r ∧ μ = P.map (fun ω => scaledAt0 (xiGamma γ) D c r (h ω))} =
      {μ | ∃ r : ℝ, 0 < r ∧ μ = P₀.map (fun ω => scaledAt0 (xiGamma γ) D c r (h₀ ω))} := by
    ext μ
    exact ⟨fun ⟨r, hr, e⟩ => ⟨r, hr, e.trans (hlaw r hr)⟩,
      fun ⟨r, hr, e⟩ => ⟨r, hr, e.trans (hlaw r hr).symm⟩⟩
  have hS' : {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) | ∃ r : ℝ, 0 < r ∧
      (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (fun ω => scaledAt0 (xiGamma γ) D c r (h ω))} =
      {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) | ∃ r : ℝ, 0 < r ∧
        (ν : Measure C(ℂ × ℂ, ℝ)) = P₀.map (fun ω => scaledAt0 (xiGamma γ) D c r (h₀ ω))} := by
    ext ν
    exact ⟨fun ⟨r, hr, e⟩ => ⟨r, hr, e.trans (hlaw r hr)⟩,
      fun ⟨r, hr, e⟩ => ⟨r, hr, e.trans (hlaw r hr).symm⟩⟩
  show IsTightMeasureSet {μ | ∃ r : ℝ, 0 < r ∧
      μ = P.map (fun ω => scaledAt0 (xiGamma γ) D c r (h ω))} ∧
    ∀ μ : ProbabilityMeasure C(ℂ × ℂ, ℝ),
      μ ∈ closure {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) | ∃ r : ℝ, 0 < r ∧
        (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (fun ω => scaledAt0 (xiGamma γ) D c r (h ω))} →
      ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), IsContinuousMetric d
  rw [hS, hS']
  exact ⟨htight, hcl⟩

end LQGMetric.DFGPS
