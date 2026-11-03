/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S1.StrongWeak at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Defs
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelMetric
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Subseq

/-!
# GM §1.4: `C D` is a weak metric (GM.S1.7) and the axioms I–IV′ for a strong metric

Source: Gwynne–Miller, arXiv:1905.00383v3 (GM), `literature/src/1905.00383/uniqueness-final.tex`.

* `gm_s1_7` (GM.S1.7, used at l. 588: "`C D` is again a weak γ-LQG metric"): if `D` is a weak
  γ-LQG metric with scaling constants `𝔠_r`, then `C D` is one with constants `C 𝔠_r`; the
  normalized fields `𝔠_r⁻¹ e^{−ξ h_r(0)} D_h(r·, r·)` of Axiom V are unchanged, Axioms I–III and
  IV′ follow by scaling (lengths, internal metrics and Weyl scalings of `C D` are `C` times those
  of `D`: `MetricGeometry.internalEDist_image_of_edist_eq`, `weylScale_smul`).
* `IsStrongLQGMetric.translation` (Axiom IV′ from Axiom IV with `r = 1`, GM l. 452–458).
* `GM.tightAcrossScales_of_strong`, `GM.gm_eq1_15_of_circleAvg` (GM (1.15), l. 452–465): a strong
  metric is weak with `𝔠_r = r^{ξQ}`, `Λ = |ξQ| + 2`, given the circle-average scaling
  `(h(r·))_1(0) = h_r(0)` a.s. (P2-FCIRC leaf (b), hypothesis `hcirc`).

Own elementary proofs of steps GM leaves implicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

theorem ContMetric.smulPos_eq_smul (C : ℝ) (hC : 0 < C) (D : ContMetric) :
    D.smulPos C hC = D.smul C hC := rfl

/-- `C D` is a length metric if `D` is -/
theorem ContMetric.isLength_smulPos {C : ℝ} (hC : 0 < C) {D : ContMetric} (hD : D.IsLength) :
    (D.smulPos C hC).IsLength := by
  intro x y ε hε
  let f : D.Space → (D.smulPos C hC).Space := fun z => z
  have hf : ∀ a b, edist (f a) (f b) = ENNReal.ofReal C * edist a b :=
    fun a b => D.edist_smul C hC a b
  have hfc : Continuous f :=
    (show LipschitzWith (Real.toNNReal C) f from fun a b => (hf a b).le).continuous
  let x' : D.Space := x
  let y' : D.Space := y
  obtain ⟨γ, hγ⟩ := hD x' y' (ε / C) (div_pos hε hC)
  refine ⟨γ.map hfc, ?_⟩
  calc MetricGeometry.pathLength (γ.map hfc) = ENNReal.ofReal C * MetricGeometry.pathLength γ :=
        MetricGeometry.pathLength_map_of_edist_eq hf hfc γ
    _ ≤ ENNReal.ofReal C * (edist x' y' + ENNReal.ofReal (ε / C)) := by gcongr
    _ = edist (f x') (f y') + ENNReal.ofReal ε := by
        rw [mul_add, ← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne', ← hf]

/-- internal metrics of `C D` are `C` times those of `D` -/
theorem ContMetric.internal_smulPos {C : ℝ} (hC : 0 < C) (D : ContMetric) (U : Set ℂ)
    (z w : ℂ) : (D.smulPos C hC).internal U z w = ENNReal.ofReal C * D.internal U z w := by
  have h := MetricGeometry.internalEDist_image_of_edist_eq (X := D.Space)
    (Z := (D.smulPos C hC).Space) (Equiv.refl ℂ) (c := ENNReal.ofReal C)
    (ENNReal.ofReal_pos.2 hC).ne' ENNReal.ofReal_ne_top (fun a b => D.edist_smul C hC a b)
    (D.pt '' U) z w
  unfold ContMetric.internal
  convert h using 2
  all_goals first | rfl | (ext x; exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => hyx ▸ hy⟩)

namespace GM

variable {γ : ℝ}

theorem measurable_smulMetric {D : DistC → ContMetric} (hD : Measurable D) {C : ℝ}
    (hC : 0 < C) : Measurable (smulMetric C hC D) :=
  ((continuous_const_smul C).measurable.comp (measurable_subtype_coe.comp hD)).subtype_mk

/-- **GM.S1.7**: `C D` is a weak γ-LQG metric with scaling constants `C 𝔠_r`. -/
theorem gm_s1_7 {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {C : ℝ}
    (hC : 0 < C) : IsWeakLQGMetric γ (smulMetric C hC D) (fun r => C * c r) where
  measurable := measurable_smulMetric hD.measurable hC
  length P _ h hh := by
    filter_upwards [hD.length P h hh] with ω hω using ContMetric.isLength_smulPos hC hω
  locality P _ h hh U := by
    obtain ⟨F, hFm, hF⟩ := hD.locality P h hh U
    refine ⟨fun g z w => ENNReal.ofReal C * F g z w, ?_, ?_⟩
    · exact measurable_pi_iff.2 fun z => measurable_pi_iff.2 fun w =>
        ((measurable_pi_apply w).comp ((measurable_pi_apply z).comp hFm)).const_mul _
    · filter_upwards [hF] with ω hω z hz w hw
      rw [smulMetric, ContMetric.internal_smulPos, hω z hz w hw]
  weyl P _ h hh := by
    filter_upwards [hD.weyl P h hh] with ω hω f z w
    rw [smulMetric, smulMetric, ContMetric.smulPos_eq_smul, weylScale_smul, hω f z w,
      ContMetric.smulPos_apply, ENNReal.ofReal_mul hC.le]
  translation P _ h hh z := by
    filter_upwards [hD.translation P h hh z] with ω hω u v
    simp only [smulMetric, ContMetric.smulPos_apply, hω u v]
  tightness := by
    obtain ⟨hpos, ⟨Λ, hΛ, hrat⟩, hT⟩ := hD.tightness
    refine ⟨fun r hr => mul_pos hC (hpos r hr), ⟨Λ, hΛ, fun δ hδ r hr => ?_⟩, ?_⟩
    · rw [mul_div_mul_left _ _ hC.ne']
      exact hrat δ hδ r hr
    · intro Ω _ P _ h hh
      have hX : ∀ (r : ℝ) (ω : Ω),
          ((C * c r)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) r 0)) •
            (smulMetric C hC D (h ω)).1.comp (scaleArgs r) =
          ((c r)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) r 0)) •
            (D (h ω)).1.comp (scaleArgs r) := by
        intro r ω
        ext p
        simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, smul_eq_mul, smulMetric,
          ContMetric.smulPos_apply]
        rw [mul_inv]
        calc C⁻¹ * (c r)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) r 0) *
              (C * (D (h ω)).1 ((scaleArgs r) p))
            = (C⁻¹ * C) * ((c r)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) r 0) *
              (D (h ω)).1 ((scaleArgs r) p)) := by ring
          _ = _ := by rw [inv_mul_cancel₀ hC.ne', one_mul]
      have key := hT P h hh
      dsimp only at key ⊢
      simp only [hX]
      exact key

end GM

/-- Axiom IV′ from Axiom IV (`r = 1`, GM l. 452–458). -/
theorem IsStrongLQGMetric.translation {D : DistC → ContMetric} {γ : ℝ}
    (hD : IsStrongLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (affineComp 1 z (h ω))).1 (u, v) = (D (h ω)).1 (u + z, v + z) := by
  filter_upwards [hD.coord P h hh 1 one_pos z] with ω hω u v
  have := hω u v
  rw [Real.log_one, mul_zero, GFFLaw.addConst_zero'] at this
  simpa using this.symm

namespace GM

/-- **GM (1.15), Axiom V part** (GM l. 458–465): for a strong metric, with `𝔠_r = r^{ξQ}`,
`𝔠_r⁻¹ e^{−ξ h_r(0)} D_h(r·, r·) = D_{h(r·) − h_r(0)}` a.s. (Axioms IV and III with the constant
`h_r(0) + Q log r`), and `h(r·) − h_r(0)` is a normalized whole-plane GFF, so all these laws
agree (`GFFLaw.map_eq_of_normalized_ae` with `CircleAvg.ae_circleAvg_addConst_one_zero`); one
law is tight and the closure of a singleton is the singleton. The input `hcirc`
(`(h(r·))_1(0) = h_r(0)` a.s.) is leaf (b) `ae_circleAvg_affineComp` (at `z = 0`) of task
P2-FCIRC (`handoff/P2-FCIRC.md`), not yet proved. -/
theorem tightAcrossScales_of_strong {γ : ℝ} {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D)
    (hcirc : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
        ∀ᵐ ω ∂P, circleAvg (affineComp r 0 (h ω)) 1 0 = circleAvg (h ω) r 0) :
    TightAcrossScales (xiGamma γ) D (fun r => r ^ (xiGamma γ * Q γ)) := by
  refine ⟨fun r hr => Real.rpow_pos_of_pos hr _,
    ⟨|xiGamma γ * Q γ| + 2, by linarith [abs_nonneg (xiGamma γ * Q γ)], fun δ hδ r hr => ?_⟩, ?_⟩
  · have hδ0 := hδ.1
    have hδ1 := hδ.2.le
    dsimp only
    rw [Real.mul_rpow hδ0.le hr.le, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hr _).ne']
    have hb1 := le_abs_self (xiGamma γ * Q γ)
    have hb2 := neg_abs_le (xiGamma γ * Q γ)
    set Λ := |xiGamma γ * Q γ| + 2 with hΛ
    have hΛ1 : 1 ≤ Λ := by linarith [abs_nonneg (xiGamma γ * Q γ)]
    have e1 : δ ^ Λ ≤ δ ^ (xiGamma γ * Q γ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
    have e2 : δ ^ (xiGamma γ * Q γ) ≤ δ ^ (-Λ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
    have p1 : 0 ≤ δ ^ Λ := (Real.rpow_pos_of_pos hδ0 _).le
    have p2 : 0 ≤ δ ^ (-Λ) := (Real.rpow_pos_of_pos hδ0 _).le
    have i1 : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ1
    constructor
    · calc Λ⁻¹ * δ ^ Λ ≤ 1 * δ ^ Λ := by gcongr
        _ ≤ _ := by rw [one_mul]; exact e1
    · calc δ ^ (xiGamma γ * Q γ) ≤ 1 * δ ^ (-Λ) := by rw [one_mul]; exact e2
        _ ≤ Λ * δ ^ (-Λ) := by gcongr
  · intro Ω _ P _ h hh X
    let g : ℝ → Ω → DistC := fun r ω => addConst (affineComp r 0 (h ω)) (-(circleAvg (h ω) r 0))
    have hg : ∀ r, 0 < r → IsWholePlaneGFF (g r) P := fun r hr =>
      (hh.affineComp hr 0).addConst ((measurable_circleAvg_left r 0).comp hh.measurable).neg
    have hX : ∀ r, 0 < r → X r =ᵐ[P] fun ω => (D (g r ω)).1 := by
      intro r hr
      filter_upwards [hD.coord P h (isGFFPlusCont_of_isWholePlaneGFF hh) r hr 0,
        hD.ae_dist_addConst (isGFFPlusCont_of_isWholePlaneGFF (hg r hr))] with ω h1 h2
      ext ⟨u, v⟩
      have e1 := h1 u v
      have e2 := h2 (circleAvg (h ω) r 0 + Q γ * Real.log r) u v
      have e3 : addConst (g r ω) (circleAvg (h ω) r 0 + Q γ * Real.log r) =
          addConst (affineComp r 0 (h ω)) (Q γ * Real.log r) := by
        simp only [g, GFFLaw.addConst_addConst]
        congr 1; ring
      rw [e3] at e2
      rw [add_zero, add_zero] at e1
      simp only [X, ContinuousMap.smul_apply, ContinuousMap.comp_apply, smul_eq_mul, scaleArgs,
        ContinuousMap.coe_mk]
      have e4 : (r ^ (xiGamma γ * Q γ))⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) r 0) *
          Real.exp (xiGamma γ * (circleAvg (h ω) r 0 + Q γ * Real.log r)) = 1 := by
        rw [Real.rpow_def_of_pos hr, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
        rw [show -(Real.log r * (xiGamma γ * Q γ)) + -xiGamma γ * circleAvg (h ω) r 0 +
          xiGamma γ * (circleAvg (h ω) r 0 + Q γ * Real.log r) = 0 by ring, Real.exp_zero]
      rw [e1, e2]
      linear_combination (D (g r ω)).1 (u, v) * e4
    have hn : ∀ r, 0 < r → ∀ᵐ ω ∂P, circleAvg (g r ω) 1 0 = 0 := fun r hr => by
      filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero (hh.affineComp hr 0), hcirc P h hh r hr] with ω h1 h2
      simp only [g]
      rw [h1, h2]
      ring
    have hlaw : ∀ r, 0 < r → P.map (g r) = P.map (g 1) := fun r hr =>
      GFFLaw.map_eq_of_normalized_ae (GFFLaw.integral_bumpTest 0 0)
        (measurable_circleAvg_left 1 0) (hg r hr) (hg 1 one_pos) (CircleAvg.ae_circleAvg_addConst_one_zero (hg r hr))
        (CircleAvg.ae_circleAvg_addConst_one_zero (hg 1 one_pos)) (hn r hr) (hn 1 one_pos)
    have hDv : Measurable fun d : DistC => (D d).1 := measurable_subtype_coe.comp hD.measurable
    set μ₀ := P.map (fun ω => (D (g 1 ω)).1) with hμ₀
    have hmap : ∀ r, 0 < r → P.map (X r) = μ₀ := fun r hr => by
      rw [Measure.map_congr (hX r hr)]
      change P.map ((fun d : DistC => (D d).1) ∘ g r) = P.map ((fun d : DistC => (D d).1) ∘ g 1)
      rw [← Measure.map_map hDv (hg r hr).measurable, hlaw r hr,
        Measure.map_map hDv (hg 1 one_pos).measurable]
    have hS : {μ | ∃ r : ℝ, 0 < r ∧ μ = P.map (X r)} = {μ₀} := by
      ext μ
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact hmap r hr
      · rintro rfl
        exact ⟨1, one_pos, (hmap 1 one_pos).symm⟩
    refine ⟨?_, fun μ hμ => ?_⟩
    · rw [hS]
      exact isTightMeasureSet_singleton
    · have hsub : {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) | ∃ r : ℝ, 0 < r ∧
          (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (X r)} ⊆
          {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) | (ν : Measure C(ℂ × ℂ, ℝ)) = μ₀} := by
        rintro ν ⟨r, hr, hν⟩
        exact hν.trans (hmap r hr)
      have hcl : IsClosed {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) |
          (ν : Measure C(ℂ × ℂ, ℝ)) = μ₀} :=
        Set.Subsingleton.isClosed fun ν₁ h₁ ν₂ h₂ =>
          ProbabilityMeasure.toMeasure_injective (h₁.trans h₂.symm)
      have hμ' : (μ : Measure C(ℂ × ℂ, ℝ)) = μ₀ := closure_minimal hsub hcl hμ
      rw [hμ', hμ₀]
      exact (ae_map_iff (μ := P) (f := fun ω => (D (g 1 ω)).1)
        (hDv.comp (hg 1 one_pos).measurable).aemeasurable
        measurableSet_isContinuousMetric).2 (ae_of_all _ fun ω => (D (g 1 ω)).2)

/-- **GM (1.15)** (GM l. 452–465), given the circle-average scaling fact `hcirc` (P2-FCIRC leaf
(b)): a strong
γ-LQG metric is a weak γ-LQG metric with scaling constants `𝔠_r = r^{ξQ}`. -/
theorem gm_eq1_15_of_circleAvg {γ : ℝ} (_hγ : 0 < γ)
    (hcirc : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
        ∀ᵐ ω ∂P, circleAvg (affineComp r 0 (h ω)) 1 0 = circleAvg (h ω) r 0)
    {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D) :
    IsWeakLQGMetric γ D (fun r => r ^ (xiGamma γ * Q γ)) where
  measurable := hD.measurable
  length := hD.length
  locality := hD.locality
  weyl := hD.weyl
  translation P _ h hh z := hD.translation P h hh z
  tightness := tightAcrossScales_of_strong hD hcirc

end GM

end LQGMetric
