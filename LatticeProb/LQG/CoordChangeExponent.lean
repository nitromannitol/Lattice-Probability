import LatticeProb.Bonanno.LQGMetric.Assembly.MainFinal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Eq115
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Asm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperFinal
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3Wire3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L37Q1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P16D3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53W1

/-!
# The coordinate-change exponent of an LQG metric is determined by its Weyl exponent

Let `γ ∈ (0, 2)` and `ξ = γ / d_γ`. Let `D : h ↦ D_h` be a measurable map from distributions to
continuous metrics on `ℂ` which, for every whole-plane GFF plus a continuous function `h`, satisfies
Axioms I-III of Gwynne-Miller (*Existence and uniqueness of the Liouville quantum gravity metric for
γ ∈ (0, 2)*, arXiv:1905.00383, Section 1.2) with Weyl exponent `ξ`, together with the coordinate change
formula `D_h(r u + z, r v + z) = D_{h(r · + z) + Q' log r}(u, v)` for some exponent `Q'`. Then
`Q' = Q = 2/γ + γ/2` (`coordExponent_eq_Q`).

As in Gwynne-Miller (1.15), the coordinate change formula makes `D` a weak γ-LQG metric with scaling
constants `𝔠_r = r^{ξ Q'}` (`isWeakLQGMetric_rpow_of_coord`): by Weyl scaling with the constant
`h_r(0) + Q' log r`, `𝔠_r⁻¹ e^{-ξ h_r(0)} D_h(r ·, r ·) = D_{h(r ·) - h_r(0)}`, whose law does not depend
on `r`. By Dubédat-Falconet-Gwynne-Pfeffer-Sun (*Weak LQG metrics and Liouville first passage
percolation*, arXiv:1905.00380, Theorem 1.5), the scaling constants of every weak γ-LQG metric satisfy
`𝔠_{δ r} / 𝔠_r = δ^{ξ Q + o_δ(1)}` (`dfgpsScaling_holds`), so `ξ Q' = ξ Q`.

Since `γ ↦ 2/γ + γ/2` is injective on `(0, 2)` (`eq_of_Q_eq`), the pair `(ξ, Q)` of exponents of an
LQG metric determines `γ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LatticeProb.LQG

/-- **Dubédat-Falconet-Gwynne-Pfeffer-Sun, Theorem 1.5** (arXiv:1905.00380, p. 7): for `γ ∈ (0, 2)`, the
scaling constants of every weak γ-LQG metric satisfy `𝔠_{δ r} / 𝔠_r = δ^{ξ Q + o_δ(1)}` as `δ → 0`,
uniformly in `r > 0`. Assembled from the Ding-Gwynne and Ding-Zeitouni-Zhang estimates of the library. -/
theorem dfgpsScaling_holds : LQGMetric.Blueprint.DFGPSScaling :=
  have hD : LQGMetric.DG.DZZInputsDGForm := LQGMetric.DG.dzzInputsDGForm_of
    (LQGMetric.DZZ.dzzInputsDG_of_exp
      (LQGMetric.DZZ.dzzLem53ExpAll_of_hbadB LQGMetric.l53HbadBAll_proved))
  LQGMetric.DFGPS.dfgpsScaling_of_lem3_6 LQGMetric.LM.lmLem3_1a
    (LQGMetric.DFGPS.L36.lem3_6_of_DG
      (LQGMetric.DG.wire_dgThm1_5KU_of LQGMetric.DG.L37Q.dgLem3_7
        (LQGMetric.DG.dgProp3_16_of_lem37 LQGMetric.DG.L37Q.dgLem3_7) hD)
      (LQGMetric.DG.wire_dgProp3_21_of LQGMetric.DG.L37Q.dgLem3_7 hD))

/-- **Axiom V from a coordinate change with exponent `Q'`** (as in Gwynne-Miller (1.15)): if `D` satisfies
the length and Weyl scaling axioms with Weyl exponent `ξ = γ / d_γ` and the coordinate change formula with
exponent `Q'`, then `D` is tight across scales with scaling constants `𝔠_r = r^{ξ Q'}`. -/
theorem tightAcrossScales_rpow_of_coord {γ Q' : ℝ} {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hm : Measurable D)
    (hlen : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLength)
    (hweyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), ∀ z w : ℂ,
        LQGMetric.weylScale (LQGMetric.xiGamma γ) f (D (h ω)) z w =
          ENNReal.ofReal ((D (LQGMetric.addFun (h ω) f)).1 (z, w)))
    (hcoord : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (r * u + z, r * v + z) =
          (D (LQGMetric.addConst (LQGMetric.affineComp r z (h ω)) (Q' * Real.log r))).1 (u, v)) :
    LQGMetric.TightAcrossScales (LQGMetric.xiGamma γ) D
      (fun r => r ^ (LQGMetric.xiGamma γ * Q')) := by
  refine LQGMetric.GM.tightAcrossScales_of_ae_eq hm (fun r hr => Real.rpow_pos_of_pos hr _)
    (LQGMetric.GM.rpow_ratio_bounds _) ?_
  intro Ω _ P _ h hh r hr
  have hg : LQGMetric.IsWholePlaneGFF (fun ω => LQGMetric.addConst
      (LQGMetric.affineComp r 0 (h ω)) (-(LQGMetric.circleAvg (h ω) r 0))) P :=
    (hh.affineComp hr 0).addConst
      ((LQGMetric.measurable_circleAvg_left r 0).comp hh.measurable).neg
  have hgc := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hg
  filter_upwards [hcoord P h (LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh) r hr 0,
    hlen P _ hgc, hweyl P _ hgc] with ω h1 hl hw
  ext ⟨u, v⟩
  have e1 := h1 u v
  have e2 := LQGMetric.dist_addConst_of_weyl hl hw
    (LQGMetric.circleAvg (h ω) r 0 + Q' * Real.log r) u v
  have e3 : LQGMetric.addConst (LQGMetric.addConst (LQGMetric.affineComp r 0 (h ω))
      (-(LQGMetric.circleAvg (h ω) r 0))) (LQGMetric.circleAvg (h ω) r 0 + Q' * Real.log r) =
      LQGMetric.addConst (LQGMetric.affineComp r 0 (h ω)) (Q' * Real.log r) := by
    rw [LQGMetric.GFFLaw.addConst_addConst]
    congr 1
    ring
  rw [e3] at e2
  rw [add_zero, add_zero] at e1
  simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, smul_eq_mul,
    LQGMetric.scaleArgs, ContinuousMap.coe_mk]
  have e4 : (r ^ (LQGMetric.xiGamma γ * Q'))⁻¹ *
      Real.exp (-LQGMetric.xiGamma γ * LQGMetric.circleAvg (h ω) r 0) *
      Real.exp (LQGMetric.xiGamma γ * (LQGMetric.circleAvg (h ω) r 0 + Q' * Real.log r)) = 1 := by
    rw [Real.rpow_def_of_pos hr, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    rw [show -(Real.log r * (LQGMetric.xiGamma γ * Q')) +
        -LQGMetric.xiGamma γ * LQGMetric.circleAvg (h ω) r 0 +
        LQGMetric.xiGamma γ * (LQGMetric.circleAvg (h ω) r 0 + Q' * Real.log r) = 0 by ring,
      Real.exp_zero]
  rw [e1, e2]
  linear_combination
    (D (LQGMetric.addConst (LQGMetric.affineComp r 0 (h ω))
      (-(LQGMetric.circleAvg (h ω) r 0)))).1 (u, v) * e4

/-- **A metric with a coordinate change of exponent `Q'` is a weak LQG metric** with scaling constants
`𝔠_r = r^{ξ Q'}` (Gwynne-Miller (1.15), with `Q'` in place of `Q`): Axioms I-III with Weyl exponent
`ξ = γ / d_γ`, translation invariance (the coordinate change at `r = 1`) and tightness across scales
(`tightAcrossScales_rpow_of_coord`). -/
theorem isWeakLQGMetric_rpow_of_coord {γ Q' : ℝ} {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hm : Measurable D)
    (hlen : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLength)
    (hloc : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
        ∃ F : LQGMetric.DistOn U → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
          ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
            (D (h ω)).internal U z w = F (LQGMetric.restrictTo U (h ω)) z w)
    (hweyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), ∀ z w : ℂ,
        LQGMetric.weylScale (LQGMetric.xiGamma γ) f (D (h ω)) z w =
          ENNReal.ofReal ((D (LQGMetric.addFun (h ω) f)).1 (z, w)))
    (hcoord : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (r * u + z, r * v + z) =
          (D (LQGMetric.addConst (LQGMetric.affineComp r z (h ω)) (Q' * Real.log r))).1 (u, v)) :
    LQGMetric.IsWeakLQGMetric γ D (fun r => r ^ (LQGMetric.xiGamma γ * Q')) where
  measurable := hm
  length := hlen
  locality := hloc
  weyl := hweyl
  translation := by
    intro Ω _ P _ h hh z
    filter_upwards [hcoord P h hh 1 one_pos z] with ω hω u v
    have := hω u v
    rw [Real.log_one, mul_zero, LQGMetric.GFFLaw.addConst_zero'] at this
    simpa using this.symm
  tightness := tightAcrossScales_rpow_of_coord hm hlen hweyl hcoord

/-- **The coordinate-change exponent is `Q = 2/γ + γ/2`.** For `γ ∈ (0, 2)`, a measurable map from
distributions to continuous metrics satisfying Axioms I-III with Weyl exponent `ξ = γ / d_γ` and the
coordinate change formula with exponent `Q'` has `Q' = Q` (Gwynne-Miller (1.15) and
Dubédat-Falconet-Gwynne-Pfeffer-Sun, Theorem 1.5). -/
theorem coordExponent_eq_Q {γ Q' : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hm : Measurable D)
    (hlen : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLength)
    (hloc : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
        ∃ F : LQGMetric.DistOn U → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
          ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
            (D (h ω)).internal U z w = F (LQGMetric.restrictTo U (h ω)) z w)
    (hweyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), ∀ z w : ℂ,
        LQGMetric.weylScale (LQGMetric.xiGamma γ) f (D (h ω)) z w =
          ENNReal.ofReal ((D (LQGMetric.addFun (h ω) f)).1 (z, w)))
    (hcoord : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (r * u + z, r * v + z) =
          (D (LQGMetric.addConst (LQGMetric.affineComp r z (h ω)) (Q' * Real.log r))).1 (u, v)) :
    Q' = LQGMetric.Q γ := by
  have hW := isWeakLQGMetric_rpow_of_coord hm hlen hloc hweyl hcoord
  have hξ : 0 < LQGMetric.xiGamma γ := LQGMetric.GM.xiGamma_pos hγ
  suffices hab : LQGMetric.xiGamma γ * Q' = LQGMetric.xiGamma γ * LQGMetric.Q γ from
    mul_left_cancel₀ hξ.ne' hab
  set a := LQGMetric.xiGamma γ * LQGMetric.Q γ with ha
  set b := LQGMetric.xiGamma γ * Q' with hb
  by_contra hne
  have hζ : 0 < |a - b| / 2 := by
    have := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
    linarith
  obtain ⟨δ₀, hδ₀, hS⟩ := dfgpsScaling_holds γ hγ hγ2 D _ hW (|a - b| / 2) hζ
  have hδ0 : 0 < min (δ₀ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have hδ1 : min (δ₀ / 2) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδδ₀ : min (δ₀ / 2) (1 / 2) < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨h1, h2⟩ := hS (min (δ₀ / 2) (1 / 2)) ⟨hδ0, hδδ₀⟩ 1 one_pos
  simp only [mul_one, Real.one_rpow, div_one] at h1 h2
  rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hδ0 hδ1] at h1 h2
  have : |a - b| ≤ |a - b| / 2 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  linarith

/-- `γ ↦ Q = 2/γ + γ/2` is injective on `(0, 2)`. -/
theorem eq_of_Q_eq {γ γ' : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hγ' : 0 < γ') (hγ2' : γ' < 2)
    (h : LQGMetric.Q γ = LQGMetric.Q γ') : γ = γ' := by
  have e : LQGMetric.Q γ - LQGMetric.Q γ' = (γ' - γ) * (4 - γ * γ') / (2 * γ * γ') := by
    unfold LQGMetric.Q
    field_simp
    ring
  rw [h, sub_self, eq_comm, div_eq_zero_iff] at e
  have hprod : 0 < 4 - γ * γ' := by nlinarith
  rcases e with e | e
  · rcases mul_eq_zero.1 e with e | e
    · linarith
    · linarith
  · have : 0 < 2 * γ * γ' := by positivity
    linarith

end LatticeProb.LQG
