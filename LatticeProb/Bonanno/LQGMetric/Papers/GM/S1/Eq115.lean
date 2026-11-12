/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S1.Eq115 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.StrongWeak
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine

/-!
# GM (1.15): a strong γ-LQG metric is weak with `𝔠_r = r^{ξQ}`

Source: Gwynne–Miller, arXiv:1905.00383v3 (GM), `literature/src/1905.00383/uniqueness-final.tex`
l. 452–465 ((1.15)). `gm_eq1_15_of_circleAvg` (P2-M1A, `StrongWeak.lean`) with its circle-average
input `(h(r·))_1(0) = h_r(0)` a.s. discharged by `CircleAvg.ae_circleAvg_affineComp` (P2-FCIRC).

`rpow_ratio_bounds`, `tightAcrossScales_of_ae_eq`: the same argument for constants `𝔠_r = r^β`
with the normalized fields given a.s. as `D_{h(r·) − h_r(0)}` (input of GM.S1.12, l. 520–529,
in `WeakStrong.lean`); copied and generalized from `tightAcrossScales_of_strong` (P2-M1A).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric
namespace GM

/-- **GM (1.15)** (GM l. 452–465): a strong γ-LQG metric is a weak γ-LQG metric with scaling
constants `𝔠_r = r^{ξQ}`. -/
theorem gm_eq1_15 {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D) :
    IsWeakLQGMetric γ D (fun r => r ^ (xiGamma γ * Q γ)) :=
  gm_eq1_15_of_circleAvg hγ (fun _ _ _ hh _ hr => CircleAvg.ae_circleAvg_affineComp hh hr 0) hD

/-! ### The (1.15) argument for constants `𝔠_r = r^β` (used by GM.S1.12, l. 520–529) -/

/-- the ratio bounds of Axiom V for `𝔠_r = r^β` (`Λ = |β| + 2`) -/
lemma rpow_ratio_bounds (β : ℝ) : ∃ Λ : ℝ, 1 < Λ ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
    Λ⁻¹ * δ ^ Λ ≤ (δ * r) ^ β / r ^ β ∧ (δ * r) ^ β / r ^ β ≤ Λ * δ ^ (-Λ) := by
  refine ⟨|β| + 2, by linarith [abs_nonneg β], fun δ hδ r hr => ?_⟩
  rw [Real.mul_rpow hδ.1.le hr.le, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hr _).ne']
  have hΛ1 : 1 ≤ |β| + 2 := by linarith [abs_nonneg β]
  have e1 : δ ^ (|β| + 2) ≤ δ ^ β :=
    Real.rpow_le_rpow_of_exponent_ge hδ.1 hδ.2.le (by linarith [le_abs_self β])
  have e2 : δ ^ β ≤ δ ^ (-(|β| + 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ.1 hδ.2.le (by linarith [neg_abs_le β])
  have p1 : 0 ≤ δ ^ (|β| + 2) := (Real.rpow_pos_of_pos hδ.1 _).le
  have p2 : 0 ≤ δ ^ (-(|β| + 2)) := (Real.rpow_pos_of_pos hδ.1 _).le
  constructor
  · calc (|β| + 2)⁻¹ * δ ^ (|β| + 2) ≤ 1 * δ ^ (|β| + 2) := by
          gcongr; exact inv_le_one_of_one_le₀ hΛ1
      _ ≤ _ := by rw [one_mul]; exact e1
  · calc δ ^ β ≤ 1 * δ ^ (-(|β| + 2)) := by rw [one_mul]; exact e2
      _ ≤ _ := by gcongr

/-- Axiom V when the normalized fields are a.s. `D_{h(r·) − h_r(0)}` (GM l. 523–529): all these
laws equal the law of `D_h` for a normalized GFF (P2-M1A's argument for (1.15)). -/
theorem tightAcrossScales_of_ae_eq {ξ : ℝ} {D : DistC → ContMetric} (hDm : Measurable D)
    {c : ℝ → ℝ} (hpos : ∀ r, 0 < r → 0 < c r)
    (hrat : ∃ Λ : ℝ, 1 < Λ ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
      Λ⁻¹ * δ ^ Λ ≤ c (δ * r) / c r ∧ c (δ * r) / c r ≤ Λ * δ ^ (-Λ))
    (hX : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r, 0 < r →
      (fun ω => ((c r)⁻¹ * Real.exp (-ξ * circleAvg (h ω) r 0)) • (D (h ω)).1.comp (scaleArgs r))
        =ᵐ[P] fun ω => (D (addConst (affineComp r 0 (h ω)) (-(circleAvg (h ω) r 0)))).1) :
    TightAcrossScales ξ D c := by
  refine ⟨hpos, hrat, ?_⟩
  intro Ω _ P _ h hh X
  let g : ℝ → Ω → DistC := fun r ω => addConst (affineComp r 0 (h ω)) (-(circleAvg (h ω) r 0))
  have hg : ∀ r, 0 < r → IsWholePlaneGFF (g r) P := fun r hr =>
    (hh.affineComp hr 0).addConst ((measurable_circleAvg_left r 0).comp hh.measurable).neg
  have hn : ∀ r, 0 < r → ∀ᵐ ω ∂P, circleAvg (g r ω) 1 0 = 0 := fun r hr => by
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero (hh.affineComp hr 0),
      CircleAvg.ae_circleAvg_affineComp hh hr 0] with ω h1 h2
    simp only [g]
    rw [h1, h2]
    ring
  have hlaw : ∀ r, 0 < r → P.map (g r) = P.map (g 1) := fun r hr =>
    GFFLaw.map_eq_of_normalized_ae (GFFLaw.integral_bumpTest 0 0)
      (measurable_circleAvg_left 1 0) (hg r hr) (hg 1 one_pos)
      (CircleAvg.ae_circleAvg_addConst_one_zero (hg r hr))
      (CircleAvg.ae_circleAvg_addConst_one_zero (hg 1 one_pos)) (hn r hr) (hn 1 one_pos)
  have hDv : Measurable fun d : DistC => (D d).1 := measurable_subtype_coe.comp hDm
  set μ₀ := P.map (fun ω => (D (g 1 ω)).1) with hμ₀
  have hmap : ∀ r, 0 < r → P.map (X r) = μ₀ := fun r hr => by
    rw [Measure.map_congr (hX P h hh r hr)]
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
    rw [closure_minimal hsub hcl hμ, hμ₀]
    exact (ae_map_iff (μ := P) (f := fun ω => (D (g 1 ω)).1)
      (hDv.comp (hg 1 one_pos).measurable).aemeasurable
      measurableSet_isContinuousMetric).2 (ae_of_all _ fun ω => (D (g 1 ω)).2)

end GM
end LQGMetric
