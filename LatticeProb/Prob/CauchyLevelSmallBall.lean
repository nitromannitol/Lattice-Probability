import Mathlib
import LatticeProb.Prob.LevelPassageMarkov
import LatticeProb.Prob.BrownianFirstPassageBounds
import LatticeProb.Prob.GaussianFreezing

/-!
# Small-ball bound for the level-passage process at a fixed level

Let `W` be the law on `C(ℝ≥0, ℝ)` of a standard real Brownian motion and let
`ν = (W ⊗ W) ⊗ (W ⊗ W)`. For `a > 0` the level-passage process `Y a = cauchyLevel a` takes the
value of the second path of each pair at the first passage of the first path at `-a`, and subtracts.
Given the first paths, `Y a` is a difference of two independent centred Gaussians, so its density is
at most `1 / √(2π T)`, where `T` is either passage time; averaging the bound `(√T)⁻¹` over the
passage time gives a bound of order `r / a`.

* `hitFrom_neg_toNNReal_eq_firstBelow`: for a continuous path started at `0`, the finite first
  passage time at `-a ≤ 0` is the first time at which the path is at most `-a`.
* `hitFrom_neg_toNNReal_ne_zero`: for `a > 0` that passage time is positive.
* `pathLaw_eval_mem_Icc_le`: the Gaussian bound for the one-dimensional marginal of `W`.
* `lintegral_inv_sqrt_hitFrom_neg_le`: `∫ (√T_a)⁻¹ dW ≤ 4 / a`.
* `measure_abs_cauchyLevel_le`: `ν {|Y a| ≤ r} ≤ (2 r / √(2π)) (4 / a)`.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

noncomputable section

/-- For a continuous path `w` with `w 0 = 0` and a finite first passage at `-a ≤ 0`, the passage
time is the first time `t ≥ 0` at which the extension `t ↦ w (t⁺)` is at most `-a`. -/
theorem hitFrom_neg_toNNReal_eq_firstBelow {w : C(ℝ≥0, ℝ)} (hw0 : w 0 = 0) {a : ℝ}
    (ha : 0 ≤ a) (hT : hitFrom (-a) 0 (w : ℝ≥0 → ℝ) ≠ ⊤) :
    ((hitFrom (-a) 0 (w : ℝ≥0 → ℝ)).toNNReal : ℝ) =
      firstBelow (fun t : ℝ => w t.toNNReal) 0 (-a) := by
  obtain ⟨s, hs, -, hws, -⟩ := exists_hitFrom_eq w.continuous hT
  have hf : Continuous fun t : ℝ => w t.toNNReal := w.continuous.comp continuous_real_toNNReal
  have hws' : (fun t : ℝ => w t.toNNReal) (s : ℝ) ≤ -a := by
    show w (s : ℝ).toNNReal ≤ -a
    rw [Real.toNNReal_coe, hws]
  have hsb : ∃ b, (0 : ℝ) ≤ b ∧ (fun t : ℝ => w t.toNNReal) b ≤ -a :=
    ⟨s, NNReal.coe_nonneg s, hws'⟩
  rw [hs, ENNReal.toNNReal_coe]
  refine le_antisymm ?_ (firstBelow_le (f := fun t : ℝ => w t.toNNReal) (NNReal.coe_nonneg s) hws')
  obtain ⟨hu0, hu⟩ := firstBelow_mem hf hsb
  have hIcc : -a ∈ Icc ((fun t : ℝ => w t.toNNReal) (firstBelow (fun t : ℝ => w t.toNNReal) 0 (-a)))
      ((fun t : ℝ => w t.toNNReal) 0) := by
    refine ⟨hu, ?_⟩
    show -a ≤ w (0 : ℝ).toNNReal
    rw [Real.toNNReal_zero, hw0]
    linarith
  obtain ⟨u', hu', hwu'⟩ := Set.mem_of_mem_of_subset hIcc (intermediate_value_Icc' hu0 hf.continuousOn)
  have hle : hitFrom (-a) 0 (w : ℝ≥0 → ℝ) ≤ u'.toNNReal :=
    hitFrom_le (w := (w : ℝ≥0 → ℝ)) zero_le hwu'
  rw [hs, ENNReal.coe_le_coe] at hle
  calc (s : ℝ) ≤ u'.toNNReal := NNReal.coe_le_coe.2 hle
    _ = u' := Real.coe_toNNReal _ hu'.1
    _ ≤ firstBelow (fun t : ℝ => w t.toNNReal) 0 (-a) := hu'.2

/-- For a continuous path `w` with `w 0 = 0` and a finite first passage at `-a < 0`, the passage
time is positive. -/
theorem hitFrom_neg_toNNReal_ne_zero {w : C(ℝ≥0, ℝ)} (hw0 : w 0 = 0) {a : ℝ} (ha : 0 < a)
    (hT : hitFrom (-a) 0 (w : ℝ≥0 → ℝ) ≠ ⊤) : (hitFrom (-a) 0 (w : ℝ≥0 → ℝ)).toNNReal ≠ 0 := by
  obtain ⟨s, hs, -, hws, -⟩ := exists_hitFrom_eq w.continuous hT
  rw [hs, ENNReal.toNNReal_coe]
  rintro rfl
  rw [hw0] at hws
  linarith

section PathLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- Under the Brownian path law, the value at a time `t > 0` lies in `[c, d]` with probability at
most `(d - c) / √(2π t)`. -/
theorem pathLaw_eval_mem_Icc_le (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {t : ℝ≥0} (ht : t ≠ 0) {c d : ℝ} (hcd : c ≤ d) :
    (P.map (pathMap B hcont)) {v : C(ℝ≥0, ℝ) | v t ∈ Icc c d} ≤
      ENNReal.ofReal ((d - c) / √(2 * Real.pi * t)) := by
  have hS : MeasurableSet {v : C(ℝ≥0, ℝ) | v t ∈ Icc c d} :=
    (continuous_eval_const t).measurable measurableSet_Icc
  calc (P.map (pathMap B hcont)) {v : C(ℝ≥0, ℝ) | v t ∈ Icc c d}
      = P (B t ⁻¹' Icc c d) := Measure.map_apply (measurable_pathMap B hm hcont) hS
    _ = (P.map (B t)) (Icc c d) := (Measure.map_apply (hm t) measurableSet_Icc).symm
    _ = gaussianReal 0 t (Icc c d) := by rw [(hB.toIsPreBrownianReal.hasLaw_eval t).map_eq]
    _ ≤ _ := gaussianReal_Icc_le ht hcd

/-- Under the Brownian path law, the inverse square root of the first passage time at `-a < 0`
has mean at most `4 / a`. -/
theorem lintegral_inv_sqrt_hitFrom_neg_le (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {a : ℝ} (ha : 0 < a) :
    ∫⁻ w, ENNReal.ofReal (√((hitFrom (-a) 0 (w : ℝ≥0 → ℝ)).toNNReal : ℝ))⁻¹
        ∂(P.map (pathMap B hcont)) ≤ ENNReal.ofReal (4 / a) := by
  have hpm := measurable_pathMap B hm hcont
  have hg : Measurable fun w : C(ℝ≥0, ℝ) =>
      ENNReal.ofReal (√((hitFrom (-a) 0 (w : ℝ≥0 → ℝ)).toNNReal : ℝ))⁻¹ :=
    ENNReal.measurable_ofReal.comp
      ((measurable_hitFrom (r := fun _ => 0) measurable_const (-a)).ennreal_toReal.sqrt.inv)
  rw [lintegral_map hg hpm]
  have hXB : (fun (t : ℝ≥0) ω => B ((t : ℝ).toNNReal) ω) = B := by
    funext t ω
    rw [Real.toNNReal_coe]
  have hB' : IsBrownianReal (fun (t : ℝ≥0) ω => B ((t : ℝ).toNNReal) ω) P := by
    rw [hXB]
    exact hB
  have hm' : ∀ t : ℝ≥0, Measurable fun ω => B ((t : ℝ).toNNReal) ω := by
    intro t
    rw [Real.toNNReal_coe]
    exact hm t
  have hcont' : ∀ ω, Continuous fun s : ℝ => B s.toNNReal ω :=
    fun ω => (hcont ω).comp continuous_real_toNNReal
  refine le_trans (le_of_eq (lintegral_congr_ae ?_))
    (lintegral_inv_sqrt_firstBelow_le (X := fun ω (s : ℝ) => B s.toNNReal ω) hB' hm' hcont' ha)
  filter_upwards [ae_of_ae_map hpm.aemeasurable (ae_hitFrom_neg_ne_top_pathLaw hB hm hcont)]
    with ω hω
  simp only [hitFrom_neg_toNNReal_eq_firstBelow hω.1 ha.le (hω.2 a ha.le), pathMap_apply]

/-- **Small-ball bound for the level-passage process at a fixed level.** Under
`ν = (W ⊗ W) ⊗ (W ⊗ W)`, for `a > 0` and `r ≥ 0`,
`ν {|Y a| ≤ r} ≤ (2 r / √(2π)) (4 / a)`, where `Y = cauchyLevel`. -/
theorem measure_abs_cauchyLevel_le (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 ≤ r) :
    (((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
        ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))))
        {q | |cauchyLevel a q| ≤ r} ≤
      ENNReal.ofReal (2 * r / √(2 * Real.pi)) * ENNReal.ofReal (4 / a) := by
  set W := P.map (pathMap B hcont)
  have : IsProbabilityMeasure W :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pathMap B hm hcont).aemeasurable).2
      inferInstance
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hS : MeasurableSet
      {q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) | |cauchyLevel a q| ≤ r} :=
    measurableSet_le (continuous_abs.measurable.comp (measurable_cauchyLevel a)) measurable_const
  have hinner : ∀ p₁ : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ),
      (W.prod W) (Prod.mk p₁ ⁻¹' {q | |cauchyLevel a q| ≤ r}) ≤
        ENNReal.ofReal (2 * r / √(2 * Real.pi)) * ENNReal.ofReal (4 / a) := by
    intro p₁
    have hS₁ : MeasurableSet {p₂ : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) |
        passageValue a p₂ ∈ Icc (passageValue a p₁ - r) (passageValue a p₁ + r)} :=
      measurable_passageValue a measurableSet_Icc
    have hsub : Prod.mk p₁ ⁻¹' {q | |cauchyLevel a q| ≤ r} = {p₂ : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) |
        passageValue a p₂ ∈ Icc (passageValue a p₁ - r) (passageValue a p₁ + r)} := by
      ext p₂
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, cauchyLevel, Set.mem_Icc, abs_le]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [hsub, Measure.prod_apply hS₁]
    calc ∫⁻ l, W (Prod.mk l ⁻¹' {p₂ : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) |
          passageValue a p₂ ∈ Icc (passageValue a p₁ - r) (passageValue a p₁ + r)}) ∂W
        ≤ ∫⁻ l, ENNReal.ofReal (2 * r / √(2 * Real.pi)) *
            ENNReal.ofReal (√((hitFrom (-a) 0 (l : ℝ≥0 → ℝ)).toNNReal : ℝ))⁻¹ ∂W := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_hitFrom_neg_ne_top_pathLaw hB hm hcont] with l hl
          have ht := hitFrom_neg_toNNReal_ne_zero hl.1 ha (hl.2 a ha.le)
          have hpre : Prod.mk l ⁻¹' {p₂ : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) |
              passageValue a p₂ ∈ Icc (passageValue a p₁ - r) (passageValue a p₁ + r)} =
              {v : C(ℝ≥0, ℝ) | v (hitFrom (-a) 0 (l : ℝ≥0 → ℝ)).toNNReal ∈
                Icc (passageValue a p₁ - r) (passageValue a p₁ + r)} := rfl
          rw [hpre]
          refine (pathLaw_eval_mem_Icc_le hB hm hcont ht (by linarith)).trans (le_of_eq ?_)
          rw [← ENNReal.ofReal_mul (p := 2 * r / √(2 * Real.pi)) (by positivity)]
          congr 1
          have e : passageValue a p₁ + r - (passageValue a p₁ - r) = 2 * r := by ring
          rw [e, Real.sqrt_mul h2π, div_mul_eq_div_div,
            div_eq_mul_inv (2 * r / √(2 * Real.pi))]
      _ = ENNReal.ofReal (2 * r / √(2 * Real.pi)) *
            ∫⁻ l, ENNReal.ofReal (√((hitFrom (-a) 0 (l : ℝ≥0 → ℝ)).toNNReal : ℝ))⁻¹ ∂W :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * r / √(2 * Real.pi)) * ENNReal.ofReal (4 / a) := by
          gcongr _ * ?_
          exact lintegral_inv_sqrt_hitFrom_neg_le hB hm hcont ha
  calc _ = ∫⁻ p₁, (W.prod W) (Prod.mk p₁ ⁻¹' {q | |cauchyLevel a q| ≤ r}) ∂(W.prod W) :=
        Measure.prod_apply hS
    _ ≤ ∫⁻ _p₁, ENNReal.ofReal (2 * r / √(2 * Real.pi)) * ENNReal.ofReal (4 / a) ∂(W.prod W) :=
        lintegral_mono hinner
    _ = ENNReal.ofReal (2 * r / √(2 * Real.pi)) * ENNReal.ofReal (4 / a) := by
        rw [lintegral_const, measure_univ, mul_one]

end PathLaw

end

end LatticeProb
