import Mathlib
import LatticeProb.Prob.CauchyLevelSmallBall
import LatticeProb.Prob.GaussianSmallBall

/-!
# Lower small-ball bound for the level-passage process at a fixed level

Let `W` be the law on `C(ℝ≥0, ℝ)` of a standard real Brownian motion and let
`ν = (W ⊗ W) ⊗ (W ⊗ W)`, the law of two independent pairs `((l₁, r₁), (l₂, r₂))` of independent
Brownian paths. With `Tᵢ` the first passage time of `lᵢ` at `-a`, the level-passage process is
`Y a = r₂ (T₂) - r₁ (T₁)`. Given the first paths, `Y a` is centred Gaussian with variance `T₁ + T₂`.

* `pathLaw_map_eval`: the one-dimensional marginals of `W` are `gaussianReal 0 t`.
* `pathLaw_prod_map_sub_eval`: under `W ⊗ W`, `p.2 t - p.1 s` has law `gaussianReal 0 (s + t)`.
* `measure_abs_cauchyLevel_le_eq_lintegral`: `ν {|Y a| ≤ r}` is the `W ⊗ W`-average over the first
  paths of `gaussianReal 0 (T₁ + T₂) [-r, r]`.
* `gaussianReal_Iic_neg_one_le_pathLaw_hitFrom_neg_le`: `W {T_a ≤ a²} ≥ P(N(0,1) ≤ -1)`.
* `le_measure_abs_cauchyLevel_le`: for `a > 0` and `r ≥ 0`,
  `ν {|Y a| ≤ r} ≥ c₀ min 1 (r / (√2 a)) P(N(0,1) ≤ -1)²`, `c₀ = 2 e^{-1/2} / √(2π)`.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

noncomputable section

section PathLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- The one-dimensional marginals of the Brownian path law. -/
theorem pathLaw_map_eval (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (t : ℝ≥0) :
    (P.map (pathMap B hcont)).map (fun v : C(ℝ≥0, ℝ) => v t) = gaussianReal 0 t := by
  rw [Measure.map_map (continuous_eval_const t).measurable (measurable_pathMap B hm hcont)]
  exact (hB.toIsPreBrownianReal.hasLaw_eval t).map_eq

/-- Under the product of two Brownian path laws, the difference of the values of the two paths at
times `t` and `s` is centred Gaussian with variance `s + t`. -/
theorem pathLaw_prod_map_sub_eval (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (s t : ℝ≥0) :
    ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).map
        (fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => p.2 t - p.1 s) = gaussianReal 0 (s + t) := by
  have : IsProbabilityMeasure (P.map (pathMap B hcont)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pathMap B hm hcont).aemeasurable).2
      inferInstance
  have hs : Measurable fun v : C(ℝ≥0, ℝ) => -(v s) := (continuous_eval_const s).measurable.neg
  have ht : Measurable fun v : C(ℝ≥0, ℝ) => v t := (continuous_eval_const t).measurable
  have hWs : (P.map (pathMap B hcont)).map (fun v : C(ℝ≥0, ℝ) => -(v s)) = gaussianReal 0 s := by
    have hcomp : (fun v : C(ℝ≥0, ℝ) => -(v s)) =
        (fun x : ℝ => -x) ∘ (fun v : C(ℝ≥0, ℝ) => v s) := rfl
    rw [hcomp, ← Measure.map_map measurable_neg (continuous_eval_const s).measurable,
      pathLaw_map_eval hB hm hcont s, gaussianReal_map_neg, neg_zero]
  have hfun : (fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => p.2 t - p.1 s) =
      (fun x : ℝ × ℝ => x.1 + x.2) ∘
        Prod.map (fun v : C(ℝ≥0, ℝ) => -(v s)) (fun v : C(ℝ≥0, ℝ) => v t) := by
    funext p
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
    ring
  rw [hfun, ← Measure.map_map measurable_add (hs.prodMap ht), ← Measure.map_prod_map _ _ hs ht,
    hWs, pathLaw_map_eval hB hm hcont t]
  have hconv : ((gaussianReal 0 s).prod (gaussianReal 0 t)).map (fun x : ℝ × ℝ => x.1 + x.2) =
      gaussianReal 0 s ∗ gaussianReal 0 t := rfl
  rw [hconv, gaussianReal_conv_gaussianReal, add_zero]

/-- **Conditional Gaussian law of the level-passage process.** Under `ν = (W ⊗ W) ⊗ (W ⊗ W)`,
the probability that `|Y a| ≤ r` is the average over the two first paths of the mass of
`[-r, r]` under the centred Gaussian law whose variance is the sum of the two passage times. -/
theorem measure_abs_cauchyLevel_le_eq_lintegral (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (a r : ℝ) :
    (((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
        ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))))
        {q | |cauchyLevel a q| ≤ r} =
      ∫⁻ l₁, ∫⁻ l₂, gaussianReal 0 ((hitFrom (-a) 0 (l₁ : ℝ≥0 → ℝ)).toNNReal +
          (hitFrom (-a) 0 (l₂ : ℝ≥0 → ℝ)).toNNReal) (Icc (-r) r)
        ∂(P.map (pathMap B hcont)) ∂(P.map (pathMap B hcont)) := by
  set W := P.map (pathMap B hcont)
  have : IsProbabilityMeasure W :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pathMap B hm hcont).aemeasurable).2
      inferInstance
  set S := {q : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) | |cauchyLevel a q| ≤ r}
    with hSdef
  have hS : MeasurableSet S :=
    measurableSet_le (continuous_abs.measurable.comp (measurable_cauchyLevel a)) measurable_const
  rw [Measure.prod_apply hS, lintegral_prod _ (measurable_measure_prodMk_left hS).aemeasurable]
  refine lintegral_congr fun l₁ => ?_
  have hg₃ : Measurable fun x : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × C(ℝ≥0, ℝ) =>
      ((l₁, x.1.1), (x.1.2, x.2)) := by fun_prop
  have hS₃ : MeasurableSet {x : (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × C(ℝ≥0, ℝ) |
      ((l₁, x.1.1), (x.1.2, x.2)) ∈ S} := hg₃ hS
  calc ∫⁻ r₁, (W.prod W) (Prod.mk (l₁, r₁) ⁻¹' S) ∂W
      = ∫⁻ r₁, ∫⁻ l₂, W {r₂ | ((l₁, r₁), (l₂, r₂)) ∈ S} ∂W ∂W :=
        lintegral_congr fun r₁ => Measure.prod_apply (measurable_prodMk_left hS)
    _ = ∫⁻ l₂, ∫⁻ r₁, W {r₂ | ((l₁, r₁), (l₂, r₂)) ∈ S} ∂W ∂W :=
        lintegral_lintegral_swap (f := fun r₁ l₂ => W {r₂ | ((l₁, r₁), (l₂, r₂)) ∈ S})
          (measurable_measure_prodMk_left hS₃).aemeasurable
    _ = _ := by
        refine lintegral_congr fun l₂ => ?_
        have hg₂ : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => ((l₁, p.1), (l₂, p.2)) := by
          fun_prop
        have hS₂ : MeasurableSet {p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) | ((l₁, p.1), (l₂, p.2)) ∈ S} :=
          hg₂ hS
        have hd : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
            p.2 (hitFrom (-a) 0 (l₂ : ℝ≥0 → ℝ)).toNNReal -
              p.1 (hitFrom (-a) 0 (l₁ : ℝ≥0 → ℝ)).toNNReal :=
          ((continuous_eval_const _).measurable.comp measurable_snd).sub
            ((continuous_eval_const _).measurable.comp measurable_fst)
        have hset : {p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) | ((l₁, p.1), (l₂, p.2)) ∈ S} =
            (fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
              p.2 (hitFrom (-a) 0 (l₂ : ℝ≥0 → ℝ)).toNNReal -
                p.1 (hitFrom (-a) 0 (l₁ : ℝ≥0 → ℝ)).toNNReal) ⁻¹' Icc (-r) r := by
          ext p
          simp only [hSdef, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, abs_le,
            cauchyLevel, passageValue]
        calc ∫⁻ r₁, W {r₂ | ((l₁, r₁), (l₂, r₂)) ∈ S} ∂W
            = (W.prod W) {p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) | ((l₁, p.1), (l₂, p.2)) ∈ S} :=
              (Measure.prod_apply hS₂).symm
          _ = ((W.prod W).map (fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
                p.2 (hitFrom (-a) 0 (l₂ : ℝ≥0 → ℝ)).toNNReal -
                  p.1 (hitFrom (-a) 0 (l₁ : ℝ≥0 → ℝ)).toNNReal)) (Icc (-r) r) := by
              rw [hset, Measure.map_apply hd measurableSet_Icc]
          _ = _ := congrArg (fun μ : Measure ℝ => μ (Icc (-r) r))
              (pathLaw_prod_map_sub_eval hB hm hcont _ _)

/-- Under the Brownian path law, the first passage at `-a < 0` happens by time `a²` with
probability at least `P(N(0,1) ≤ -1)`. -/
theorem gaussianReal_Iic_neg_one_le_pathLaw_hitFrom_neg_le (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {a : ℝ} (ha : 0 < a) :
    gaussianReal 0 1 (Iic (-1)) ≤ (P.map (pathMap B hcont))
      {w : C(ℝ≥0, ℝ) | ((hitFrom (-a) 0 (w : ℝ≥0 → ℝ)).toNNReal : ℝ) ≤ a ^ 2} := by
  have hpm := measurable_pathMap B hm hcont
  have hA : MeasurableSet
      {w : C(ℝ≥0, ℝ) | ((hitFrom (-a) 0 (w : ℝ≥0 → ℝ)).toNNReal : ℝ) ≤ a ^ 2} :=
    measurableSet_le (measurable_hitFrom (r := fun _ => 0) measurable_const (-a)).ennreal_toReal
      measurable_const
  rw [Measure.map_apply hpm hA]
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
  refine (gaussianReal_Iic_neg_one_le_measure_firstBelow_le
    (X := fun ω (s : ℝ) => B s.toNNReal ω) hB' hm' ha).trans (measure_mono_ae ?_)
  filter_upwards [ae_of_ae_map hpm.aemeasurable (ae_hitFrom_neg_ne_top_pathLaw hB hm hcont)]
    with ω hω hle
  have hle' : firstBelow (fun s : ℝ => B s.toNNReal ω) 0 (-a) ≤ a ^ 2 := hle
  show ((hitFrom (-a) 0 (pathMap B hcont ω : ℝ≥0 → ℝ)).toNNReal : ℝ) ≤ a ^ 2
  rw [hitFrom_neg_toNNReal_eq_firstBelow hω.1 ha.le (hω.2 a ha.le)]
  exact hle'

/-- **Lower small-ball bound for the level-passage process at a fixed level.** Under
`ν = (W ⊗ W) ⊗ (W ⊗ W)`, for `a > 0` and `r ≥ 0`,
`ν {|Y a| ≤ r} ≥ c₀ min 1 (r / (√2 a)) P(N(0,1) ≤ -1)²` with `c₀ = 2 e^{-1/2} / √(2π)`. -/
theorem le_measure_abs_cauchyLevel_le (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (2 * Real.exp (-(1 / 2)) / √(2 * Real.pi) * min 1 (r / (√2 * a))) *
        gaussianReal 0 1 (Iic (-1)) ^ 2 ≤
      (((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))).prod
        ((P.map (pathMap B hcont)).prod (P.map (pathMap B hcont))))
        {q | |cauchyLevel a q| ≤ r} := by
  rw [measure_abs_cauchyLevel_le_eq_lintegral hB hm hcont a r]
  have hΦ := gaussianReal_Iic_neg_one_le_pathLaw_hitFrom_neg_le hB hm hcont ha
  have hae : ∀ᵐ l : C(ℝ≥0, ℝ) ∂(P.map (pathMap B hcont)),
      (hitFrom (-a) 0 (l : ℝ≥0 → ℝ)).toNNReal ≠ 0 := by
    filter_upwards [ae_hitFrom_neg_ne_top_pathLaw hB hm hcont] with l hl
    exact hitFrom_neg_toNNReal_ne_zero hl.1 ha (hl.2 a ha.le)
  set W := P.map (pathMap B hcont)
  set K := ENNReal.ofReal (2 * Real.exp (-(1 / 2)) / √(2 * Real.pi) * min 1 (r / (√2 * a)))
  set A := {w : C(ℝ≥0, ℝ) | ((hitFrom (-a) 0 (w : ℝ≥0 → ℝ)).toNNReal : ℝ) ≤ a ^ 2}
  have hA : MeasurableSet A :=
    measurableSet_le (measurable_hitFrom (r := fun _ => 0) measurable_const (-a)).ennreal_toReal
      measurable_const
  have hpt : ∀ l₁ l₂ : C(ℝ≥0, ℝ), (hitFrom (-a) 0 (l₁ : ℝ≥0 → ℝ)).toNNReal ≠ 0 → l₁ ∈ A →
      l₂ ∈ A → K ≤ gaussianReal 0 ((hitFrom (-a) 0 (l₁ : ℝ≥0 → ℝ)).toNNReal +
        (hitFrom (-a) 0 (l₂ : ℝ≥0 → ℝ)).toNNReal) (Icc (-r) r) := by
    intro l₁ l₂ h0 h1 h2
    have h1' : ((hitFrom (-a) 0 (l₁ : ℝ≥0 → ℝ)).toNNReal : ℝ) ≤ a ^ 2 := h1
    have h2' : ((hitFrom (-a) 0 (l₂ : ℝ≥0 → ℝ)).toNNReal : ℝ) ≤ a ^ 2 := h2
    have hv0 : (hitFrom (-a) 0 (l₁ : ℝ≥0 → ℝ)).toNNReal +
        (hitFrom (-a) 0 (l₂ : ℝ≥0 → ℝ)).toNNReal ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg (pos_iff_ne_zero.2 h0) zero_le)
    refine le_trans ?_ (ofReal_mul_min_le_gaussianReal_Icc_neg hv0 hr)
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_min le_rfl ?_)
      (by positivity))
    have hvpos : (0 : ℝ) < ((hitFrom (-a) 0 (l₁ : ℝ≥0 → ℝ)).toNNReal +
        (hitFrom (-a) 0 (l₂ : ℝ≥0 → ℝ)).toNNReal : ℝ≥0) := by
      exact_mod_cast pos_iff_ne_zero.2 hv0
    refine div_le_div_of_nonneg_left hr (Real.sqrt_pos.2 hvpos) ?_
    have hv2 : (((hitFrom (-a) 0 (l₁ : ℝ≥0 → ℝ)).toNNReal +
        (hitFrom (-a) 0 (l₂ : ℝ≥0 → ℝ)).toNNReal : ℝ≥0) : ℝ) ≤ 2 * a ^ 2 := by
      rw [NNReal.coe_add]
      linarith
    calc √(((hitFrom (-a) 0 (l₁ : ℝ≥0 → ℝ)).toNNReal +
          (hitFrom (-a) 0 (l₂ : ℝ≥0 → ℝ)).toNNReal : ℝ≥0) : ℝ) ≤ √(2 * a ^ 2) :=
          Real.sqrt_le_sqrt hv2
      _ = √2 * a := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq ha.le]
  calc K * gaussianReal 0 1 (Iic (-1)) ^ 2 ≤ K * (W A * W A) := by
        rw [sq]
        gcongr
    _ = ∫⁻ l₁, A.indicator (fun _ => K * W A) l₁ ∂W := by
        rw [lintegral_indicator_const hA, mul_assoc]
    _ ≤ _ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with l₁ h0
        by_cases h1 : l₁ ∈ A
        · rw [Set.indicator_of_mem h1, ← lintegral_indicator_const hA]
          refine lintegral_mono fun l₂ => ?_
          by_cases h2 : l₂ ∈ A
          · rw [Set.indicator_of_mem h2]
            exact hpt l₁ l₂ h0 h1 h2
          · rw [Set.indicator_of_notMem h2]
            exact zero_le
        · rw [Set.indicator_of_notMem h1]
          exact zero_le

end PathLaw

end

end LatticeProb
