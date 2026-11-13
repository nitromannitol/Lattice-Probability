import LatticeProb.Prob.ExcursionCountMeanLinear
import LatticeProb.Analysis.ExcursionCountScale

/-!
# Brownian scaling of the mean excursion count

For a real Brownian motion `B` with continuous paths, `ε > 0` and `b > 0`, let `J_ε(b)` be the number of excursions
of `B` above its running minimum, of length larger than `ε`, completed before the first passage below `B 0 - b`
(`pathExcursionCount`). Brownian scaling `t ↦ ε^{-1/2} B (ε t)` carries `J_ε(b)` to `J_1(b / √ε)`, and the mean is
linear in the level (`lintegral_pathExcursionCount_eq_mul`), hence

  `E J_ε(b) = (b / √ε) * E J_1(1)`.

* `pathExcursionCount_scale`: the deterministic scaling identity, for paths with `f (r t) = k g t`;
* `map_eval_eq_of_isPreBrownianReal`: two pre-Brownian motions with measurable coordinates have the same law on the
  product σ-algebra of `ℝ≥0 → ℝ`;
* `lintegral_pathExcursionCount_eq_of_isPreBrownianReal`: the mean excursion count does not depend on the
  underlying Brownian motion (continuous paths);
* `lintegral_pathExcursionCount_eq_div_sqrt`: the scaling formula above.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

/-- **Scaling of the excursion count of a path.** If `f (r t) = k g t` for every `t`, with `r, k > 0`, then the number
of excursions of `f` above its running minimum of length larger than `r ε` before its first passage below
`f 0 - k b` equals the number of excursions of `g` of length larger than `ε` before its first passage below
`g 0 - b`. -/
theorem pathExcursionCount_scale {f g : ℝ≥0 → ℝ} {r : ℝ≥0} {k : ℝ} (hr : 0 < r) (hk : 0 < k)
    (h : ∀ t, f (r * t) = k * g t) (b ε : ℝ) :
    pathExcursionCount f (k * b) (r * ε) = pathExcursionCount g b ε := by
  have hY : ∀ u : ℝ, nnExtend f ((r : ℝ) * u) = k * nnExtend g u := by
    intro u
    simp only [nnExtend]
    rw [Real.toNNReal_mul (NNReal.coe_nonneg r), Real.toNNReal_coe, h]
  have hs := excursionCount_firstPassageBelow_scale (X := nnExtend g) (Y := nnExtend f)
    (NNReal.coe_pos.2 hr) hk hY 0 b ε
  simp only [mul_zero] at hs
  exact hs

/-- **Uniqueness of the law of a pre-Brownian motion.** Two pre-Brownian motions with measurable coordinates have the
same law on the product σ-algebra of `ℝ≥0 → ℝ`. -/
theorem map_eval_eq_of_isPreBrownianReal {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {B : ℝ≥0 → Ω → ℝ} {W : ℝ≥0 → Ω' → ℝ}
    (hB : IsPreBrownianReal B P) (hW : IsPreBrownianReal W Q) (hmB : ∀ t, Measurable (B t))
    (hmW : ∀ t, Measurable (W t)) :
    P.map (fun ω t => B t ω) = Q.map (fun ω t => W t ω) := by
  have hBm : Measurable fun (ω : Ω) (t : ℝ≥0) => B t ω := measurable_pi_iff.2 hmB
  have hWm : Measurable fun (ω : Ω') (t : ℝ≥0) => W t ω := measurable_pi_iff.2 hmW
  have h1 : IsProjectiveLimit (P.map fun (ω : Ω) (t : ℝ≥0) => B t ω) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map I.measurable_restrict hBm]
    exact (hB.hasLaw I).map_eq
  have h2 : IsProjectiveLimit (Q.map fun (ω : Ω') (t : ℝ≥0) => W t ω) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map I.measurable_restrict hWm]
    exact (hW.hasLaw I).map_eq
  exact h1.unique h2

/-- **The mean excursion count depends only on the law.** For two pre-Brownian motions with measurable coordinates and
continuous paths, the mean excursion counts `E J_ε(b)` agree. -/
theorem lintegral_pathExcursionCount_eq_of_isPreBrownianReal {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'} {B : ℝ≥0 → Ω → ℝ} {W : ℝ≥0 → Ω' → ℝ}
    (hB : IsPreBrownianReal B P) (hW : IsPreBrownianReal W Q) (hmB : ∀ t, Measurable (B t))
    (hmW : ∀ t, Measurable (W t)) (hcB : ∀ ω, Continuous fun t => B t ω)
    (hcW : ∀ ω, Continuous fun t => W t ω) (b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P =
      ∫⁻ ω, (pathExcursionCount (fun t => W t ω) b ε : ℝ≥0∞) ∂Q := by
  obtain ⟨Φ, hΦ, hΦP⟩ := exists_measurable_pathExcursionCount b hε
  have hBm : Measurable fun (ω : Ω) (t : ℝ≥0) => B t ω := measurable_pi_iff.2 hmB
  have hWm : Measurable fun (ω : Ω') (t : ℝ≥0) => W t ω := measurable_pi_iff.2 hmW
  calc ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P
      = ∫⁻ ω, Φ (fun t => B t ω) ∂P := lintegral_congr fun ω => (hΦP _ (hcB ω)).symm
    _ = ∫⁻ x, Φ x ∂(P.map fun ω t => B t ω) := (lintegral_map hΦ hBm).symm
    _ = ∫⁻ x, Φ x ∂(Q.map fun ω t => W t ω) := by
        rw [map_eval_eq_of_isPreBrownianReal hB hW hmB hmW]
    _ = ∫⁻ ω, Φ (fun t => W t ω) ∂Q := lintegral_map hΦ hWm
    _ = ∫⁻ ω, (pathExcursionCount (fun t => W t ω) b ε : ℝ≥0∞) ∂Q :=
        lintegral_congr fun ω => hΦP _ (hcW ω)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Brownian scaling of the mean excursion count.** For a real Brownian motion `B` with continuous paths, `ε > 0`
and `b > 0`, the mean number of excursions above the running minimum of length larger than `ε` completed before the
first passage below `B 0 - b` is `(b / √ε)` times the mean number of excursions of length larger than `1` completed
before the first passage below `B 0 - 1`. -/
theorem lintegral_pathExcursionCount_eq_div_sqrt [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ} (hε : 0 < ε) {b : ℝ}
    (hb : 0 < b) :
    ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P =
      ENNReal.ofReal (b / √ε) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P := by
  set c : ℝ≥0 := ⟨ε, hε.le⟩ with hc_def
  have hcε : (c : ℝ) = ε := rfl
  have hcpos : 0 < c := NNReal.coe_pos.1 hε
  have hsq : 0 < √ε := Real.sqrt_pos.2 hε
  have hW : IsBrownianReal (fun t ω => (√(c : ℝ))⁻¹ * B (c * t) ω) P := hB.smul hcpos.ne'
  have hmW : ∀ t, Measurable fun ω => (√(c : ℝ))⁻¹ * B (c * t) ω := fun t => (hm _).const_mul _
  have hcW : ∀ ω, Continuous fun t => (√(c : ℝ))⁻¹ * B (c * t) ω := fun ω =>
    ((hcont ω).comp (continuous_const.mul continuous_id)).const_mul _
  have hdet : ∀ ω, pathExcursionCount (fun t => B t ω) b ε =
      pathExcursionCount (fun t => (√(c : ℝ))⁻¹ * B (c * t) ω) (b / √ε) 1 := by
    intro ω
    have hs := pathExcursionCount_scale (f := fun t => B t ω)
      (g := fun t => (√(c : ℝ))⁻¹ * B (c * t) ω) (r := c) (k := √ε) hcpos hsq
      (fun t => by rw [← hcε]; exact (mul_inv_cancel_left₀ (hcε ▸ hsq.ne') _).symm) (b / √ε) 1
    have e : √ε * (b / √ε) = b := by field_simp
    rw [e, hcε, mul_one] at hs
    exact hs
  calc ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P
      = ∫⁻ ω, (pathExcursionCount (fun t => (√(c : ℝ))⁻¹ * B (c * t) ω) (b / √ε) 1 : ℝ≥0∞) ∂P :=
        lintegral_congr fun ω => by rw [hdet ω]
    _ = ∫⁻ ω, (pathExcursionCount (fun t => B t ω) (b / √ε) 1 : ℝ≥0∞) ∂P :=
        lintegral_pathExcursionCount_eq_of_isPreBrownianReal hW.toIsPreBrownianReal hB.toIsPreBrownianReal
          hmW hm hcW hcont _ one_pos
    _ = ENNReal.ofReal (b / √ε) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P :=
        lintegral_pathExcursionCount_eq_mul hB hm hcont one_pos (div_pos hb hsq)

end LatticeProb.LadderSet
