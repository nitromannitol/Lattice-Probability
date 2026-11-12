import LatticeProb.Prob.UpcrossPieceFdd

/-!
# Weak limits of stay-conditioned drifted laws start at the origin

Let `B` be a Brownian motion with continuous paths, `Q` the law of its path on `C(ℝ≥0, ℝ)`, and for
`δ > 0` let `μ_δ = Q[· | {w | drift μ w stays above -δ}]` be the law of the path conditioned on the drifted
path staying above `-δ`.  Every `μ_δ` is absolutely continuous with respect to `Q`, and `Q` is carried by
the paths started at `0`.  Hence any weak limit `ν` of `μ_δ` as `δ → 0+` is carried by the paths started
at `0`: the bounded continuous function `w ↦ min 1 |w 0|` has integral `0` against every `μ_δ`, hence
against `ν`.

## Main statement

* `LatticeProb.ae_eval_zero_of_weakLimit`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **A weak limit of the stay-conditioned drifted path laws starts at the origin.**  If the laws of
the path of Brownian motion `B`, conditioned on the drifted path `w + μ t` staying above `-δ`, converge
weakly to `ν` along `δ → 0+`, then `ν`-almost every path `z` satisfies `z 0 = 0`.  (The positivity of the
drift is not used in the proof.) -/
theorem ae_eval_zero_of_weakLimit [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ}
    (_hmu : 0 < mu) {ν : Measure C(ℝ≥0, ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ, Tendsto (fun δ : ℝ =>
      ∫ w, f w ∂((P.map (pathMap B hcont))[|driftMap mu ⁻¹' staySet δ]))
      (𝓝[>] 0) (𝓝 (∫ w, f w ∂ν))) :
    ∀ᵐ z : C(ℝ≥0, ℝ) ∂ν, z 0 = 0 := by
  obtain ⟨f, hf⟩ : ∃ f : C(ℝ≥0, ℝ) →ᵇ ℝ, ∀ z, f z = min 1 |z 0| := by
    refine ⟨BoundedContinuousFunction.mkOfBound
      ⟨fun z => min 1 |z 0|, continuous_const.min (continuous_eval_const 0).abs⟩ 1 ?_,
      fun _ => rfl⟩
    intro x y
    have hx : 0 ≤ min 1 |x 0| := le_min zero_le_one (abs_nonneg _)
    have hy : 0 ≤ min 1 |y 0| := le_min zero_le_one (abs_nonneg _)
    have hx' : min 1 |x 0| ≤ 1 := min_le_left _ _
    have hy' : min 1 |y 0| ≤ 1 := min_le_left _ _
    rw [Real.dist_eq, abs_le]
    exact ⟨by simp only [ContinuousMap.coe_mk]; linarith, by simp only [ContinuousMap.coe_mk]; linarith⟩
  have hf0 : ∀ z, 0 ≤ f z := fun z => by
    rw [hf]; exact le_min zero_le_one (abs_nonneg _)
  have hQ : ∀ᵐ z ∂(P.map (pathMap B hcont)), z 0 = 0 := by
    have hmeas : Measurable (pathMap B hcont) := measurable_pathMap B hm hcont
    have hset : MeasurableSet {z : C(ℝ≥0, ℝ) | z 0 = 0} :=
      (isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet
    rw [ae_map_iff hmeas.aemeasurable hset]
    simpa using hB.toIsPreBrownianReal.eval_zero_ae_eq_zero
  have hint : ∀ δ : ℝ,
      ∫ w, f w ∂((P.map (pathMap B hcont))[|driftMap mu ⁻¹' staySet δ]) = 0 := by
    intro δ
    have h1 : ∀ᵐ z ∂((P.map (pathMap B hcont))[|driftMap mu ⁻¹' staySet δ]), z 0 = 0 :=
      hQ.filter_mono cond_absolutelyContinuous.ae_le
    refine integral_eq_zero_of_ae (h1.mono fun z hz => ?_)
    simp [hf, hz]
  have hlim : Tendsto (fun δ : ℝ =>
      ∫ w, f w ∂((P.map (pathMap B hcont))[|driftMap mu ⁻¹' staySet δ]))
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr fun δ => (hint δ).symm
  have h0 : ∫ w, f w ∂ν = 0 := tendsto_nhds_unique (hν f) hlim
  have h2 : f =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg hf0 (f.integrable ν)).1 h0
  filter_upwards [h2] with z hz
  by_contra hne
  have hpos : 0 < f z := by
    rw [hf]; exact lt_min one_pos (abs_pos.2 hne)
  exact hpos.ne' hz

end LatticeProb
