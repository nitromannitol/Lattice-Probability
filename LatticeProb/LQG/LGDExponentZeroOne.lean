import LatticeProb.LQG.LGDExponentLQGLimit
import LatticeProb.LQG.LGDExponentSimilarity
import LatticeProb.LQG.LGDMeasurableInMeasure
import LatticeProb.LQG.WholePlaneProfileLaw
import LatticeProb.LQG.GMCScaleIncrement
import LatticeProb.LQG.GMCDyadicLimit

/-!
# The Liouville graph distance exponent between `0` and `1` for the whole-plane GFF

Let `h` be a whole-plane GFF normalized so that its circle average over `∂B_1(0)` vanishes, and let
`μ_h` be its `γ`-LQG measure (`0 < γ < 2`). Almost surely the Liouville graph distance
`D_δ(μ_h)(0, 1)` of Ding-Zeitouni-Zhang satisfies `log D_δ(μ_h)(0, 1) / log δ⁻¹ → χ_γ` as `δ ↓ 0`.

The statement is deduced from one model: a white noise `W` with its whole-plane GFF `h₀`, together
with a whole-plane GFF `(hC₀, hcirc₀)` whose circle averages are, for each `(r, z)`, almost surely
those of `h₀ − h₀_1(0)`. In this model the exponent between two points of the Fernique box
`[3/10, 7/10]²` is `χ_γ` (`LatticeProb.LQG.ae_tendsto_lgdRatio_of_isLQGLimit`). The law of the
LQG measure does not depend on the model (`LatticeProb.LQG.ae_mem_iff_of_isWholePlaneGFF`), and the
coordinate change for `x ↦ (x − z)/4` moves the two points to `0` and `1` up to a positive
constant factor of the measure, which does not change the exponent
(`LatticeProb.LQG.tendsto_lgdRatio_of_map_simMap_eq_smul`).

* `LatticeProb.LQG.mem_openSquare_of_mem_ball_ferniqueBox`: points of `[3/10, 7/10]²` are at distance
  at least `1/10` from the boundary of the unit square.
* `LatticeProb.LQG.ae_ae_eq_circleAvg_of_isWholePlaneGFF`: pointwise almost sure agreement of the
  circle averages gives almost sure agreement for Lebesgue-almost every centre.
* `LatticeProb.LQG.ae_tendsto_lgdRatio_zero_one_of_model`: the exponent between `0` and `1`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric

open QuantumZipper GMCIdent3 GMCIdent WhiteNoise DZZ GFFExist DG SupTail

/-- **The Fernique box `[3/10, 7/10]²` stays at distance `1/10` from the boundary of the unit
square.** -/
theorem _root_.LatticeProb.LQG.mem_openSquare_of_mem_ball_ferniqueBox {z : ℂ}
    (hz : z ∈ ferniqueBox ⟨3 / 10, 3 / 10⟩ (2 / 5)) : Metric.ball z (1 / 10) ⊆ openSquare := by
  intro w hw
  have hd : ‖w - z‖ < 1 / 10 := by rw [← dist_eq_norm]; exact Metric.mem_ball.1 hw
  have hre : |w.re - z.re| < 1 / 10 := by
    have := Complex.abs_re_le_norm (w - z); rw [Complex.sub_re] at this; linarith
  have him : |w.im - z.im| < 1 / 10 := by
    have := Complex.abs_im_le_norm (w - z); rw [Complex.sub_im] at this; linarith
  rw [ferniqueBox, Complex.mem_reProdIm, mem_Icc, mem_Icc] at hz
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hz
  rw [abs_lt] at hre him
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **From pointwise to Lebesgue-almost-everywhere agreement of circle averages.** If the circle
averages of a whole-plane GFF `(hC, hcirc)` agree, for each radius `r > 0` and centre `z`, almost
surely with those of `h₀ − h₀_1(0)` for a measurable distribution-valued field `h₀`, then almost
surely, for every dyadic radius `2^{-k}`, they agree for Lebesgue-almost every centre. -/
theorem _root_.LatticeProb.LQG.ae_ae_eq_circleAvg_of_isWholePlaneGFF {Ω₀ : Type*}
    [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {h₀ : Ω₀ → DistC}
    (hm₀ : Measurable h₀) {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ}
    (hG₀ : LatticeProb.Gauss.IsWholePlaneGFF P₀ hC₀ hcirc₀)
    (hcirc₀_eq : ∀ r : ℝ, 0 < r → ∀ z : ℂ, (fun ω => hcirc₀ ω r z) =ᵐ[P₀]
      fun ω => circleAvg (h₀ ω) r z - circleAvg (h₀ ω) 1 0) :
    ∀ᵐ ω ∂P₀, ∀ k, hcirc₀ ω (LatticeProb.LQG.dyadicScale k) =ᵐ[volume] fun z =>
      circleAvg (h₀ ω) (radius k) z - circleAvg (h₀ ω) 1 0 := by
  obtain ⟨F, hF, hFc⟩ := LatticeProb.LQG.exists_measurable_profile hG₀
  have hpos : ∀ k : ℕ, 0 < LatticeProb.LQG.dyadicScale k := fun k => by
    unfold LatticeProb.LQG.dyadicScale; positivity
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂P₀, ∀ᵐ z ∂(volume : Measure ℂ),
      F ω ⟨⟨LatticeProb.LQG.dyadicScale k, hpos k⟩, z⟩ =
        circleAvg (h₀ ω) (radius k) z - circleAvg (h₀ ω) 1 0 := by
    intro k
    set r : Set.Ioi (0 : ℝ) := ⟨LatticeProb.LQG.dyadicScale k, hpos k⟩ with hr
    have hmeas : MeasurableSet {x : ℂ × Ω₀ |
        F x.2 ⟨r, x.1⟩ = circleAvg (h₀ x.2) (radius k) x.1 - circleAvg (h₀ x.2) 1 0} := by
      apply measurableSet_eq_fun
      · exact measurable_uncurry_of_continuous_of_measurable (u := fun z ω => F ω ⟨r, z⟩)
          (fun ω => (F ω).continuous.comp (continuous_const.prodMk continuous_id))
          (fun z => (continuous_eval_const _).measurable.comp hF)
      · exact (measurable_circleAvg.comp ((hm₀.comp measurable_snd).prodMk
          (measurable_const.prodMk measurable_fst))).sub
          ((measurable_circleAvg_left 1 0).comp (hm₀.comp measurable_snd))
    refine (Measure.ae_ae_comm hmeas).1 (Eventually.of_forall fun z => ?_)
    filter_upwards [hFc, hcirc₀_eq _ r.2 z] with ω h1 h2
    rw [h1]
    exact h2
  filter_upwards [ae_all_iff.2 hk, hFc] with ω hω hFω k
  filter_upwards [hω k] with z hz
  rw [← hz]
  exact (hFω (⟨LatticeProb.LQG.dyadicScale k, hpos k⟩, z)).symm

/-- **The Liouville graph distance exponent between `0` and `1`.** Suppose some probability space
carries a white noise `W` with whole-plane GFF `h₀` (pairings almost surely those of `W`) and a
whole-plane GFF `(hC₀, hcirc₀)` whose circle averages are, for each radius `r > 0` and centre `z`,
almost surely those of `h₀ − h₀_1(0)`. Then for every whole-plane GFF `(hC, hcirc)` on any
probability space and its `γ`-LQG measure `μ` (`0 < γ < 2`), almost surely
`log D_δ(μ)(0, 1) / log δ⁻¹ → χ_γ` as `δ ↓ 0`. -/
theorem _root_.LatticeProb.LQG.ae_tendsto_lgdRatio_zero_one_of_model
    {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {W : WNSpace → Ω₀ → ℝ} (hW : IsWhiteNoise P₀ W) {h₀ : Ω₀ → DistC}
    (hh₀ : LQGMetric.IsWholePlaneGFF h₀ P₀) (hm₀ : Measurable h₀)
    (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P₀] W (testL2 φ))
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ}
    (hG₀ : LatticeProb.Gauss.IsWholePlaneGFF P₀ hC₀ hcirc₀)
    (hcirc₀_eq : ∀ r : ℝ, 0 < r → ∀ z : ℂ, (fun ω => hcirc₀ ω r z) =ᵐ[P₀]
      fun ω => circleAvg (h₀ ω) r z - circleAvg (h₀ ω) 1 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ}
    (hμ : LatticeProb.LQG.IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, Tendsto (fun δ : ℝ => Real.log (lgdDZZ (μ ω) δ 0 1).toNat / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 (chiDZZ γ)) := by
  have hz0 : ∀ H : ℝ → ℂ → ℝ, LatticeProb.Gauss.fieldCircleAverage 0 H = H := fun H => by
    funext r z; simp [LatticeProb.Gauss.fieldCircleAverage]
  -- the model: exponent between `u` and `v` in the Fernique box `[3/10, 7/10]²`
  obtain ⟨m₀, hm₀'⟩ := hG₀.exists_isLQGMeasure hγ hγ2
  have hcircL := LatticeProb.LQG.ae_ae_eq_circleAvg_of_isWholePlaneGFF hm₀ hG₀ hcirc₀_eq
  set u : ℂ := ⟨3 / 8, 1 / 2⟩ with hu
  set v : ℂ := ⟨5 / 8, 1 / 2⟩ with hv
  have huv : u ≠ v := by
    intro h
    have := congrArg Complex.re h
    norm_num [hu, hv] at this
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      u + (t : ℂ) * (v - u) ∈ interior (ferniqueBox ⟨3 / 10, 3 / 10⟩ (2 / 5)) := by
    intro t ht0 ht1
    rw [ferniqueBox, Complex.interior_reProdIm, interior_Icc, Complex.mem_reProdIm]
    simp only [hu, hv, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, mem_Ioo]
    norm_num
    constructor <;> linarith
  have hmodel := LatticeProb.LQG.ae_tendsto_lgdRatio_of_isLQGLimit hW hh₀ hm₀ hae
    (by norm_num : (0 : ℝ) < 2 / 5) (fun z hz => LatticeProb.LQG.mem_openSquare_of_mem_ball_ferniqueBox hz)
    hγ hγ2 hm₀' hcircL huv hseg
  -- the coordinate change `x ↦ (x + 4u)/4` of the given field
  have hμ' : LatticeProb.LQG.IsLQGMeasure P γ hcirc μ := by
    simpa only [LatticeProb.LQG.IsLQGMeasureOfField, hz0] using hμ
  obtain ⟨hC'', hcirc'', μ'', c, hG'', hμ'', hc⟩ :=
    hG.exists_coordChange hγ hγ2 hμ' (r := 4) (by norm_num) (-(4 * u))
  -- law transfer from the model
  have hm₀f : LatticeProb.LQG.IsLQGMeasureOfField P₀ γ 0 hcirc₀ m₀ := by
    simpa only [LatticeProb.LQG.IsLQGMeasureOfField, hz0] using hm₀'
  have hμ''f : LatticeProb.LQG.IsLQGMeasureOfField P γ 0 hcirc'' μ'' := by
    simpa only [LatticeProb.LQG.IsLQGMeasureOfField, hz0] using hμ''
  have htr := (LatticeProb.LQG.ae_mem_iff_of_isWholePlaneGFF hG₀ hG'' hm₀f hμ''f
    (LatticeProb.LQG.measurableSet_lgdExponentEvent u v (chiDZZ γ))).1 hmodel
  have hψ : (fun x : ℂ => (x - -(4 * u)) / ((4 : ℝ) : ℂ)) = simMap (1 / 4) u := by
    funext x
    simp only [simMap]
    push_cast
    ring
  have h0 : simMap (1 / 4 : ℂ) u 0 = u := by simp [simMap]
  have h1 : simMap (1 / 4 : ℂ) u 1 = v := by
    apply Complex.ext <;> norm_num [simMap, hu, hv]
  filter_upwards [htr, hc] with ω hω hcω
  obtain ⟨hc0, hcT, hmap⟩ := hcω
  rw [hψ, ← ENNReal.ofReal_toReal hcT] at hmap
  refine LatticeProb.LQG.tendsto_lgdRatio_of_map_simMap_eq_smul (by norm_num) u
    (ENNReal.toReal_pos hc0 hcT) hmap ?_
  rw [h0, h1]
  exact hω

end LQGMetric
