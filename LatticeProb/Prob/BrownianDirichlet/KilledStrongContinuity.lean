import LatticeProb.Prob.BrownianDirichlet.KilledLp
import LatticeProb.Analysis.ContractionSemigroup
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Strong continuity of killed Brownian evolution

Bounded continuous data converge at zero by dominated convergence on paths and then on
starting points. Density and contraction extend this convergence to the full L² space.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace LatticeProb

noncomputable section

variable {d : ℕ} {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
  {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)

include hB hμ in
/-- At an interior starting point, killed expectation of bounded continuous data
converges to the initial datum. -/
lemma tendsto_killed_zero_of_bcf (b : Euc d →ᵇ ℝ) {x : Euc d} (hx : x ∈ B) :
    Tendsto (fun t : ℝ≥0 ↦ killed B σ μ t b x) (𝓝 0) (𝓝 (b x)) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hlim : ∀ᵐ ω ∂μ, Tendsto
      (fun t : ℝ≥0 ↦ if (t : ℝ≥0∞) < scaledExit B σ x ω
        then b (x + σ • ω t) else 0) (𝓝 0) (𝓝 (b x)) := by
    filter_upwards [standardBrownianLaw_eval_zero_ae hμ] with ω hω
    have hp := scaledExit_pos hB σ hx hω
    have he : ∀ᶠ t : ℝ≥0 in 𝓝 0, (t : ℝ≥0∞) < scaledExit B σ x ω :=
      (ENNReal.continuous_coe.tendsto 0).eventually (gt_mem_nhds hp)
    have hc : Continuous (fun t : ℝ≥0 ↦ b (x + σ • ω t)) :=
      b.continuous.comp (continuous_const.add (ω.continuous.const_smul σ))
    have hc := hc.tendsto 0
    simp only [hω, smul_zero, add_zero] at hc
    apply hc.congr'
    filter_upwards [he] with t ht
    exact (if_pos ht).symm
  have hi := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (fun _ ↦ ‖b‖)
    (Eventually.of_forall fun t ↦
      (integrable_killed_integrand hB σ t b.continuous.measurable (norm_nonneg b)
        (fun y ↦ (Real.norm_eq_abs _).symm.trans_le (b.norm_coe_le_norm y)) x).1)
    (Eventually.of_forall fun t ↦ Eventually.of_forall fun ω ↦ by
      split_ifs
      · exact b.norm_coe_le_norm _
      · exact (norm_zero : ‖(0 : ℝ)‖ = 0).le.trans (norm_nonneg b))
    (integrable_const ‖b‖) hlim
  simpa only [killed, integral_const, probReal_univ, one_smul] using hi

variable [IsFiniteMeasure (volume.restrict B)]

/-- Killed evolution converges in L² to every bounded continuous initial datum. -/
lemma tendsto_killedLp_zero_of_bcf (b : Euc d →ᵇ ℝ) :
    Tendsto (fun t : ℝ≥0 ↦ killedLp hB σ hμ t
      (BoundedContinuousFunction.toLp 2 (volume.restrict B) ℝ b)) (𝓝 0)
      (𝓝 (BoundedContinuousFunction.toLp 2 (volume.restrict B) ℝ b)) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hbC : ∀ y, |b y| ≤ ‖b‖ := fun y ↦
    (Real.norm_eq_abs _).symm.trans_le (b.norm_coe_le_norm y)
  have hbLp : MemLp b 2 (volume.restrict B) :=
    MemLp.of_bound b.continuous.aestronglyMeasurable ‖b‖
      (Eventually.of_forall b.norm_coe_le_norm)
  have hbEq : BoundedContinuousFunction.toLp 2 (volume.restrict B) ℝ b =
      hbLp.toLp b := by
    apply Lp.ext
    exact (BoundedContinuousFunction.coeFn_toLp 2 (volume.restrict B) ℝ b).trans
      hbLp.coeFn_toLp.symm
  rw [hbEq]
  simp_rw [killedLp_toLp hB σ hμ _ b.continuous.measurable (norm_nonneg b) hbC]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun t ↦ killed B σ μ t b)
    (fun t ↦ memLp_killed hB σ hμ t b.continuous.measurable (norm_nonneg b) hbC)
    b hbLp).2
  simp_rw [eLpNorm_two_eq_lintegral_sq]
  have hi : Tendsto
      (fun t : ℝ≥0 ↦ ∫⁻ x, ENNReal.ofReal ((killed B σ μ t b x - b x) ^ 2)
        ∂(volume.restrict B)) (𝓝 0) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence
      (μ := volume.restrict B) (l := 𝓝 (0 : ℝ≥0)) (f := fun _ ↦ 0)
      (F := fun t : ℝ≥0 ↦ fun x ↦
        ENNReal.ofReal ((killed B σ μ t b x - b x) ^ 2))
      (fun _ ↦ ENNReal.ofReal ((2 * ‖b‖) ^ 2))
      (Eventually.of_forall fun t ↦
        (((measurable_killed hB σ t b.continuous.measurable).sub
          b.continuous.measurable).pow_const 2).ennreal_ofReal)
      (Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ by
        apply ENNReal.ofReal_le_ofReal
        have hk := abs_killed_le (B := B) σ (μ := μ) t (norm_nonneg b) hbC x
        have hd : |killed B σ μ t b x - b x| ≤ 2 * ‖b‖ :=
          (abs_sub _ _).trans (by linarith [hbC x])
        nlinarith [sq_abs (killed B σ μ t b x - b x), abs_nonneg
          (killed B σ μ t b x - b x)])
      (by
        rw [lintegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) ?_
    · simpa only [lintegral_zero] using h
    · filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
      have hc := ((tendsto_killed_zero_of_bcf hB σ hμ b hx).sub
        (tendsto_const_nhds (x := b x))).pow 2
      simpa only [Function.comp_def, sub_self, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]
        using (ENNReal.continuous_ofReal.tendsto _).comp hc
  simpa only [Pi.sub_apply, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    using hi.ennrpow_const (1 / 2 : ℝ)

/-- Contraction extends convergence at zero from bounded continuous data to all L² data. -/
lemma tendsto_killedLp_zero (z : Lp ℝ 2 (volume.restrict B)) :
    Tendsto (fun t : ℝ≥0 ↦ killedLp hB σ hμ t z) (𝓝 0) (𝓝 z) := by
  have he : Equicontinuous (fun t : ℝ≥0 ↦
      (killedLp hB σ hμ t : Lp ℝ 2 (volume.restrict B) →
        Lp ℝ 2 (volume.restrict B))) :=
    (LipschitzWith.uniformEquicontinuous _ 1 fun t ↦
      ContinuousLinearMap.lipschitzWith_of_opNorm_le (by
        simpa only [NNReal.coe_one] using norm_killedLp_le hB σ hμ t)).equicontinuous
  have hc := he.isClosed_setOf_tendsto (l := 𝓝 (0 : ℝ≥0)) continuous_id
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ (volume.restrict B) ℝ
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hs : Set.range (BoundedContinuousFunction.toLp 2 (volume.restrict B) ℝ) ⊆
      {z | Tendsto (fun t : ℝ≥0 ↦ killedLp hB σ hμ t z) (𝓝 0) (𝓝 z)} := by
    rintro _ ⟨b, rfl⟩
    exact tendsto_killedLp_zero_of_bcf hB σ hμ b
  have hh := closure_minimal hs hc
  rw [hd.closure_range] at hh
  exact hh (mem_univ z)

/-- The difference of two orbits is controlled by the two nonnegative time increments. -/
lemma norm_killedLp_sub_le (z : Lp ℝ 2 (volume.restrict B)) (s t : ℝ≥0) :
    ‖killedLp hB σ hμ t z - killedLp hB σ hμ s z‖ ≤
      ‖killedLp hB σ hμ (t - s) z - z‖ +
        ‖killedLp hB σ hμ (s - t) z - z‖ := by
  have hi (a b : ℝ≥0) (hab : a ≤ b) :
      ‖killedLp hB σ hμ b z - killedLp hB σ hμ a z‖ ≤
        ‖killedLp hB σ hμ (b - a) z - z‖ := by
    have ht : b = a + (b - a) := (add_tsub_cancel_of_le hab).symm
    conv_lhs => rw [ht, killedLp_add]
    change ‖killedLp hB σ hμ a (killedLp hB σ hμ (b - a) z) -
      killedLp hB σ hμ a z‖ ≤ _
    rw [← map_sub]
    simpa only [one_mul] using (killedLp hB σ hμ a).le_of_opNorm_le
      (norm_killedLp_le hB σ hμ a) (killedLp hB σ hμ (b - a) z - z)
  rcases le_total s t with hst | hts
  · exact (hi s t hst).trans (le_add_of_nonneg_right (norm_nonneg _))
  · rw [norm_sub_rev]
    exact (hi t s hts).trans (le_add_of_nonneg_left (norm_nonneg _))

/-- Every killed Brownian L² orbit is continuous on nonnegative real time. -/
lemma continuous_killedLp_orbit (z : Lp ℝ 2 (volume.restrict B)) :
    Continuous (fun t : ℝ≥0 ↦ killedLp hB σ hμ t z) := by
  apply continuous_iff_continuousAt.2
  intro s
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hz : Tendsto (fun t : ℝ≥0 ↦ ‖killedLp hB σ hμ t z - z‖)
      (𝓝 0) (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_killedLp_zero hB σ hμ z)
  have hr : Tendsto (fun t : ℝ≥0 ↦ t - s) (𝓝 s) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ≥0 ↦ t - s) := by fun_prop
    simpa only [tsub_self] using hc.tendsto s
  have hl : Tendsto (fun t : ℝ≥0 ↦ s - t) (𝓝 s) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ≥0 ↦ s - t) := by fun_prop
    simpa only [tsub_self] using hc.tendsto s
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (norm_killedLp_sub_le hB σ hμ z s) (by
      simpa only [Function.comp_apply, add_zero] using (hz.comp hr).add (hz.comp hl))

/-- Killed Brownian evolution as a strongly continuous contraction semigroup on L². -/
def killedSemigroup : ContractionSemigroup.StronglyContinuousContractionSemigroup
    (Lp ℝ 2 (volume.restrict B)) where
  operator := killedLp hB σ hμ
  map_zero := killedLp_zero hB σ hμ
  map_add := killedLp_add hB σ hμ
  norm_le_one := norm_killedLp_le hB σ hμ
  continuous_orbit := continuous_killedLp_orbit hB σ hμ

end

end LatticeProb
