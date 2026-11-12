import Mathlib
import LatticeProb.LQG.LQGMassInduction
import LatticeProb.LQG.LQGBallMassUpperDyadic

/-!
# Positive moments of the mass of a disc against the Liouville measure

Let `h` be a whole-plane Gaussian free field and `μ` its `γ`-Liouville measure, the almost sure vague limit of
the approximate Liouville measures `μ_n = lqgApprox γ h 2^{-n}`. For `γ ≠ 0` and `1 ≤ p` with `p γ² < 4`,
the moment `E μ(B(0, 1/4))^p` is bounded by a constant that depends only on `γ` and `p`.

The proof takes a continuous cut-off `g₀` with `1_{B(0,1/4)} ≤ g₀ ≤ 1_{B(0,1/2)}`, so that
`μ(B(0,1/4)) ≤ ∫ g₀ dμ = lim_n ∫ g₀ dμ_n` almost surely (vague convergence), and applies Fatou's lemma to the
uniform moment bound for `M_n = ∫ g₀ dμ_n`.

* `LatticeProb.LQG.pow_measure_ball_le_liminf`: the deterministic comparison `μ(B)^p ≤ liminf M_{n+1}^p`.
* `LatticeProb.LQG.IsWholePlaneGFF.aemeasurable_lqgApproxMass`: `M_n` is almost everywhere measurable.
* `LatticeProb.LQG.ballMassPosMoment_of_lt`: the moment bound for the mass of the disc.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling LatticeProb

/-- A continuous density gives a locally finite measure `lqgApprox`. -/
theorem isLocallyFiniteMeasure_lqgApprox_of_continuous (γ : ℝ) {hε : ℝ → ℂ → ℝ} {ε : ℝ}
    (hc : Continuous (hε ε)) : IsLocallyFiniteMeasure (lqgApprox γ hε ε) := by
  unfold lqgApprox
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc)))

/-- For a locally finite measure and a nonnegative continuous compactly supported `g`,
`∫⁻ ofReal g = ofReal ∫ g`. -/
theorem lintegral_ofReal_eq_ofReal_integral_of_hasCompactSupport {ν : Measure ℂ} [IsLocallyFiniteMeasure ν]
    {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ x, 0 ≤ g x) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂ν = ENNReal.ofReal (∫ x, g x ∂ν) :=
  (ofReal_integral_eq_lintegral_ofReal (hg.integrable_of_hasCompactSupport hgc)
    (ae_of_all _ hg0)).symm

/-- **Comparison with the approximations.** If `μ` is the vague limit of the approximate Liouville measures
(along the dyadic scales, with continuous densities), `g` is continuous with compact support, `g ≥ 0` and
`g ≥ 1` on `B(0, 1/4)`, then `μ(B(0, 1/4))^p ≤ liminf_n (∫ g dμ_{n+1})^p`. -/
theorem pow_measure_ball_le_liminf {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k))) {m : Measure ℂ} (hm : IsLQGLimit γ hε m)
    {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∀ x ∈ ball (0 : ℂ) (1 / 4), 1 ≤ g x) {p : ℝ} (hp : 0 ≤ p) :
    (m (ball (0 : ℂ) (1 / 4))) ^ p ≤
      liminf (fun k : ℕ => (lqgApproxMass γ hε (fun x => ENNReal.ofReal (g x)) (k + 1)) ^ p) atTop := by
  have hMk : ∀ k : ℕ, lqgApproxMass γ hε (fun x => ENNReal.ofReal (g x)) k =
      ENNReal.ofReal (∫ x, g x ∂(lqgApprox γ hε (dyadicScale k))) := fun k => by
    have := isLocallyFiniteMeasure_lqgApprox_of_continuous γ (hcont k)
    exact lintegral_ofReal_eq_ofReal_integral_of_hasCompactSupport hg hgc hg0
  have htend : Tendsto (fun k : ℕ => lqgApproxMass γ hε (fun x => ENNReal.ofReal (g x)) k) atTop
      (𝓝 (ENNReal.ofReal (∫ x, g x ∂m))) := by
    simp_rw [hMk]
    exact ENNReal.tendsto_ofReal (hm.tendsto_integral g hg hgc)
  have hshift := (tendsto_add_atTop_iff_nat 1).2 htend
  have hpow : Tendsto (fun k : ℕ =>
      (lqgApproxMass γ hε (fun x => ENNReal.ofReal (g x)) (k + 1)) ^ p) atTop
      (𝓝 ((ENNReal.ofReal (∫ x, g x ∂m)) ^ p)) :=
    ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp hshift
  rw [hpow.liminf_eq]
  refine ENNReal.rpow_le_rpow ?_ hp
  have := hm.isLocallyFiniteMeasure
  rw [← lintegral_ofReal_eq_ofReal_integral_of_hasCompactSupport hg hgc hg0, ← lintegral_indicator_one
    (measurableSet_ball : MeasurableSet (ball (0 : ℂ) (1 / 4)))]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ ball (0 : ℂ) (1 / 4)
  · rw [Set.indicator_of_mem hx]
    exact ENNReal.one_le_ofReal.2 (hg1 x hx)
  · rw [Set.indicator_of_notMem hx]; exact zero_le

/-- The mass `M_n = ∫ f dμ_n` of a measurable cut-off supported in `closedBall 0 (1/2)` is almost
everywhere measurable. -/
theorem IsWholePlaneGFF.aemeasurable_lqgApproxMass {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {f : ℂ → ℝ≥0∞} (hfm : Measurable f) (hf0 : ∀ x ∉ closedBall (0 : ℂ) (1 / 2), f x = 0) (n : ℕ) :
    AEMeasurable (fun ω => lqgApproxMass γ (hcirc ω) f n) P := by
  classical
  have h1 : (0 : ℝ) < 1 := one_pos
  have heq : (fun ω => lqgApproxMass γ (hcirc ω) f n) = fun ω => ∑ c : ZMod 2 × ZMod 2,
      ∑ i ∈ (squareIndex 1).filter (fun i => squareClass i = c), squareMass γ (hcirc ω) f 1 i n :=
    funext fun ω => lqgApproxMass_eq_sum_squareClass h1 γ (hcirc ω) hf0 n
  rw [heq]
  refine Finset.aemeasurable_fun_sum _ fun c _ => ?_
  refine Finset.aemeasurable_fun_sum _ fun i _ => ?_
  exact LatticeProb.LQG.IsWholePlaneGFF.aemeasurable_squareMass hh γ hfm 1 i n

/-- **Positive moments of the mass of a disc.** For `γ ≠ 0` and `1 ≤ p` with `p γ² < 4`, the moment
`E μ(B(0, 1/4))^p` of the `γ`-Liouville measure of a whole-plane Gaussian free field is bounded by a constant
depending only on `γ` and `p`. -/
theorem ballMassPosMoment_of_lt.{u} {γ p : ℝ} (hγ : γ ≠ 0) (hp : 1 ≤ p) (hpγ : p * γ ^ 2 < 4) :
    BallMassPosMoment.{u} γ p := by
  classical
  obtain ⟨g, hg1, hg0, hgc, hgI⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall (0 : ℂ) (1 / 4)) (isOpen_ball (x := (0 : ℂ)) (ε := 1 / 2)).isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 (closedBall_subset_ball (by norm_num)))
  have hgnn : ∀ x, 0 ≤ g x := fun x => (hgI x).1
  have hgle : ∀ x, g x ≤ 1 := fun x => (hgI x).2
  have hcut : IsCutoffFn (fun x => ENNReal.ofReal (g x)) :=
    { measurable := ENNReal.measurable_ofReal.comp g.continuous.measurable
      le_one := fun x => ENNReal.ofReal_le_one.2 (hgle x)
      one_le_of_mem := fun x hx => by
        have := hg1 (ball_subset_closedBall hx)
        simp only [Pi.one_apply] at this
        simp [this]
      eq_zero_of_not_mem := fun x hx => by
        have hx' : x ∈ (ball (0 : ℂ) (1 / 2))ᶜ := fun h => hx (ball_subset_closedBall h)
        have := hg0 hx'
        simp [this] }
  obtain ⟨C, hC⟩ := exists_massMomentBound.{u} hγ hcut hp hpγ
  refine ⟨Real.toNNReal C, ?_⟩
  intro Ω _ P hCm hcirc μ hh hμ
  have := hh.isProbabilityMeasure
  have hnn : ∀ k : ℕ, 1 ≤ k + 1 := fun k => Nat.le_add_left 1 k
  calc ∫⁻ ω, (μ ω (ball (0 : ℂ) (1 / 4))) ^ p ∂P
      ≤ ∫⁻ ω, liminf (fun k : ℕ => (lqgApproxMass γ (hcirc ω) (fun x => ENNReal.ofReal (g x))
          (k + 1)) ^ p) atTop ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hμ, hh.ae_continuousOn_circle] with ω hω hcω
        refine pow_measure_ball_le_liminf (fun k => ?_) hω g.continuous hgc hgnn
          (fun x hx => by
            have := hg1 (ball_subset_closedBall hx)
            simp only [Pi.one_apply] at this
            exact this.ge) (by linarith)
        exact hcω.comp_continuous (continuous_const.prodMk continuous_id) fun z =>
          ⟨dyadicScale_pos' k, Set.mem_univ z⟩
    _ ≤ liminf (fun k : ℕ => ∫⁻ ω, (lqgApproxMass γ (hcirc ω) (fun x => ENNReal.ofReal (g x))
          (k + 1)) ^ p ∂P) atTop :=
        lintegral_liminf_le' fun k =>
          (IsWholePlaneGFF.aemeasurable_lqgApproxMass hh γ hcut.measurable hcut.eq_zero_of_not_mem
            (k + 1)).pow_const p
    _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal C) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall fun k => hC Ω P hCm hcirc hh (k + 1) (hnn k))
    _ = ((Real.toNNReal C : ℝ≥0) : ℝ≥0∞) := by rw [Filter.liminf_const]; rfl

end LatticeProb.LQG
