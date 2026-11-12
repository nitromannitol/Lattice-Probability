import Mathlib
import LatticeProb.LQG.GMCAffineCovariance

/-!
# Vague limits of the LQG approximations: splitting off the origin

Let `m` be the dyadic vague limit of the approximations `lqgApprox γ h (2^{-k})` of a γ-LQG measure. For another
scale sequence `s k → 0`, the convergence of `∫ f d(lqgApprox γ h (s k))` to `∫ f dm` for every continuous compactly
supported `f` follows from

* the same convergence for the test functions `f` whose support stays away from the origin, and
* *origin non-concentration*: for every `η > 0` there is `δ > 0` such that the approximations at every small scale
  give mass at most `η` to the disc `B_δ(0)`.

This is the pathwise step that separates the analysis away from a log singularity at the origin (where the field is
locally absolutely continuous with respect to a whole-plane GFF) from the non-concentration estimate at the origin.

## Main results

* `OriginNonConcentration γ h`: the approximations do not concentrate at the origin.
* `integral_le_toReal_measure_ball`: a continuous `χ` with `0 ≤ χ ≤ 1`, vanishing off `B_δ(0)`, has integral at most
  the mass of `B_δ(0)`, when that mass is finite.
* `integral_bump_le_of_isLQGLimit`: under origin non-concentration, such a `χ` has integral at most `η` against the
  dyadic limit.
* `isLQGLimitAlong_of_tendsto_off_origin`: the vague limit along `s` from the off-origin limit and non-concentration.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace LatticeProb.LQG

/-- **Origin non-concentration** of the approximations of the γ-LQG measure: for every `η > 0` there are `δ > 0` and
`ε₀ > 0` such that `lqgApprox γ h ε (B_δ(0)) ≤ η` for every scale `ε ∈ (0, ε₀)`. -/
def OriginNonConcentration (γ : ℝ) (h : ℝ → ℂ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε ∈ Ioo (0 : ℝ) ε₀, lqgApprox γ h ε (ball 0 δ) ≤ ENNReal.ofReal η

/-- A continuous function with values in `[0, 1]` which vanishes off the disc `B_δ(0)` is integrable, with integral
at most the mass of the disc, for any measure giving the disc finite mass. -/
theorem integral_le_toReal_measure_ball {ν : Measure ℂ} {χ : ℂ → ℝ} {δ : ℝ} (hχ : Continuous χ)
    (h0 : ∀ z, 0 ≤ χ z) (h1 : ∀ z, χ z ≤ 1) (hout : ∀ z, δ ≤ ‖z‖ → χ z = 0)
    (hfin : ν (ball 0 δ) < ∞) :
    Integrable χ ν ∧ ∫ z, χ z ∂ν ≤ (ν (ball 0 δ)).toReal := by
  have hle : ∀ z, χ z ≤ (ball (0 : ℂ) δ).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ ball (0 : ℂ) δ
    · rw [indicator_of_mem hz]; exact h1 z
    · rw [indicator_of_notMem hz]
      have : δ ≤ ‖z‖ := by
        rw [mem_ball, dist_zero_right, not_lt] at hz; exact hz
      exact (hout z this).le
  have hind : Integrable ((ball (0 : ℂ) δ).indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const hfin.ne)
  have hint : Integrable χ ν :=
    hind.mono' hχ.aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 z)]; exact hle z)
  refine ⟨hint, ?_⟩
  calc ∫ z, χ z ∂ν ≤ ∫ z, (ball (0 : ℂ) δ).indicator (fun _ => (1 : ℝ)) z ∂ν :=
        integral_mono hint hind hle
    _ = (ν (ball 0 δ)).toReal := by
        have := integral_indicator_one (μ := ν) (measurableSet_ball (x := (0 : ℂ)) (ε := δ))
        simpa [Pi.one_def, measureReal_def] using this

private theorem dyadicScale_tendsto_nhdsGT : Tendsto dyadicScale atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
  · show Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · show (0 : ℝ) < (2 : ℝ)⁻¹ ^ k
    exact pow_pos (by norm_num) k

/-- Under origin non-concentration, a continuous `χ` with values in `[0, 1]` vanishing off `B_δ(0)` has integral at
most `η` against the dyadic vague limit `m`, where `δ` is the radius given for `η`. -/
theorem integral_bump_le_of_isLQGLimit {γ : ℝ} {h : ℝ → ℂ → ℝ} {m : Measure ℂ} (hm : IsLQGLimit γ h m)
    {χ : ℂ → ℝ} {δ ε₀ η : ℝ} (hε₀ : 0 < ε₀)
    (hball : ∀ ε ∈ Ioo (0 : ℝ) ε₀, lqgApprox γ h ε (ball 0 δ) ≤ ENNReal.ofReal η) (hη : 0 ≤ η)
    (hχ : Continuous χ) (h0 : ∀ z, 0 ≤ χ z) (h1 : ∀ z, χ z ≤ 1) (hout : ∀ z, δ ≤ ‖z‖ → χ z = 0) :
    ∫ z, χ z ∂m ≤ η := by
  have hcs : HasCompactSupport χ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) δ) fun z hz => by
      rw [mem_closedBall, dist_zero_right, not_le] at hz
      exact hout z hz.le
  have hlim := hm.tendsto_integral χ hχ hcs
  have hsmall : ∀ᶠ k in atTop, dyadicScale k ∈ Ioo (0 : ℝ) ε₀ :=
    dyadicScale_tendsto_nhdsGT.eventually (Ioo_mem_nhdsGT hε₀)
  refine le_of_tendsto hlim (hsmall.mono fun k hk => ?_)
  have hb := hball _ hk
  have hfin : lqgApprox γ h (dyadicScale k) (ball 0 δ) < ∞ := hb.trans_lt ENNReal.ofReal_lt_top
  exact (integral_le_toReal_measure_ball hχ h0 h1 hout hfin).2.trans (ENNReal.toReal_le_of_le_ofReal hη hb)

/-- **Vague limit along a scale sequence from the limit off the origin.** Let `m` be the dyadic vague limit of the
approximations of `h`, which do not concentrate at the origin. Let `s k → 0` be positive scales at which the
approximations are locally finite. If `∫ f d(lqgApprox γ h (s k)) → ∫ f dm` for every continuous compactly supported
`f` vanishing near the origin, then the approximations converge vaguely to `m` along `s`. -/
theorem isLQGLimitAlong_of_tendsto_off_origin {γ : ℝ} {h : ℝ → ℂ → ℝ} {m : Measure ℂ} {s : ℕ → ℝ}
    (hm : IsLQGLimit γ h m) (hON : OriginNonConcentration γ h) (hs0 : ∀ k, 0 < s k)
    (hs : Tendsto s atTop (𝓝 0)) (hloc : ∀ k, IsLocallyFiniteMeasure (lqgApprox γ h (s k)))
    (hoff : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (0 : ℂ) ∉ tsupport f →
      Tendsto (fun k => ∫ z, f z ∂(lqgApprox γ h (s k))) atTop (𝓝 (∫ z, f z ∂m))) :
    IsLQGLimitAlong γ h s m := by
  have := hm.isLocallyFiniteMeasure
  refine ⟨hm.isLocallyFiniteMeasure, fun f hf hfc => ?_⟩
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (4 * (|C| + 1)) with hη_def
  have hC1 : 0 < |C| + 1 := by positivity
  have hη : 0 < η := by positivity
  have hCη : |C| * η ≤ ε / 4 := by
    rw [hη_def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg C]
  obtain ⟨δ, hδ, ε₀, hε₀, hball⟩ := hON η hη
  -- the cutoff `χ`: equal to `1` on `B_{δ/4}(0)`, vanishing off `B_{δ/2}(0)`
  set χ : ℂ → ℝ := fun z => max 0 (min 1 (2 - 4 * ‖z‖ / δ)) with hχ_def
  have hχc : Continuous χ := by
    refine continuous_const.max (continuous_const.min ?_)
    exact continuous_const.sub ((continuous_const.mul continuous_norm).div_const _)
  have hχ0 : ∀ z, 0 ≤ χ z := fun z => le_max_left _ _
  have hχ1 : ∀ z, χ z ≤ 1 := fun z => max_le zero_le_one (min_le_left _ _)
  have hχout : ∀ z, δ ≤ ‖z‖ → χ z = 0 := by
    intro z hz
    have : 2 - 4 * ‖z‖ / δ ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hδ]; nlinarith
    simp only [hχ_def]
    exact max_eq_left ((min_le_right _ _).trans this)
  have hχin : ∀ z, ‖z‖ < δ / 4 → χ z = 1 := by
    intro z hz
    have : 1 ≤ 2 - 4 * ‖z‖ / δ := by
      have : 4 * ‖z‖ / δ < 1 := by rw [div_lt_one hδ]; linarith
      linarith
    simp only [hχ_def, min_eq_left this, max_eq_right zero_le_one]
  have hχcs : HasCompactSupport χ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) δ) fun z hz => by
      rw [mem_closedBall, dist_zero_right, not_le] at hz
      exact hχout z hz.le
  -- the split `f = f (1 - χ) + f χ`
  set f₁ : ℂ → ℝ := fun z => f z * (1 - χ z) with hf₁_def
  set f₂ : ℂ → ℝ := fun z => f z * χ z with hf₂_def
  have hf₁c : Continuous f₁ := hf.mul (continuous_const.sub hχc)
  have hf₂c : Continuous f₂ := hf.mul hχc
  have hf₁cs : HasCompactSupport f₁ := hfc.mul_right
  have hf₂cs : HasCompactSupport f₂ := hfc.mul_right
  have hf₁0 : (0 : ℂ) ∉ tsupport f₁ := by
    have hsub : tsupport f₁ ⊆ {z : ℂ | δ / 4 ≤ ‖z‖} := by
      refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
      intro z hz
      by_contra hlt
      rw [mem_ofPred_eq, not_le] at hlt
      exact hz (by simp only [hf₁_def, hχin z hlt, sub_self, mul_zero])
    intro h0
    have := hsub h0
    rw [mem_ofPred_eq, norm_zero] at this
    linarith
  have hsplit : ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
      ∫ z, f z ∂ν = ∫ z, f₁ z ∂ν + ∫ z, f₂ z ∂ν := by
    intro ν hν
    rw [← integral_add (hf₁c.integrable_of_hasCompactSupport hf₁cs)
      (hf₂c.integrable_of_hasCompactSupport hf₂cs)]
    congr 1
    ext z
    simp only [hf₁_def, hf₂_def]
    ring
  -- the `χ` part is small for both measures
  have hbound : ∀ ν : Measure ℂ, Integrable χ ν → ∫ z, χ z ∂ν ≤ η →
      |∫ z, f₂ z ∂ν| ≤ ε / 4 := by
    intro ν hint hle
    have h2 : ‖∫ z, f₂ z ∂ν‖ ≤ ∫ z, |C| * χ z ∂ν := by
      refine norm_integral_le_of_norm_le (hint.const_mul _) (ae_of_all _ fun z => ?_)
      simp only [hf₂_def, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 z)]
      exact mul_le_mul_of_nonneg_right ((hC z).trans (le_abs_self C)) (hχ0 z)
    rw [integral_const_mul] at h2
    rw [← Real.norm_eq_abs]
    calc ‖∫ z, f₂ z ∂ν‖ ≤ |C| * ∫ z, χ z ∂ν := h2
      _ ≤ |C| * η := mul_le_mul_of_nonneg_left hle (abs_nonneg C)
      _ ≤ ε / 4 := hCη
  have hm2 : |∫ z, f₂ z ∂m| ≤ ε / 4 :=
    hbound m (hχc.integrable_of_hasCompactSupport hχcs)
      (integral_bump_le_of_isLQGLimit hm hε₀ hball hη.le hχc hχ0 hχ1 hχout)
  -- choose the index
  have hsmall : ∀ᶠ k in atTop, s k ∈ Ioo (0 : ℝ) ε₀ :=
    (hs.eventually (gt_mem_nhds hε₀)).mono fun k hk => ⟨hs0 k, hk⟩
  have h1lim := Metric.tendsto_atTop.1 (hoff f₁ hf₁c hf₁cs hf₁0) (ε / 4) (by positivity)
  obtain ⟨N₁, hN₁⟩ := h1lim
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hsmall
  refine ⟨max N₁ N₂, fun k hk => ?_⟩
  have hk₁ := hN₁ k (le_of_max_le_left hk)
  have hk₂ := hN₂ k (le_of_max_le_right hk)
  have hb := hball _ hk₂
  have hfin : lqgApprox γ h (s k) (ball 0 δ) < ∞ := hb.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨hint, hle⟩ := integral_le_toReal_measure_ball hχc hχ0 hχ1 hχout hfin
  have hk2 : |∫ z, f₂ z ∂(lqgApprox γ h (s k))| ≤ ε / 4 :=
    hbound _ hint (hle.trans (ENNReal.toReal_le_of_le_ofReal hη.le hb))
  rw [Real.dist_eq] at hk₁ ⊢
  rw [hsplit _ (hloc k), hsplit m hm.isLocallyFiniteMeasure]
  obtain ⟨a1, a2⟩ := abs_lt.1 hk₁
  obtain ⟨b1, b2⟩ := abs_le.1 hk2
  obtain ⟨c1, c2⟩ := abs_le.1 hm2
  rw [abs_lt]
  constructor <;> linarith

end LatticeProb.LQG
