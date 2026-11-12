import Mathlib
import LatticeProb.LQG.LQGMassFatou
import LatticeProb.LQG.LQGBallMassLowerTail
import LatticeProb.Prob.LaplaceNegMoment

/-!
# Negative moments of the Liouville mass from Laplace bounds on the approximations

Let `h` be a whole-plane Gaussian free field and `μ` its `γ`-Liouville measure, the almost sure vague limit
of the approximate Liouville measures `μ_n = lqgApprox γ h 2^{-n}`. Suppose that for a measurable set
`T ⊆ B̄(0, 1/4)` the Laplace transforms of the approximate masses `μ_n(T)` decay polynomially, uniformly in
`n ≥ 1` and in the probability space: `E exp(-t μ_n(T)) ≤ A t^{-a}` for every `t > 0`. Then for every
`0 < q < a` the negative moment `E μ(B(0,1))^{-q}` is bounded by a constant depending only on `A`, `a`, `q`.

The proof takes a continuous cut-off `g` with `1_{B̄(0,1/4)} ≤ g ≤ 1_{B(0,1/2)}`. Almost surely
`μ_n(T) ≤ ∫ g dμ_n → ∫ g dμ ≤ μ(B(0,1))` (vague convergence), so by dominated convergence the Laplace bound
passes to `∫ g dμ`, and the negative moments follow from the Laplace transform by the Gamma-function
identity `x^{-q} = Γ(q)^{-1} ∫_0^∞ t^{q-1} e^{-t x} dt`.

* `LatticeProb.LQG.ballMassNegMoment_of_laplace`: the passage to the limit, for one exponent.
* `LatticeProb.LQG.ballMassNegMoment_of_laplace_all`: if the Laplace bound holds with every exponent `a`,
  then `BallMassNegMoment γ q` holds for every `q > 0`.

This is the last step of the proof of the negative moments of Gaussian multiplicative chaos
(Kahane 1985; Robert-Vargas 2010; Rhodes-Vargas 2014, Thm. 2.12).
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling LatticeProb

/-- **Negative moments of the Liouville mass from Laplace bounds on the approximations.** Let
`T ⊆ B̄(0, 1/4)` be measurable, `A ≥ 0` and `0 < q < a`. If `E exp(-t μ_n(T)) ≤ A t^{-a}` for every `t > 0`,
every `n ≥ 1` and every whole-plane Gaussian free field on a probability space of the universe `u`, then
`E μ(B(0,1))^{-q} ≤ Γ(q)^{-1} (1/q + A/(a-q))` for the `γ`-Liouville measure `μ` of every such field. -/
theorem ballMassNegMoment_of_laplace.{u} {γ a A q : ℝ} {T : Set ℂ} (hT : MeasurableSet T)
    (hTB : T ⊆ closedBall (0 : ℂ) (1 / 4)) (hA : 0 ≤ A) (hq : 0 < q) (hqa : q < a)
    (hL : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ n : ℕ, 1 ≤ n → ∀ lam : ℝ, 0 < lam →
        ∫ ω, Real.exp (-(lam * (lqgApproxMass γ (hcirc ω) (T.indicator 1) n).toReal)) ∂P ≤
          A * lam ^ (-a)) :
    BallMassNegMoment.{u} γ q := by
  classical
  obtain ⟨g, hg1, hg0, hgc, hgI⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall (0 : ℂ) (1 / 4)) (isOpen_ball (x := (0 : ℂ)) (ε := 1 / 2)).isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 (closedBall_subset_ball (by norm_num)))
  have hgnn : ∀ x, 0 ≤ g x := fun x => (hgI x).1
  have hgle : ∀ x, g x ≤ 1 := fun x => (hgI x).2
  have hgout : ∀ x, x ∉ ball (0 : ℂ) (1 / 2) → g x = 0 := fun x hx => by
    have := hg0 (show x ∈ (ball (0 : ℂ) (1 / 2))ᶜ from hx)
    simpa using this
  have hgm : Measurable fun x => ENNReal.ofReal (g x) :=
    ENNReal.measurable_ofReal.comp g.continuous.measurable
  have hgsupp : ∀ x ∉ closedBall (0 : ℂ) (1 / 2), ENNReal.ofReal (g x) = 0 := fun x hx => by
    rw [hgout x fun h => hx (ball_subset_closedBall h)]
    simp
  have hTm : Measurable (T.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hT
  have hTsupp : ∀ x ∉ closedBall (0 : ℂ) (1 / 2), T.indicator (1 : ℂ → ℝ≥0∞) x = 0 := fun x hx => by
    refine Set.indicator_of_notMem (fun hxT => hx ?_) _
    exact closedBall_subset_closedBall (by norm_num) (hTB hxT)
  have hTg : ∀ x, T.indicator (1 : ℂ → ℝ≥0∞) x ≤ ENNReal.ofReal (g x) := by
    intro x
    by_cases hx : x ∈ T
    · have h1 := hg1 (hTB hx)
      simp only [Pi.one_apply] at h1
      simp [Set.indicator_of_mem hx, h1]
    · simp [Set.indicator_of_notMem hx]
  refine ⟨Real.toNNReal ((Real.Gamma q)⁻¹ * (1 / q + A / (a - q))), ?_⟩
  intro Ω _ P hCm hcirc μ hh hμ
  have := hh.isProbabilityMeasure
  -- the approximate masses of `g` and of `T`, and the limit mass of `g`
  set M : ℕ → Ω → ℝ≥0∞ := fun n ω => lqgApproxMass γ (hcirc ω) (fun x => ENNReal.ofReal (g x)) n
    with hMdef
  set Z : ℕ → Ω → ℝ≥0∞ := fun n ω => lqgApproxMass γ (hcirc ω) (T.indicator 1) n with hZdef
  set F : Ω → ℝ := fun ω => ∫ x, g x ∂(μ ω) with hFdef
  have hMm : ∀ n, AEMeasurable (M n) P := fun n => IsWholePlaneGFF.aemeasurable_lqgApproxMass hh γ hgm hgsupp n
  have hZm : ∀ n, AEMeasurable (Z n) P := fun n => IsWholePlaneGFF.aemeasurable_lqgApproxMass hh γ hTm hTsupp n
  have hZM : ∀ n ω, Z n ω ≤ M n ω := fun n ω => lintegral_mono hTg
  have hgood : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) ∧
      ∀ k : ℕ, Continuous (hcirc ω (dyadicScale k)) := by
    filter_upwards [hμ, hh.ae_continuousOn_circle] with ω hω hcω
    exact ⟨hω, fun k => hcω.comp_continuous (continuous_const.prodMk continuous_id) fun z =>
      ⟨dyadicScale_pos' k, Set.mem_univ z⟩⟩
  have hMeq : ∀ᵐ ω ∂P, ∀ n, M n ω =
      ENNReal.ofReal (∫ x, g x ∂(lqgApprox γ (hcirc ω) (dyadicScale n))) := by
    filter_upwards [hgood] with ω hω n
    have := isLocallyFiniteMeasure_lqgApprox_of_continuous γ (hω.2 n)
    exact lintegral_ofReal_eq_ofReal_integral_of_hasCompactSupport g.continuous hgc hgnn
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => (M n ω).toReal) atTop (𝓝 (F ω)) := by
    filter_upwards [hgood, hMeq] with ω hω hMω
    have hnn : ∀ n, 0 ≤ ∫ x, g x ∂(lqgApprox γ (hcirc ω) (dyadicScale n)) :=
      fun n => integral_nonneg hgnn
    simp_rw [hMω, ENNReal.toReal_ofReal (hnn _)]
    exact hω.1.tendsto_integral g g.continuous hgc
  have hFm : AEMeasurable F P :=
    aemeasurable_of_tendsto_metrizable_ae' (fun n => (hMm n).ennreal_toReal) hlim
  -- every `exp(-t X)` with `X ≥ 0` is bounded by `1`
  have hexp_le : ∀ t X : ℝ, 0 < t → 0 ≤ X → ‖Real.exp (-(t * X))‖ ≤ 1 := fun t X ht hX => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg ht.le hX
  have hint : ∀ t : ℝ, 0 < t → ∀ X : Ω → ℝ, AEMeasurable X P → (∀ ω, 0 ≤ X ω) →
      Integrable (fun ω => Real.exp (-(t * X ω))) P := fun t ht X hX hX0 =>
    Integrable.of_bound
      (Real.measurable_exp.comp_aemeasurable (hX.const_mul t).neg).aestronglyMeasurable 1
      (ae_of_all _ fun ω => hexp_le t (X ω) ht (hX0 ω))
  -- the Laplace bound passes to the limit mass `∫ g dμ`
  have hLF : ∀ t : ℝ, 0 < t → ∫ ω, Real.exp (-(t * F ω)) ∂P ≤ A * t ^ (-a) := by
    intro t ht
    have hconv : Tendsto (fun n => ∫ ω, Real.exp (-(t * (M (n + 1) ω).toReal)) ∂P) atTop
        (𝓝 (∫ ω, Real.exp (-(t * F ω)) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => ?_)
        (integrable_const 1) (fun n => ae_of_all _ fun ω => hexp_le t _ ht ENNReal.toReal_nonneg) ?_
      · exact (Real.measurable_exp.comp_aemeasurable
          ((hMm (n + 1)).ennreal_toReal.const_mul t).neg).aestronglyMeasurable
      · filter_upwards [hlim] with ω hω
        exact (Real.continuous_exp.tendsto _).comp
          (((hω.comp (tendsto_add_atTop_nat 1)).const_mul t).neg)
    refine le_of_tendsto' hconv fun n => ?_
    refine le_trans (integral_mono_ae (hint t ht _ (hMm (n + 1)).ennreal_toReal
      fun ω => ENNReal.toReal_nonneg) (hint t ht _ (hZm (n + 1)).ennreal_toReal
      fun ω => ENNReal.toReal_nonneg) ?_) (hL Ω P hCm hcirc hh (n + 1) (Nat.le_add_left 1 n) t ht)
    filter_upwards [hMeq] with ω hMω
    have hfin : M (n + 1) ω ≠ ∞ := by rw [hMω]; exact ENNReal.ofReal_ne_top
    refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ ht.le))
    exact ENNReal.toReal_mono hfin (hZM (n + 1) ω)
  -- a measurable nonnegative version of `∫ g dμ`
  set Y : Ω → ℝ := fun ω => max (hFm.mk F ω) 0 with hYdef
  have hYm : Measurable Y := hFm.measurable_mk.max measurable_const
  have hYF : ∀ᵐ ω ∂P, Y ω = F ω := by
    filter_upwards [hFm.ae_eq_mk] with ω hω
    simp only [hYdef, ← hω]
    exact max_eq_left (integral_nonneg hgnn)
  have hLY : ∀ t : ℝ, 0 < t → ∫ ω, Real.exp (-(t * Y ω)) ∂P ≤ A * t ^ (-a) := by
    intro t ht
    rw [integral_congr_ae (hYF.mono fun ω hω => by
      show Real.exp (-(t * Y ω)) = Real.exp (-(t * F ω)); rw [hω])]
    exact hLF t ht
  have hI3 := lintegral_rpow_neg_le_of_laplace_le hYm (fun ω => le_max_right _ _) hq hqa hA hLY
  calc ∫⁻ ω, (μ ω (ball (0 : ℂ) 1)) ^ (-q) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Y ω) ^ (-q) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgood, hYF] with ω hω hYω
        have := hω.1.isLocallyFiniteMeasure
        have hle : ENNReal.ofReal (Y ω) ≤ μ ω (ball (0 : ℂ) 1) := by
          rw [hYω, hFdef, ← lintegral_ofReal_eq_ofReal_integral_of_hasCompactSupport g.continuous hgc
            hgnn, ← lintegral_indicator_one measurableSet_ball]
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ ball (0 : ℂ) 1
          · rw [Set.indicator_of_mem hx, Pi.one_apply]
            exact ENNReal.ofReal_le_one.2 (hgle x)
          · have hx' : x ∉ ball (0 : ℂ) (1 / 2) := fun h => hx (ball_subset_ball (by norm_num) h)
            simp [hgout x hx']
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hle hq.le)
    _ ≤ ENNReal.ofReal ((Real.Gamma q)⁻¹ * (1 / q + A / (a - q))) := hI3
    _ = ((Real.toNNReal ((Real.Gamma q)⁻¹ * (1 / q + A / (a - q))) : ℝ≥0) : ℝ≥0∞) := rfl

/-- **Negative moments of every order.** If for every `a > 0` there is `A ≥ 0` with
`E exp(-t μ_n(T)) ≤ A t^{-a}` for every `t > 0`, every `n ≥ 1` and every whole-plane Gaussian free field on a
probability space of the universe `u` (with `T ⊆ B̄(0, 1/4)` measurable), then `E μ(B(0,1))^{-q}` is bounded
uniformly in the field for every `q > 0`. -/
theorem ballMassNegMoment_of_laplace_all.{u} {γ : ℝ} {T : Set ℂ} (hT : MeasurableSet T)
    (hTB : T ⊆ closedBall (0 : ℂ) (1 / 4))
    (hL : ∀ a : ℝ, 0 < a → ∃ A : ℝ, 0 ≤ A ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        ∀ n : ℕ, 1 ≤ n → ∀ lam : ℝ, 0 < lam →
          ∫ ω, Real.exp (-(lam * (lqgApproxMass γ (hcirc ω) (T.indicator 1) n).toReal)) ∂P ≤
            A * lam ^ (-a))
    {q : ℝ} (hq : 0 < q) : BallMassNegMoment.{u} γ q := by
  obtain ⟨A, hA, hLA⟩ := hL (q + 1) (by linarith)
  exact ballMassNegMoment_of_laplace hT hTB hA hq (by linarith) hLA

end LatticeProb.LQG
