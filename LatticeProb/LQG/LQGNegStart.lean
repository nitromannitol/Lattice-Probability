import Mathlib
import LatticeProb.LQG.LQGMassInduction
import LatticeProb.LQG.LQGMassFatou
import LatticeProb.Prob.LaplaceOfMoments

/-!
# First moment of the mass and a uniform Laplace-transform bound

* `IsWholePlaneGFF.lintegral_lqgApproxMass_eq`: for `f ≥ 0` measurable and vanishing off `closedBall 0 (1/2)`
  and `n ≥ 1`, `E ∫ f dμ_n = ∫ f` (Lebesgue measure), `μ_n` the approximation at scale `2^{-n}`.
* `exists_laplace_uniform_bound`: for a measurable `T ⊆ closedBall 0 (1/2)` of positive volume, `γ ≠ 0`,
  `γ² < 4`, there are `η, λ > 0` such that `E exp(-λ μ_n(T)) ≤ 1 - η/2` for every `n ≥ 1` and every model
  of the whole-plane Gaussian free field in the universe `u` (Paley-Zygmund with the uniform moment bound).
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **First moment of the mass.** For `f` measurable, vanishing off `B(0, 1/2)`, and `n ≥ 1`,
`E ∫ f dμ_n = ∫ f dx`. -/
theorem IsWholePlaneGFF.lintegral_lqgApproxMass_eq [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {n : ℕ} (hn : 1 ≤ n)
    {f : ℂ → ℝ≥0∞} (hfm : Measurable f)
    (hf0 : ∀ x, x ∉ closedBall (0 : ℂ) (1 / 2) → f x = 0) :
    ∫⁻ ω, lqgApproxMass γ (hcirc ω) f n ∂P = ∫⁻ x, f x := by
  classical
  have hε : 0 < dyadicScale n := dyadicScale_pos' n
  have hε2 : dyadicScale n ≤ 1 / 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [dyadicScale_succ_eq_half]
    have := dyadicScale_le_one' m
    linarith
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  set B := closedBall (0 : ℂ) (1 / 2) with hBdef
  let dens : ℂ → Ω → ℝ≥0∞ := gmcDensityENN (fun z ω => H ω (dyadicScale n) z) γ (dyadicScale n)
  have hdensm : Measurable (Function.uncurry dens) :=
    measurable_uncurry_gmcDensityENN (hHm _ hε) γ _
  have hdensx : ∀ ω, Measurable (fun x => dens x ω) := fun ω =>
    hdensm.comp (measurable_id.prodMk measurable_const)
  have hdensω : ∀ x, Measurable (fun ω => dens x ω) := fun x =>
    hdensm.comp (measurable_const.prodMk measurable_id)
  have hstep : ∀ᵐ ω ∂P, lqgApproxMass γ (hcirc ω) f n = ∫⁻ x, dens x ω * f x := by
    filter_upwards [hHae] with ω hω
    have e : (fun z => ENNReal.ofReal (dyadicScale n ^ (γ ^ 2 / 2) *
        Real.exp (γ * hcirc ω (dyadicScale n) z))) = fun z => dens z ω := by
      funext z
      simp only [dens, gmcDensityENN, hω]
    unfold lqgApproxMass lqgApprox
    rw [e, lintegral_withDensity_eq_lintegral_mul _ (hdensx ω) hfm]
    rfl
  have hE : ∀ x ∈ B, ∫⁻ ω, dens x ω ∂P = 1 := by
    intro x hx
    have hxn : ‖x‖ + dyadicScale n ≤ 1 := by
      have := mem_closedBall_zero_iff.1 hx
      linarith
    have h1 := hh.lintegral_rpow_mul_exp_circle hε hxn (γ ^ 2 / 2) γ (p := 1) zero_le_one
    have h0 : (1 : ℝ) * (γ ^ 2 / 2) - 1 ^ 2 * γ ^ 2 / 2 = 0 := by ring
    rw [h0, Real.rpow_zero, ENNReal.ofReal_one] at h1
    simp only [ENNReal.rpow_one] at h1
    rw [← h1]
    refine lintegral_congr_ae (hHae.mono fun ω hω => ?_)
    simp only [dens, gmcDensityENN, hω]
  calc ∫⁻ ω, lqgApproxMass γ (hcirc ω) f n ∂P = ∫⁻ ω, (∫⁻ x, dens x ω * f x) ∂P :=
        lintegral_congr_ae hstep
    _ = ∫⁻ x, ∫⁻ ω, dens x ω * f x ∂P := by
        rw [lintegral_lintegral_swap]
        exact ((hdensm.comp measurable_swap).mul (hfm.comp measurable_snd)).aemeasurable
    _ = ∫⁻ x, f x := by
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ B
        · rw [lintegral_mul_const _ (hdensω x), hE x hx, one_mul]
        · simp [hf0 x hx]

/-- **A uniform bound on the Laplace transform of the mass of a set.** Let `γ ≠ 0`, `γ² < 4` and let
`T ⊆ B(0, 1/2)` be measurable of positive volume. There are `η, λ > 0` such that
`E exp(-λ μ_n(T)) ≤ 1 - η/2` for all `n ≥ 1` and all models of the whole-plane Gaussian free field. -/
theorem exists_laplace_uniform_bound.{u} {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 4) {T : Set ℂ}
    (hT : MeasurableSet T) (hTB : T ⊆ closedBall (0 : ℂ) (1 / 2)) (hT0 : 0 < volume T) :
    ∃ η lam : ℝ, 0 < η ∧ 0 < lam ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        ∀ n : ℕ, 1 ≤ n →
          ∫ ω, Real.exp (-(lam * (lqgApproxMass γ (hcirc ω) (T.indicator 1) n).toReal)) ∂P ≤
            1 - η / 2 := by
  have hγpos : 0 < γ ^ 2 := by positivity
  set B : Set ℂ := closedBall (0 : ℂ) (1 / 2) with hBdef
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hcut : IsCutoffFn (B.indicator 1) :=
    { measurable := measurable_one.indicator hBm
      le_one := fun x => by
        by_cases hx : x ∈ B <;> simp [hx]
      one_le_of_mem := fun x hx => by
        have : x ∈ B := ball_subset_closedBall (ball_subset_ball (by norm_num) hx)
        simp [this]
      eq_zero_of_not_mem := fun x hx => Set.indicator_of_notMem hx _ }
  set p : ℝ := (1 + 4 / γ ^ 2) / 2 with hpdef
  have hp1 : 1 < p := by
    have : 1 < 4 / γ ^ 2 := by rw [lt_div_iff₀ hγpos]; linarith
    rw [hpdef]; linarith
  have hpγ : p * γ ^ 2 < 4 := by
    have : p * γ ^ 2 = (γ ^ 2 + 4) / 2 := by rw [hpdef]; field_simp
    rw [this]; linarith
  obtain ⟨C, hCb⟩ := exists_massMomentBound.{u} hγ hcut hp1.le hpγ
  have hCb' := hCb.mono (le_max_left C 1)
  have hC0 : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right C 1)
  have hvolfin : volume T < ⊤ := lt_of_le_of_lt (measure_mono hTB) measure_closedBall_lt_top
  set m : ℝ := (volume T).toReal with hmdef
  have hm : 0 < m := ENNReal.toReal_pos hT0.ne' hvolfin.ne
  refine ⟨(m / 2) ^ (p / (p - 1)) * (max C 1) ^ (-(1 / (p - 1))), 2 * Real.log 2 / m, by positivity,
    by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity, ?_⟩
  intro Ω _ P _ hC hcirc hh n hn
  have hIm : Measurable (T.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hT
  have hI0 : ∀ x, x ∉ B → T.indicator (1 : ℂ → ℝ≥0∞) x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => hx (hTB h)) _
  refine laplace_le_of_moments (Z := fun ω => lqgApproxMass γ (hcirc ω) (T.indicator 1) n)
    (IsWholePlaneGFF.aemeasurable_lqgApproxMass hh γ hIm hI0 n) hm hp1 hC0 ?_ ?_ le_rfl
  · rw [IsWholePlaneGFF.lintegral_lqgApproxMass_eq hh γ hn hIm hI0, lintegral_indicator_one hT,
      hmdef, ENNReal.ofReal_toReal hvolfin.ne]
  · refine le_trans (lintegral_mono fun ω => ?_) (hCb' Ω P hC hcirc hh n hn)
    refine ENNReal.rpow_le_rpow ?_ (by linarith)
    unfold lqgApproxMass
    refine lintegral_mono fun x => ?_
    exact Set.indicator_le_indicator_of_subset hTB (fun _ => zero_le) x

end LatticeProb.LQG
