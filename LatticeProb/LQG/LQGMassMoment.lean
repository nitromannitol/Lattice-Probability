import Mathlib
import LatticeProb.LQG.LQGOnePieceMoment
import LatticeProb.LQG.LQGPieceDecouplingGMC

/-!
# Moments of the mass of a cutoff function against the approximate Liouville measure

Let `μ_n = lqgApprox γ h 2^{-n}` and let `f : ℂ → [0, ∞]` be measurable with `f ≤ 1`.

* `lintegral_rpow_le_measure_univ_mul`: Jensen's inequality `(∫ g dν)^p ≤ ν(univ)^{p-1} ∫ g^p dν`, `p ≥ 1`.
* `IsWholePlaneGFF.lintegral_rpow_mul_exp_circle`: `E[(ε^a e^{γ h_ε(x)})^p] = ε^{pa - p²γ²/2}` for `‖x‖ + ε ≤ 1`.
* `IsWholePlaneGFF.lintegral_rpow_setLIntegral_le`: for a set `S ⊆ B(z, R/4)`, `R = 2^{-k}`, `k < n`,
  `E[(∫_S f dμ_n)^p] ≤ R^{p(2+γ²/2) - p²γ²/2} E[(∫ f dμ'_{n-k})^p]`, `μ'` the approximation of the
  recentred and dilated circle averages (when `f ≥ 1` on `B(0, 1/4)`).
* `IsWholePlaneGFF.lintegral_rpow_lqgApproxMass_le`: for `f` supported in `closedBall 0 (1/2)` and `n ≥ 1`,
  `E[(∫ f dμ_n)^p] ≤ |B|^{p-1} |B| 2^{-n(pγ²/2 - p²γ²/2)}`, `B = closedBall 0 (1/2)` (a bound depending only on
  `n`, `p`, `γ`).
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace LatticeProb

/-- **Jensen's inequality** for a `[0, ∞]`-valued function: for `p ≥ 1`,
`(∫ g dν)^p ≤ ν(univ)^{p-1} ∫ g^p dν`. -/
theorem lintegral_rpow_le_measure_univ_mul {α : Type*} [MeasurableSpace α] (ν : Measure α) {p : ℝ}
    (hp : 1 ≤ p) {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) :
    (∫⁻ x, g x ∂ν) ^ p ≤ ν univ ^ (p - 1) * ∫⁻ x, g x ^ p ∂ν := by
  rcases hp.eq_or_lt with rfl | hp1
  · simp
  · have hpq := Real.HolderConjugate.conjExponent hp1
    set q := p.conjExponent
    have h : ∫⁻ x, g x ∂ν ≤ (∫⁻ x, g x ^ p ∂ν) ^ (1 / p) * ν univ ^ (1 / q) := by
      have := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hg (aemeasurable_const (b := (1 : ℝ≥0∞)))
      simpa using this
    have h1 := ENNReal.rpow_le_rpow h (by linarith : 0 ≤ p)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p), ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul] at h1
    have e1 : 1 / p * p = 1 := by field_simp
    have e2 : 1 / q * p = p - 1 := by
      have := hpq.inv_add_inv_eq_one
      field_simp
      field_simp at this
      linarith
    rw [e1, e2, ENNReal.rpow_one] at h1
    rw [mul_comm]
    exact h1

end LatticeProb

namespace LatticeProb.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Moment of the circle-average density.** For `p ≥ 0`, `ε > 0`, `‖x‖ + ε ≤ 1`,
`E[(ε^a e^{γ h_ε(x)})^p] = ε^{pa - p²γ²/2}`. -/
theorem IsWholePlaneGFF.lintegral_rpow_mul_exp_circle (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) {x : ℂ} (hx : ‖x‖ + ε ≤ 1) (a γ : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    ∫⁻ ω, (ENNReal.ofReal (ε ^ a * Real.exp (γ * hcirc ω ε x))) ^ p ∂P =
      ENNReal.ofReal (ε ^ (p * a - p ^ 2 * γ ^ 2 / 2)) := by
  have hpt : ∀ ω, (ENNReal.ofReal (ε ^ a * Real.exp (γ * hcirc ω ε x))) ^ p =
      ENNReal.ofReal (ε ^ (p * a)) *
        ENNReal.ofReal (Real.exp (p * γ * hcirc ω ε x)) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp, ← ENNReal.ofReal_mul (by positivity),
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hε.le, ← Real.exp_mul]
    congr 3
    all_goals ring
  simp_rw [hpt]
  have hm : Measurable fun ω => ENNReal.ofReal (Real.exp (p * γ * hcirc ω ε x)) :=
    Measurable.ennreal_ofReal (Real.measurable_exp.comp
      ((hh.measurable_circle ε x hε).const_mul _))
  rw [lintegral_const_mul _ hm]
  have hint := hh.integrable_exp_sum_circle hε (fun _ : Fin 1 => x) (fun _ => p * γ)
  have hexp := hh.integral_exp_sum_circle hε (fun _ : Fin 1 => x) (fun _ => p * γ)
  have hcov : cov[fun ω => hcirc ω ε x, fun ω => hcirc ω ε x; P] = -Real.log ε := by
    rw [hh.covariance_circle_inside hε hε hx hx, circlePairPotential_self_center hε.le, max_self]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hint hexp
  rw [hcov] at hexp
  have hl : ∫⁻ ω, ENNReal.ofReal (Real.exp (p * γ * hcirc ω ε x)) ∂P =
      ENNReal.ofReal (Real.exp (p * γ * (p * γ) * -Real.log ε / 2)) := by
    rw [← hexp, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  rw [hl, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_sub hε, Real.rpow_def_of_pos hε (p ^ 2 * γ ^ 2 / 2),
    div_eq_mul_inv (ε ^ _) (Real.exp _), ← Real.exp_neg]
  congr 2
  ring

end LatticeProb.Gauss

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The mass `∫ f dμ_n` of `f` against the approximate Liouville measure at the dyadic scale `2^{-n}`. -/
noncomputable def lqgApproxMass (γ : ℝ) (h : ℝ → ℂ → ℝ) (f : ℂ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, f x ∂(lqgApprox γ h (dyadicScale n))

/-- **One piece.** Let `S ⊆ B(z, R/4)`, `R = 2^{-k}`, `k < n`, `‖z‖ + R ≤ 1`, `p ≥ 0`, `f ≤ 1` and `f ≥ 1` on
`B(0, 1/4)`. Then `E[(∫_S f dμ_n)^p] ≤ R^{p(2+γ²/2) - p²γ²/2} E[(∫ f dμ'_{n-k})^p]`. -/
theorem IsWholePlaneGFF.lintegral_rpow_setLIntegral_le (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : γ ≠ 0) {p : ℝ} (hp : 0 ≤ p) {k n : ℕ} (hkn : k < n) {z : ℂ}
    (hz : ‖z‖ + dyadicScale k ≤ 1) {S : Set ℂ} (hS : S ⊆ ball z (dyadicScale k * (1 / 4)))
    {f : ℂ → ℝ≥0∞} (hf1 : ∀ x, f x ≤ 1) (hf14 : ∀ x ∈ ball (0 : ℂ) (1 / 4), 1 ≤ f x) :
    ∫⁻ ω, (∫⁻ x in S, f x ∂(lqgApprox γ (hcirc ω) (dyadicScale n))) ^ p ∂P ≤
      ENNReal.ofReal (dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) *
        ∫⁻ ω, (lqgApproxMass γ (recentredField hcirc k z ω) f (n - k)) ^ p ∂P := by
  calc ∫⁻ ω, (∫⁻ x in S, f x ∂(lqgApprox γ (hcirc ω) (dyadicScale n))) ^ p ∂P
      ≤ ∫⁻ ω, (lqgApprox γ (hcirc ω) (dyadicScale n)
          (ball z (dyadicScale k * (1 / 4)))) ^ p ∂P := by
        refine lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ hp
        calc ∫⁻ x in S, f x ∂(lqgApprox γ (hcirc ω) (dyadicScale n))
            ≤ ∫⁻ x in S, 1 ∂(lqgApprox γ (hcirc ω) (dyadicScale n)) := lintegral_mono hf1
          _ = lqgApprox γ (hcirc ω) (dyadicScale n) S := by simp
          _ ≤ _ := measure_mono hS
    _ = ENNReal.ofReal (dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) *
          ∫⁻ ω, (lqgApprox γ (recentredField hcirc k z ω) (dyadicScale (n - k))
            (ball 0 (1 / 4))) ^ p ∂P :=
        LatticeProb.LQG.IsWholePlaneGFF.lintegral_rpow_lqgApprox_ball_dyadic hh hγ hp hkn hz
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ hp)
        calc lqgApprox γ (recentredField hcirc k z ω) (dyadicScale (n - k)) (ball 0 (1 / 4))
            = ∫⁻ x in ball (0 : ℂ) (1 / 4), 1
                ∂(lqgApprox γ (recentredField hcirc k z ω) (dyadicScale (n - k))) := by simp
          _ ≤ ∫⁻ x in ball (0 : ℂ) (1 / 4), f x
                ∂(lqgApprox γ (recentredField hcirc k z ω) (dyadicScale (n - k))) :=
              setLIntegral_mono' measurableSet_ball hf14
          _ ≤ _ := setLIntegral_le_lintegral _ _

/-- **Fixed scale.** For `p ≥ 1`, `n ≥ 1` and `f` measurable, `f ≤ 1`, vanishing off `B = closedBall 0 (1/2)`,
`E[(∫ f dμ_n)^p] ≤ |B|^{p-1} |B| 2^{-n(pγ²/2 - p²γ²/2)}`. -/
theorem IsWholePlaneGFF.lintegral_rpow_lqgApproxMass_le [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {p : ℝ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n)
    {f : ℂ → ℝ≥0∞} (hfm : Measurable f) (hf1 : ∀ x, f x ≤ 1)
    (hf0 : ∀ x, x ∉ closedBall (0 : ℂ) (1 / 2) → f x = 0) :
    ∫⁻ ω, (lqgApproxMass γ (hcirc ω) f n) ^ p ∂P ≤
      volume (closedBall (0 : ℂ) (1 / 2)) ^ (p - 1) *
        (ENNReal.ofReal (dyadicScale n ^ (p * (γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) *
          volume (closedBall (0 : ℂ) (1 / 2))) := by
  classical
  have hε : 0 < dyadicScale n := dyadicScale_pos' n
  have hε2 : dyadicScale n ≤ 1 / 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [dyadicScale_succ_eq_half]
    have := dyadicScale_le_one' m
    linarith
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  set B := closedBall (0 : ℂ) (1 / 2) with hBdef
  have hB : MeasurableSet B := measurableSet_closedBall
  let dens : ℂ → Ω → ℝ≥0∞ := gmcDensityENN (fun z ω => H ω (dyadicScale n) z) γ (dyadicScale n)
  have hdensm : Measurable (Function.uncurry dens) :=
    measurable_uncurry_gmcDensityENN (hHm _ hε) γ _
  have hdensx : ∀ ω, Measurable (fun x => dens x ω) := fun ω =>
    hdensm.comp (measurable_id.prodMk measurable_const)
  have hstep : ∀ᵐ ω ∂P, lqgApproxMass γ (hcirc ω) f n ≤ ∫⁻ x in B, dens x ω := by
    filter_upwards [hHae] with ω hω
    have e : (fun z => ENNReal.ofReal (dyadicScale n ^ (γ ^ 2 / 2) *
        Real.exp (γ * hcirc ω (dyadicScale n) z))) = fun z => dens z ω := by
      funext z
      simp only [dens, gmcDensityENN, hω]
    unfold lqgApproxMass lqgApprox
    rw [e, lintegral_withDensity_eq_lintegral_mul _ (hdensx ω) hfm, ← lintegral_indicator hB]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ B
    · simpa [Set.indicator_of_mem hx] using mul_le_mul' (le_refl (dens x ω)) (hf1 x)
    · simp [Set.indicator_of_notMem hx, hf0 x hx]
  have hfin : volume B < ∞ := measure_closedBall_lt_top
  calc ∫⁻ ω, (lqgApproxMass γ (hcirc ω) f n) ^ p ∂P
      ≤ ∫⁻ ω, (∫⁻ x in B, dens x ω) ^ p ∂P :=
        lintegral_mono_ae (hstep.mono fun ω h => ENNReal.rpow_le_rpow h hp0)
    _ ≤ ∫⁻ ω, volume B ^ (p - 1) * (∫⁻ x in B, dens x ω ^ p) ∂P := by
        refine lintegral_mono fun ω => ?_
        have := LatticeProb.lintegral_rpow_le_measure_univ_mul (volume.restrict B) hp (hdensx ω).aemeasurable
        simpa [Measure.restrict_apply_univ] using this
    _ = volume B ^ (p - 1) * ∫⁻ ω, (∫⁻ x in B, dens x ω ^ p) ∂P := by
        rw [lintegral_const_mul]
        exact ((hdensm.pow_const p)).lintegral_prod_left'
    _ = volume B ^ (p - 1) * ∫⁻ x in B, (∫⁻ ω, dens x ω ^ p ∂P) := by
        rw [lintegral_lintegral_swap]
        exact ((hdensm.pow_const p).comp measurable_swap).aemeasurable
    _ = volume B ^ (p - 1) * ∫⁻ x in B,
          ENNReal.ofReal (dyadicScale n ^ (p * (γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) := by
        congr 1
        refine setLIntegral_congr_fun hB fun x hx => ?_
        have hxn : ‖x‖ + dyadicScale n ≤ 1 := by
          have := mem_closedBall_zero_iff.1 hx
          linarith
        rw [← hh.lintegral_rpow_mul_exp_circle hε hxn (γ ^ 2 / 2) γ hp0]
        refine lintegral_congr_ae (hHae.mono fun ω hω => ?_)
        simp only [dens, gmcDensityENN, hω]
    _ = _ := by rw [setLIntegral_const]

end LatticeProb.LQG
