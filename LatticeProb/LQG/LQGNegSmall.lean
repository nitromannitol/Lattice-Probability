import Mathlib
import LatticeProb.LQG.LQGNegStart
import LatticeProb.Prob.NegativeMomentMean

/-!
# Negative moments of the approximate mass at a fixed scale, and the small-scale Laplace bound

* `IsWholePlaneGFF.lintegral_density_rpow_neg`: `E[(ε^{γ²/2} e^{γ h_ε(x)})^{-r}] = ε^{-rγ²/2 - r²γ²/2}`.
* `IsWholePlaneGFF.lintegral_rpow_neg_lqgApproxMass_le`: for a measurable `T ⊆ B(0, 1/2)` of positive
  volume and `n ≥ 1`, `E[μ_n(T)^{-r}] ≤ |T|^{-r} (2^{-n})^{-rγ²/2 - r²γ²/2}`.
* `exists_laplace_small_scale_bound`: for `n ≤ k'` the Laplace transform of `μ_n(T)` decays like
  `λ^{-q}`, with a constant depending only on `γ, T, k', q`.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Negative moments of the density.** For `‖x‖ + ε ≤ 1` and `r > 0`,
`E[(ε^{γ²/2} e^{γ h_ε(x)})^{-r}] = ε^{-rγ²/2 - r²γ²/2}`. -/
theorem IsWholePlaneGFF.lintegral_density_rpow_neg (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) {x : ℂ} (hx : ‖x‖ + ε ≤ 1) (γ : ℝ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ ω, (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε x))) ^ (-r) ∂P =
      ENNReal.ofReal (ε ^ (-(r * γ ^ 2 / 2) - r ^ 2 * γ ^ 2 / 2)) := by
  have hpt : ∀ ω, (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε x))) ^ (-r) =
      (ENNReal.ofReal (ε ^ (-(γ ^ 2 / 2)) * Real.exp ((-γ) * hcirc ω ε x))) ^ r := by
    intro ω
    have hu : 0 < ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε x) := by positivity
    rw [ENNReal.rpow_neg, ← ENNReal.inv_rpow, ← ENNReal.ofReal_inv_of_pos hu, mul_inv,
      ← Real.rpow_neg hε.le, ← Real.exp_neg]
    congr 4
    ring
  simp_rw [hpt]
  rw [hh.lintegral_rpow_mul_exp_circle hε hx (-(γ ^ 2 / 2)) (-γ) hr.le]
  congr 2
  ring

/-- **Density representation of the approximate mass.** There is a jointly measurable `dens` which,
almost surely, is the density `ε^{γ²/2} e^{γ h_ε(x)}` for all `x` at once, and for which
`μ_n(f) = ∫ dens · f` for every measurable `f`, `ε = 2^{-n}`. -/
theorem IsWholePlaneGFF.exists_density_representation (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    (n : ℕ) :
    ∃ dens : ℂ → Ω → ℝ≥0∞, Measurable (Function.uncurry dens) ∧
      ∀ᵐ ω ∂P, (∀ x, dens x ω = ENNReal.ofReal (dyadicScale n ^ (γ ^ 2 / 2) *
          Real.exp (γ * hcirc ω (dyadicScale n) x))) ∧
        ∀ f : ℂ → ℝ≥0∞, Measurable f →
          lqgApproxMass γ (hcirc ω) f n = ∫⁻ x, dens x ω * f x := by
  classical
  have hε : 0 < dyadicScale n := dyadicScale_pos' n
  obtain ⟨H, -, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let dens : ℂ → Ω → ℝ≥0∞ := gmcDensityENN (fun z ω => H ω (dyadicScale n) z) γ (dyadicScale n)
  have hdensm : Measurable (Function.uncurry dens) :=
    measurable_uncurry_gmcDensityENN (hHm _ hε) γ _
  refine ⟨dens, hdensm, ?_⟩
  filter_upwards [hHae] with ω hω
  have e : (fun z => ENNReal.ofReal (dyadicScale n ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale n) z))) = fun z => dens z ω := by
    funext z
    simp only [dens, gmcDensityENN, hω]
  refine ⟨fun x => by simp only [dens, gmcDensityENN, hω], fun f hfm => ?_⟩
  have hdensx : Measurable (fun x => dens x ω) := hdensm.comp (measurable_id.prodMk measurable_const)
  unfold lqgApproxMass lqgApprox
  rw [e, lintegral_withDensity_eq_lintegral_mul _ hdensx hfm]
  rfl

/-- **Negative moments of the mass of a set at a fixed scale.** For a measurable `T ⊆ B(0, 1/2)` of
positive volume, `n ≥ 1` and `r > 0`,
`E[μ_n(T)^{-r}] ≤ |T|^{-r} (2^{-n})^{-rγ²/2 - r²γ²/2}`. -/
theorem IsWholePlaneGFF.lintegral_rpow_neg_lqgApproxMass_le [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {n : ℕ} (hn : 1 ≤ n) {T : Set ℂ}
    (hT : MeasurableSet T) (hTB : T ⊆ closedBall (0 : ℂ) (1 / 2)) (hT0 : 0 < volume T) {r : ℝ}
    (hr : 0 < r) :
    ∫⁻ ω, (lqgApproxMass γ (hcirc ω) (T.indicator 1) n) ^ (-r) ∂P ≤
      volume T ^ (-r) *
        ENNReal.ofReal (dyadicScale n ^ (-(r * γ ^ 2 / 2) - r ^ 2 * γ ^ 2 / 2)) := by
  classical
  have hε : 0 < dyadicScale n := dyadicScale_pos' n
  have hε2 : dyadicScale n ≤ 1 / 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [dyadicScale_succ_eq_half]
    have := dyadicScale_le_one' m
    linarith
  obtain ⟨dens, hdm, hae⟩ := IsWholePlaneGFF.exists_density_representation hh γ n
  have hVtop : volume T ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : ℂ)) (r := 1 / 2)).ne
      (measure_mono hTB)
  have hV0 : volume T ≠ 0 := hT0.ne'
  have hVpos : volume T ^ (-(1 + r)) ≠ ⊤ := by
    rw [ENNReal.rpow_neg]
    exact ENNReal.inv_ne_top.2 (ENNReal.rpow_pos (pos_iff_ne_zero.2 hV0) hVtop).ne'
  have hdx : ∀ ω, Measurable (fun x => dens x ω) := fun ω =>
    hdm.comp (measurable_id.prodMk measurable_const)
  -- pointwise bound
  have hpt : ∀ᵐ ω ∂P, (lqgApproxMass γ (hcirc ω) (T.indicator 1) n) ^ (-r) ≤
      volume T ^ (-(1 + r)) * (∫⁻ x in T, dens x ω ^ (-r)) := by
    filter_upwards [hae] with ω ⟨hω, hmass⟩
    have hZ : lqgApproxMass γ (hcirc ω) (T.indicator 1) n = ∫⁻ x in T, dens x ω := by
      rw [hmass _ (measurable_one.indicator hT), ← lintegral_indicator hT]
      refine lintegral_congr fun x => ?_
      by_cases hx : x ∈ T <;> simp [hx]
    rw [hZ]
    have h0 : ∀ x, dens x ω ≠ 0 := fun x => by
      rw [hω x]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have htop : ∀ x, dens x ω ≠ ⊤ := fun x => by rw [hω x]; exact ENNReal.ofReal_ne_top
    have := lintegral_rpow_neg_le_measure_univ_rpow_mul (volume.restrict T) (g := fun x => dens x ω)
      (hdx ω).aemeasurable h0 htop (by rwa [Measure.restrict_apply_univ])
      (by rwa [Measure.restrict_apply_univ]) hr
    rwa [Measure.restrict_apply_univ] at this
  calc ∫⁻ ω, (lqgApproxMass γ (hcirc ω) (T.indicator 1) n) ^ (-r) ∂P
      ≤ ∫⁻ ω, volume T ^ (-(1 + r)) * (∫⁻ x in T, dens x ω ^ (-r)) ∂P := lintegral_mono_ae hpt
    _ = volume T ^ (-(1 + r)) * ∫⁻ ω, (∫⁻ x in T, dens x ω ^ (-r)) ∂P := by
        rw [lintegral_const_mul' _ _ hVpos]
    _ = volume T ^ (-(1 + r)) * ∫⁻ x in T, (∫⁻ ω, dens x ω ^ (-r) ∂P) := by
        rw [lintegral_lintegral_swap]
        exact ((hdm.comp measurable_swap).pow_const _).aemeasurable
    _ = volume T ^ (-(1 + r)) * ∫⁻ x in T, ENNReal.ofReal
          (dyadicScale n ^ (-(r * γ ^ 2 / 2) - r ^ 2 * γ ^ 2 / 2)) := by
        congr 1
        refine setLIntegral_congr_fun hT fun x hx => ?_
        have hxn : ‖x‖ + dyadicScale n ≤ 1 := by
          have := mem_closedBall_zero_iff.1 (hTB hx)
          linarith
        rw [← IsWholePlaneGFF.lintegral_density_rpow_neg hh hε hxn γ hr]
        refine lintegral_congr_ae (hae.mono fun ω ⟨hω, _⟩ => ?_)
        beta_reduce
        rw [hω x]
    _ = volume T ^ (-r) *
        ENNReal.ofReal (dyadicScale n ^ (-(r * γ ^ 2 / 2) - r ^ 2 * γ ^ 2 / 2)) := by
        have hVr : volume T ^ (-(1 + r)) * volume T = volume T ^ (-r) := by
          have := ENNReal.rpow_add (-(1 + r)) 1 hV0 hVtop
          rw [ENNReal.rpow_one] at this
          rw [← this]
          congr 1
          ring
        rw [setLIntegral_const, mul_comm (ENNReal.ofReal _) (volume T), ← mul_assoc, hVr]

/-- **Small-scale Laplace bound.** For a measurable `T ⊆ B(0, 1/2)` of positive volume, `k' ∈ ℕ` and
`q > 0` there is `C ≥ 0`, depending only on `γ, T, k', q`, such that for every model of the
whole-plane Gaussian free field, every `1 ≤ n ≤ k'` and every `λ > 0`,
`E exp(-λ μ_n(T)) ≤ C λ^{-q}`. -/
theorem exists_laplace_small_scale_bound.{u} (γ : ℝ) {T : Set ℂ} (hT : MeasurableSet T)
    (hTB : T ⊆ closedBall (0 : ℂ) (1 / 2)) (hT0 : 0 < volume T) (k' : ℕ) {q : ℝ} (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        ∀ n : ℕ, 1 ≤ n → n ≤ k' → ∀ lam : ℝ, 0 < lam →
          ∫ ω, Real.exp (-(lam * (lqgApproxMass γ (hcirc ω) (T.indicator 1) n).toReal)) ∂P ≤
            C * lam ^ (-q) := by
  have hVtop : volume T ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : ℂ)) (r := 1 / 2)).ne
      (measure_mono hTB)
  have hVpos : 0 < (volume T).toReal := ENNReal.toReal_pos hT0.ne' hVtop
  set e : ℝ := q * γ ^ 2 / 2 + q ^ 2 * γ ^ 2 / 2 with he
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hk : 0 < dyadicScale k' := dyadicScale_pos' k'
  set K : ℝ := (volume T).toReal ^ (-q) * dyadicScale k' ^ (-e) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨q ^ q * Real.exp (-q) * K, by positivity, ?_⟩
  intro Ω _ P _ hC hcirc hh n hn hnk lam hlam
  have hf0 : ∀ x, x ∉ closedBall (0 : ℂ) (1 / 2) → T.indicator (1 : ℂ → ℝ≥0∞) x = 0 :=
    fun x hx => Set.indicator_of_notMem (fun h => hx (hTB h)) _
  have hfm : Measurable (T.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hT
  have hZ : AEMeasurable (fun ω => lqgApproxMass γ (hcirc ω) (T.indicator 1) n) P :=
    IsWholePlaneGFF.aemeasurable_lqgApproxMass hh γ hfm hf0 n
  have hE := IsWholePlaneGFF.lintegral_lqgApproxMass_eq hh γ hn hfm hf0
  rw [lintegral_indicator_one hT] at hE
  have hfin : ∀ᵐ ω ∂P, lqgApproxMass γ (hcirc ω) (T.indicator 1) n < ⊤ :=
    ae_lt_top' hZ (by rw [hE]; exact hVtop)
  have hmom : ∫⁻ ω, (lqgApproxMass γ (hcirc ω) (T.indicator 1) n) ^ (-q) ∂P ≤
      ENNReal.ofReal K := by
    refine (IsWholePlaneGFF.lintegral_rpow_neg_lqgApproxMass_le hh γ hn hT hTB hT0 hq).trans ?_
    have h1 : volume T ^ (-q) = ENNReal.ofReal ((volume T).toReal ^ (-q)) := by
      rw [← ENNReal.ofReal_rpow_of_pos hVpos, ENNReal.ofReal_toReal hVtop]
    rw [h1, ← ENNReal.ofReal_mul (by positivity), hK]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h2 : -(q * γ ^ 2 / 2) - q ^ 2 * γ ^ 2 / 2 = -e := by rw [he]; ring
    rw [h2]
    exact Real.rpow_le_rpow_of_nonpos hk (dyadicScale_le_of_le hnk) (by linarith)
  have := integral_exp_neg_le_of_lintegral_rpow_neg_le hZ hfin hq hK0 hmom hlam
  calc _ ≤ q ^ q * Real.exp (-q) * K * lam ^ (-q) := this
    _ = _ := rfl

end LatticeProb.LQG
