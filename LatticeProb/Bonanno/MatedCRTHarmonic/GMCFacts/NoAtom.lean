/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.NoAtom at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Gaussian

/-!
# The LQG measure of a whole-plane GFF has no atom at a given point

`ae_measure_singleton_eq_zero`: if `H` is a whole-plane GFF circle-average process with measurable coordinates and `μ`
its LQG measure (`IsLQGAreaOf`), then for every `z₀` with `|z₀| ≤ 1/2`, almost surely `μ({z₀}) = 0`.

Proof (first moment and Fatou): for the plateau `f_ρ = plat z₀ (4ρ)` (`𝟙_{B̄_ρ(z₀)} ≤ f_ρ ≤ 𝟙_{B_{2ρ}(z₀)}`),
`E[r^{γ²/2} e^{γ h_r(z)}] = r^{γ²/2} e^{γ² Var h_r(z)/2} ≤ 1` for `|z| + r ≤ 1` (`Var h_r(z) ≤ log r⁻¹`, the
`gffCircleCov_self_le_neg_log`), so by Tonelli and Fatou `E ∫ f_ρ dμ ≤ |B_{2ρ}(z₀)|`; Markov and `ρ → 0`. This is the
standard "no atoms at a fixed point" fact for GMC (Duplantier–Sheffield arXiv:0808.1560 Prop 1.2, first moment), used
in `Dominate.lean` for the point `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open LQGMetric.DGMC LQGMetric.DGMC.Neg3
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-- The first moment of the approximation density: `E[r^{γ²/2} e^{γ h_r(z)}] ≤ 1` when `|z| + r ≤ 1`. -/
lemma lintegral_dens_le_one (hH : LQGDimension.IsGFFCircleAverage H P) (γ : ℝ) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : ‖z‖ + r ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω)) ∂P ≤ 1 := by
  have hm : ∀ ω, ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω)) =
      ENNReal.ofReal (r ^ (γ ^ 2 / 2)) * ENNReal.ofReal (Real.exp (γ * H r z ω)) := fun ω =>
    ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)
  simp_rw [hm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, LQGMetric.DG.lintegral_exp_circleAvg hH hr z γ,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  refine ENNReal.ofReal_le_one.2 ?_
  have hv := GMSLemma27.gffCircleCov_self_le_neg_log hr hz
  rw [Real.rpow_def_of_pos hr, ← Real.exp_add]
  refine Real.exp_le_one_iff.2 ?_
  have : 0 ≤ γ ^ 2 := sq_nonneg γ
  nlinarith

/-- **No atom at a fixed point.** -/
theorem ae_measure_singleton_eq_zero (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} {μ : Ω → Measure ℂ}
    (hμ : GMSLemma27.IsLQGAreaOf γ H μ P) {z₀ : ℂ} (hz₀ : ‖z₀‖ ≤ 1 / 2) :
    ∀ᵐ ω ∂P, μ ω {z₀} = 0 := by
  have hP := hH.isProbabilityMeasure
  -- the bound at scale `ρ`
  have key : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 8 → ∀ δ : ℝ≥0∞, δ ≠ 0 → δ ≠ ⊤ →
      P {ω | δ ≤ μ ω {z₀}} ≤ volume (ball z₀ (2 * ρ)) / δ := by
    intro ρ hρ hρ8 δ hδ0 hδt
    have h4 : 0 < 4 * ρ := by positivity
    set f : ℂ → ℝ := plat z₀ (4 * ρ)
    have hfc : Continuous f := continuous_plat _ _
    have hfs : HasCompactSupport f :=
      (isCompact_closedBall z₀ (4 * ρ / 2)).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_plat h4)
    have hf0 : ∀ z, 0 ≤ f z := plat_nonneg _ _
    have hf1 : ∀ z, f z ≤ 1 := plat_le_one _ _
    have hfz : ∀ z, 2 * ρ ≤ ‖z - z₀‖ → f z = 0 := fun z hz => plat_eq_zero h4 (by linarith)
    have hfone : f z₀ = 1 := plat_eq_one h4 (by rw [sub_self, norm_zero]; positivity)
    -- `G_k ω = ∫⁻ ofReal f d(approx_k)` and `G ω = ∫⁻ ofReal f dμ`
    set G : ℕ → Ω → ℝ≥0∞ := fun k ω => ∫⁻ z, ENNReal.ofReal (f z) ∂(GMSLemma27.lqgApprox γ H k ω)
    set Glim : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, ENNReal.ofReal (f z) ∂(μ ω)
    have hdr : ∀ k, 0 < GMSLemma27.dyadicRadius k := fun k => by
      rw [dyadicRadius_eq_radius]; exact QuantumZipper.radius_pos k
    have hGk : ∀ k ω, G k ω = ∫⁻ z, ENNReal.ofReal (f z) * ENNReal.ofReal
        (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (GMSLemma27.dyadicRadius k) z ω)) := by
      intro k ω
      have hcontd : Continuous fun z => H (GMSLemma27.dyadicRadius k) z ω :=
        hH.continuous _ (hdr k) ω
      have hd : Measurable fun z => ENNReal.ofReal (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
          Real.exp (γ * H (GMSLemma27.dyadicRadius k) z ω)) :=
        ENNReal.measurable_ofReal.comp (continuous_const.mul (continuous_const.mul hcontd).rexp).measurable
      simp only [G, GMSLemma27.lqgApprox]
      rw [lintegral_withDensity_eq_lintegral_mul₀ hd.aemeasurable
        (g := fun z => ENNReal.ofReal (f z)) (ENNReal.measurable_ofReal.comp hfc.measurable).aemeasurable]
      exact lintegral_congr fun z => by simp only [Pi.mul_apply]; exact mul_comm _ _
    have hjm : ∀ k, Measurable fun p : ℂ × Ω => ENNReal.ofReal (f p.1) * ENNReal.ofReal
        (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (GMSLemma27.dyadicRadius k) p.1 p.2)) := by
      intro k
      have hj := measurable_uncurry_coord hH hHm (hdr k)
      exact (ENNReal.measurable_ofReal.comp (hfc.measurable.comp measurable_fst)).mul
        (ENNReal.measurable_ofReal.comp (measurable_const.mul ((hj.const_mul γ).exp)))
    have hGm : ∀ k, Measurable (G k) := fun k => by
      rw [show G k = fun ω => ∫⁻ z, ENNReal.ofReal (f z) * ENNReal.ofReal
          (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
            Real.exp (γ * H (GMSLemma27.dyadicRadius k) z ω)) from funext (hGk k)]
      exact (hjm k).lintegral_prod_left'
    -- `E G_k ≤ |B_{2ρ}(z₀)|` for `k ≥ 2`
    have hEG : ∀ k, 2 ≤ k → ∫⁻ ω, G k ω ∂P ≤ volume (ball z₀ (2 * ρ)) := by
      intro k hk
      have hr4 : GMSLemma27.dyadicRadius k ≤ 1 / 4 := by
        rw [dyadicRadius_eq_radius]
        calc QuantumZipper.radius k ≤ QuantumZipper.radius 2 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
          _ = 1 / 4 := radius_two
      simp_rw [hGk]
      rw [lintegral_lintegral_swap (f := fun ω z => ENNReal.ofReal (f z) * ENNReal.ofReal
          (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (GMSLemma27.dyadicRadius k) z ω)))
        ((hjm k).comp (measurable_snd.prodMk measurable_fst)).aemeasurable]
      calc ∫⁻ z, ∫⁻ ω, ENNReal.ofReal (f z) * ENNReal.ofReal (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
            Real.exp (γ * H (GMSLemma27.dyadicRadius k) z ω)) ∂P
          ≤ ∫⁻ z, (ball z₀ (2 * ρ)).indicator 1 z := by
            refine lintegral_mono fun z => ?_
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            by_cases hz : z ∈ ball z₀ (2 * ρ)
            · rw [indicator_of_mem hz, Pi.one_apply]
              have hzn : ‖z‖ + GMSLemma27.dyadicRadius k ≤ 1 := by
                rw [mem_ball, dist_eq_norm] at hz
                have : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
                  calc ‖z‖ = ‖(z - z₀) + z₀‖ := by rw [sub_add_cancel]
                    _ ≤ _ := norm_add_le _ _
                linarith
              calc ENNReal.ofReal (f z) * _ ≤ 1 * 1 :=
                    mul_le_mul' (ENNReal.ofReal_le_one.2 (hf1 z))
                      (lintegral_dens_le_one hH γ (hdr k) hzn)
                _ = 1 := one_mul 1
            · rw [indicator_of_notMem hz, hfz z (by
                rw [mem_ball, dist_eq_norm, not_lt] at hz; exact hz), ENNReal.ofReal_zero, zero_mul]
          _ = volume (ball z₀ (2 * ρ)) := lintegral_indicator_one measurableSet_ball
    -- `G_k → G` almost surely
    have hconv : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (Glim ω)) := by
      filter_upwards [hμ] with ω ⟨hlf, hc⟩
      have h1 := (ENNReal.continuous_ofReal.tendsto _).comp (hc f hfc hfs)
      have e1 : ∀ k, ENNReal.ofReal (∫ z, f z ∂(GMSLemma27.lqgApprox γ H k ω)) = G k ω := fun k => by
        have := isLocallyFiniteMeasure_lqgApprox hH γ k ω
        exact ofReal_integral_plat z₀ h4
      have e2 : ENNReal.ofReal (∫ z, f z ∂(μ ω)) = Glim ω := ofReal_integral_plat z₀ h4
      simp only [Function.comp_def, e1, e2] at h1
      exact h1
    have hGae : AEMeasurable Glim P :=
      aemeasurable_of_tendsto_metrizable_ae atTop (fun k => (hGm k).aemeasurable) hconv
    have hEGlim : ∫⁻ ω, Glim ω ∂P ≤ volume (ball z₀ (2 * ρ)) := by
      calc ∫⁻ ω, Glim ω ∂P = ∫⁻ ω, liminf (fun k => G k ω) atTop ∂P :=
            lintegral_congr_ae (hconv.mono fun ω h => h.liminf_eq.symm)
        _ ≤ liminf (fun k => ∫⁻ ω, G k ω ∂P) atTop := lintegral_liminf_le hGm
        _ ≤ volume (ball z₀ (2 * ρ)) :=
            liminf_le_of_frequently_le' (eventually_atTop.2 ⟨2, hEG⟩).frequently
    -- `μ{z₀} ≤ G` a.s.
    have hle : ∀ᵐ ω ∂P, μ ω {z₀} ≤ Glim ω := by
      filter_upwards [hμ] with ω _
      calc μ ω {z₀} = ∫⁻ z, ({z₀} : Set ℂ).indicator 1 z ∂(μ ω) :=
            (lintegral_indicator_one (measurableSet_singleton z₀)).symm
        _ ≤ Glim ω := lintegral_mono fun z => by
            by_cases hz : z = z₀
            · subst hz
              rw [indicator_of_mem (mem_singleton z), Pi.one_apply, hfone, ENNReal.ofReal_one]
            · rw [indicator_of_notMem (show z ∉ ({z₀} : Set ℂ) from hz)]
              exact zero_le
    calc P {ω | δ ≤ μ ω {z₀}} ≤ P {ω | δ ≤ Glim ω} :=
          measure_mono_ae (hle.mono fun ω h hω => le_trans hω h)
      _ ≤ (∫⁻ ω, Glim ω ∂P) / δ := meas_ge_le_lintegral_div hGae hδ0 hδt
      _ ≤ volume (ball z₀ (2 * ρ)) / δ := ENNReal.div_le_div_right hEGlim _
  -- let `ρ → 0`
  have hzero : ∀ δ : ℝ≥0∞, δ ≠ 0 → δ ≠ ⊤ → P {ω | δ ≤ μ ω {z₀}} = 0 := by
    intro δ hδ0 hδt
    set ρ : ℕ → ℝ := fun n => 1 / 8 * (1 / ((n : ℝ) + 1))
    have hρ0 : ∀ n, 0 < ρ n := fun n => by positivity
    have hρ8 : ∀ n, ρ n ≤ 1 / 8 := fun n => by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      simp only [ρ]; nlinarith
    have hρt : Tendsto ρ atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 8 : ℝ)
      simpa only [mul_zero] using this
    have h1 : Tendsto (fun n => ENNReal.ofReal (2 * ρ n)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (by simpa only [mul_zero] using hρt.const_mul 2)
    have h2 : Tendsto (fun n => ENNReal.ofReal (2 * ρ n) ^ 2 * (NNReal.pi : ℝ≥0∞)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const (((ENNReal.continuous_pow 2).tendsto 0).comp h1)
        (b := (NNReal.pi : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)
      simpa only [Function.comp_def, zero_pow two_ne_zero, zero_mul] using this
    have hlim : Tendsto (fun n => volume (ball z₀ (2 * ρ n)) / δ) atTop (𝓝 0) := by
      simp_rw [Complex.volume_ball]
      have := ENNReal.Tendsto.div_const h2 (b := δ) (Or.inr hδ0)
      simpa only [ENNReal.zero_div] using this
    exact le_antisymm (ge_of_tendsto' hlim fun n => key (ρ n) (hρ0 n) (hρ8 n) δ hδ0 hδt) zero_le
  rw [ae_iff]
  have hsub : {ω | ¬ μ ω {z₀} = 0} ⊆ ⋃ m : ℕ, {ω | ((m : ℝ≥0∞) + 1)⁻¹ ≤ μ ω {z₀}} := by
    intro ω hω
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hω
    refine mem_iUnion.2 ⟨m, ?_⟩
    show ((m : ℝ≥0∞) + 1)⁻¹ ≤ μ ω {z₀}
    refine le_trans (ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.le_succ m |>.trans_eq' rfl |> fun _ => le_self_add)) hm.le
  refine measure_mono_null hsub (measure_iUnion_null fun m => hzero _ ?_ ?_)
  · simp
  · simp

end MatedCRTHarmonic.GMCFacts
