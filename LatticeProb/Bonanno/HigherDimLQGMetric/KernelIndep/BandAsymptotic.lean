/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.BandAsymptotic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.Exponent
import LatticeProb.Bonanno.HigherDimLFPP.Exist.CrudeBounds

/-! The leading `√(2d)` coefficient in the band supremum threshold. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory Filter Topology Set Real
namespace HigherDimLQGMetric

private theorem sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy
    have h3 := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
    nlinarith

private theorem band_supMean_rate (d : ℕ) (L : ℝ) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) :
    let ℓ := Real.log ε⁻¹
    let C := 1 + (d : ℝ) * Real.log 5
    let c := HigherDimLFPP.Crude.cOne d L
    HigherDimLFPP.SupB.supMean d L ℓ (d * Real.log (4 / ε + 1)) ≤
      Real.sqrt (2 * d) * ℓ +
      (Real.sqrt 2 * Real.sqrt C + c * Real.sqrt d) * Real.sqrt ℓ +
      (c * Real.sqrt C + HigherDimLFPP.Osc.blockConst d L (Real.sqrt d)) := by
  dsimp
  set ℓ : ℝ := Real.log ε⁻¹ with hℓdef
  set C : ℝ := 1 + (d : ℝ) * Real.log 5 with hCdef
  set c : ℝ := HigherDimLFPP.Crude.cOne d L with hcdef
  have hℓ : 0 < ℓ := Real.log_pos (one_lt_inv_iff₀.2 hε)
  have hC : 0 ≤ C := by
    dsimp [C]
    have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    positivity
  have hc : 0 ≤ c := HigherDimLFPP.Crude.cOne_nonneg d L
  have harg : 4 / ε + 1 ≤ 5 / ε := by
    apply (le_div_iff₀ hε.1).2
    rw [add_mul, div_mul_cancel₀ _ hε.1.ne']
    linarith [hε.2.le]
  have hlg : Real.log (4 / ε + 1) ≤ Real.log 5 + ℓ := by
    calc Real.log (4 / ε + 1) ≤ Real.log (5 / ε) :=
      Real.log_le_log (by
        have hq : 0 ≤ 4 / ε := div_nonneg (by norm_num) hε.1.le
        linarith) harg
      _ = Real.log 5 + ℓ := by
        rw [hℓdef, div_eq_mul_inv, Real.log_mul (by norm_num : (5 : ℝ) ≠ 0)
          (inv_ne_zero hε.1.ne'), add_comm]
  have hq : 1 + (d : ℝ) * Real.log (4 / ε + 1) ≤ C + d * ℓ := by
    dsimp [C]
    nlinarith [mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.2 hlg)]
  have hroot : Real.sqrt (1 + (d : ℝ) * Real.log (4 / ε + 1)) ≤
      Real.sqrt C + Real.sqrt d * Real.sqrt ℓ := by
    calc Real.sqrt (1 + (d : ℝ) * Real.log (4 / ε + 1)) ≤
        Real.sqrt (C + d * ℓ) := Real.sqrt_le_sqrt hq
      _ ≤ Real.sqrt C + Real.sqrt (d * ℓ) :=
        sqrt_add_le' hC (mul_nonneg (Nat.cast_nonneg d) hℓ.le)
      _ = Real.sqrt C + Real.sqrt d * Real.sqrt ℓ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d)]
  have hfac : 0 ≤ Real.sqrt 2 * Real.sqrt ℓ + c := by positivity
  have hmain : Real.sqrt 2 * Real.sqrt ℓ * (Real.sqrt d * Real.sqrt ℓ) =
      Real.sqrt (2 * d) * ℓ := by
    calc Real.sqrt 2 * Real.sqrt ℓ * (Real.sqrt d * Real.sqrt ℓ) =
        (Real.sqrt 2 * Real.sqrt d) * (Real.sqrt ℓ * Real.sqrt ℓ) := by ring
      _ = (Real.sqrt 2 * Real.sqrt d) * ℓ := by rw [Real.mul_self_sqrt hℓ.le]
      _ = Real.sqrt (2 * d) * ℓ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc HigherDimLFPP.SupB.supMean d L ℓ (d * Real.log (4 / ε + 1)) =
        (Real.sqrt 2 * Real.sqrt ℓ + c) *
          Real.sqrt (1 + d * Real.log (4 / ε + 1)) +
          HigherDimLFPP.Osc.blockConst d L (Real.sqrt d) := by
          rw [HigherDimLFPP.Crude.supMean_eq, hℓdef]
    _ ≤ (Real.sqrt 2 * Real.sqrt ℓ + c) *
          (Real.sqrt C + Real.sqrt d * Real.sqrt ℓ) +
          HigherDimLFPP.Osc.blockConst d L (Real.sqrt d) :=
          add_le_add (mul_le_mul_of_nonneg_left hroot hfac) le_rfl
    _ = Real.sqrt (2 * d) * ℓ +
          (Real.sqrt 2 * Real.sqrt C + c * Real.sqrt d) * Real.sqrt ℓ +
          (c * Real.sqrt C + HigherDimLFPP.Osc.blockConst d L (Real.sqrt d)) := by
          rw [← hmain]
          ring

/-- The band expected-supremum threshold has upper asymptotic coefficient `√(2d)`. -/
theorem band_supMean_limsup (d : ℕ) (L : ℝ) :
    ∀ η > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      HigherDimLFPP.SupB.supMean d L (Real.log ε⁻¹)
        (d * Real.log (4 / ε + 1)) / Real.log ε⁻¹ < Real.sqrt (2 * d) + η := by
  intro η hη
  set C : ℝ := 1 + (d : ℝ) * Real.log 5 with hCdef
  set c : ℝ := HigherDimLFPP.Crude.cOne d L with hcdef
  set K : ℝ := Real.sqrt 2 * Real.sqrt C + c * Real.sqrt d with hKdef
  set B : ℝ := c * Real.sqrt C + HigherDimLFPP.Osc.blockConst d L (Real.sqrt d)
    with hBdef
  have hrest : Tendsto (fun ε : ℝ => (K * Real.sqrt (Real.log ε⁻¹) + B) /
      Real.log ε⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have hs := (sqrt_affine_div_tendsto_zero 0 1 (by norm_num) (by norm_num)).comp
      log_inv_tendsto_atTop
    have hi := (tendsto_inv_atTop_zero.comp log_inv_tendsto_atTop)
    have h := (hs.const_mul K).add (hi.const_mul B)
    convert h using 1
    · funext ε
      simp only [Function.comp_def, zero_add, one_mul, div_eq_mul_inv]
      ring
    · ring
  filter_upwards [hrest.eventually (Iio_mem_nhds hη),
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hrestε hε
  have hℓ : 0 < Real.log ε⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 hε)
  have hb := band_supMean_rate d L hε
  have hdiv := div_le_div_of_nonneg_right hb hℓ.le
  set R : ℝ := K * Real.sqrt (Real.log ε⁻¹) + B with hRdef
  change R / Real.log ε⁻¹ < η at hrestε
  have hdiv' : HigherDimLFPP.SupB.supMean d L (Real.log ε⁻¹)
      (d * Real.log (4 / ε + 1)) / Real.log ε⁻¹ ≤
        (Real.sqrt (2 * d) * Real.log ε⁻¹ + R) / Real.log ε⁻¹ := by
    simpa only [hRdef, hKdef, hBdef, hCdef, hcdef, add_assoc] using hdiv
  have heq : (Real.sqrt (2 * d) * Real.log ε⁻¹ + R) / Real.log ε⁻¹ =
      Real.sqrt (2 * d) + R / Real.log ε⁻¹ := by
    rw [add_div, mul_div_cancel_right₀ _ hℓ.ne']
  rw [heq] at hdiv'
  exact lt_of_le_of_lt hdiv' (by linarith [hrestε])

/-- The normalized log distance has no upper tail beyond `ξ√(2d)`. -/
theorem band_logDistance_upper_tail {d : ℕ} (hd : 2 ≤ d)
    {κ : HigherDimLFPP.Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : HigherDimLFPP.WN d → Ω → ℝ} (hW : HigherDimLFPP.IsWhiteNoise P W)
    {H : ℝ → HigherDimLFPP.Rd d → Ω → ℝ}
    (hH : ∀ ε ∈ Ioo (0 : ℝ) 1,
      HigherDimLFPP.IsBandVersion P W κ ε 1 (H ε))
    {ξ A : ℝ} (hξ : 0 < ξ) (hA : ξ * Real.sqrt (2 * d) < A) :
    Tendsto (fun ε : ℝ => P {ω |
      A ≤ Real.log (HigherDimLFPP.lfppDistance d ξ (fun z => H ε z ω)) /
        Real.log ε}) (𝓝[>] 0) (𝓝 0) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨L, hL, hB⟩ := HigherDimLFPP.exists_bandSup_bounds hκ
  set η : ℝ := (A / ξ - Real.sqrt (2 * d)) / 4 with hηdef
  have hη : 0 < η := by
    dsimp [η]
    apply div_pos _ (by norm_num)
    apply sub_pos.2
    apply (lt_div_iff₀ hξ).2
    rwa [mul_comm]
  have hrate := band_supMean_limsup d L η hη
  have hbound : Tendsto (fun ε : ℝ => ENNReal.ofReal
      (2 * Real.exp (-(η ^ 2 / 2 * Real.log ε⁻¹)))) (𝓝[>] 0) (𝓝 0) := by
    have hc : 0 < η ^ 2 / 2 := by positivity
    have hh := log_inv_tendsto_atTop.const_mul_atTop hc
    have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hh).const_mul 2
    have he' := ENNReal.tendsto_ofReal he
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using he'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound (by
      exact Filter.Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hrate] with ε hε hr
  set ℓ : ℝ := Real.log ε⁻¹ with hℓdef
  have hℓ : 0 < ℓ := Real.log_pos (one_lt_inv_iff₀.2 hε)
  set M : ℝ := HigherDimLFPP.SupB.supMean d L ℓ (d * Real.log (4 / ε + 1))
    with hMdef
  set u : ℝ := η * ℓ with hudef
  have hu : 0 ≤ u := (mul_pos hη hℓ).le
  have hthresh : ξ * (M + u) < A * ℓ := by
    have h1 := (div_lt_iff₀ hℓ).1 hr
    have h2 : (M + u) / ℓ < A / ξ := by
      rw [hudef, add_div, mul_div_cancel_right₀ η hℓ.ne']
      dsimp [η] at h1 ⊢
      linarith
    have h3 := (div_lt_iff₀ hℓ).1 h2
    calc ξ * (M + u) < ξ * (A / ξ * ℓ) := mul_lt_mul_of_pos_left h3 hξ
      _ = A * ℓ := by field_simp
  have ht := (hB hW hε.1 hε.2.le (hH ε hε) hℓ (by simp [hℓdef, one_div])
    (0 : HigherDimLFPP.Rd d) (by norm_num : (0 : ℝ) ≤ 2)).2.2.2 hu
  have hsub : {ω | A ≤ Real.log (HigherDimLFPP.lfppDistance d ξ
      (fun z => H ε z ω)) / Real.log ε} ⊆
      {ω | ∃ z ∈ HigherDimLFPP.Osc.box (0 : HigherDimLFPP.Rd d) 2,
        M + u < |H ε z ω|} := by
    intro ω hw
    by_contra hn
    have hfield : ∀ z ∈ HigherDimLFPP.cube d, |H ε z ω| ≤ M + u := by
      intro z hz
      exact le_of_not_gt (fun h => hn ⟨z,
        HigherDimLFPP.Osc.closure_cube_subset_box (subset_closure hz), h⟩)
    have hD := HigherDimLFPP.exp_neg_le_lfppDistance (ζ := ξ)
      (by omega : 0 < d) ((hH ε hε).continuous ω) hfield
    have hDpos : 0 < HigherDimLFPP.lfppDistance d ξ (fun z => H ε z ω) :=
      lt_of_lt_of_le (Real.exp_pos _) hD
    have hlogD := Real.log_le_log (Real.exp_pos _) hD
    rw [Real.log_exp] at hlogD
    have hlogε : Real.log ε = -ℓ := by rw [hℓdef, Real.log_inv]; ring
    simp only [Set.mem_ofPred_eq] at hw
    rw [hlogε] at hw
    have hw' : Real.log (HigherDimLFPP.lfppDistance d ξ
        (fun z => H ε z ω)) ≤ -(A * ℓ) := by
      have hx : A ≤ -Real.log (HigherDimLFPP.lfppDistance d ξ
          (fun z => H ε z ω)) / ℓ := by simpa only [div_neg, neg_div] using hw
      have hx' := (le_div_iff₀ hℓ).1 hx
      nlinarith
    rw [abs_of_pos hξ] at hlogD
    nlinarith
  have ht' : P {ω | ∃ z ∈ HigherDimLFPP.Osc.box
      (0 : HigherDimLFPP.Rd d) 2, M + u < |H ε z ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(η ^ 2 / 2 * ℓ))) := by
    convert ht using 1
    · simp only [hMdef, hudef, hℓdef]
      ring
    · rw [hudef, hℓdef]
      field_simp
  exact (measure_mono hsub).trans ht'

/-- A limit in probability cannot exceed a level above which every upper tail vanishes. -/
theorem limit_le_of_upper_tails {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : ℝ → Ω → ℝ}
    {lam c : ℝ} (hF : TendstoInMeasure P F (𝓝[>] (0 : ℝ)) (fun _ => lam))
    (htail : ∀ A : ℝ, c < A →
      Tendsto (fun ε : ℝ => P {ω | A ≤ F ε ω}) (𝓝[>] 0) (𝓝 0)) :
    lam ≤ c := by
  by_contra hn
  have hc : c < lam := lt_of_not_ge hn
  set A : ℝ := (c + lam) / 2 with hAdef
  have hcA : c < A := by dsimp [A]; linarith
  have hAl : A < lam := by dsimp [A]; linarith
  set δ : ℝ := (lam - A) / 2 with hδdef
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hbad := (tendstoInMeasure_iff_dist.1 hF) δ hδ
  have hhigh := htail A hcA
  have hsum : Tendsto (fun ε : ℝ =>
      P {ω | δ ≤ dist (F ε ω) lam} + P {ω | A ≤ F ε ω})
      (𝓝[>] 0) (𝓝 0) := by simpa using hbad.add hhigh
  have hevent := hsum.eventually (Iio_mem_nhds (by norm_num : (0 : ENNReal) < 1))
  obtain ⟨ε, he⟩ := hevent.exists
  have hsub : (Set.univ : Set Ω) ⊆
      {ω | δ ≤ dist (F ε ω) lam} ∪ {ω | A ≤ F ε ω} := by
    intro ω _
    by_cases hh : A ≤ F ε ω
    · exact Or.inr hh
    · left
      have hlt : F ε ω < A := lt_of_not_ge hh
      simp only [Set.mem_ofPred_eq, Real.dist_eq]
      rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ lam - F ε ω)]
      dsimp [δ]
      linarith
  have hle : (1 : ENNReal) ≤
      P {ω | δ ≤ dist (F ε ω) lam} + P {ω | A ≤ F ε ω} := by
    rw [← measure_univ (μ := P)]
    exact (measure_mono hsub).trans (measure_union_le _ _)
  exact (not_lt_of_ge hle) he

end HigherDimLQGMetric
