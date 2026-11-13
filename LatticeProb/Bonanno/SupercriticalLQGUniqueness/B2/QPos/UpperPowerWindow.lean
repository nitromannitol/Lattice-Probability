/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.UpperPowerWindow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.HighProbability
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.PowerComparison
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.Inputs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Inputs.Gaussian

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

 

theorem upper_annulus_power_window
    (hmedian : Inputs.WhiteNoiseMedianPowerWindow)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      P {ω | (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
          upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal ≤
        (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε) * (n : ℝ))})
      atTop (𝓝 1) := by
  let _ := hW.isProbabilityMeasure
  obtain ⟨p₀, hp₀, hp⟩ := upper_annulus_shifted_quantile_window hW ξ.property
  let p : ℝ := min (p₀ / 2) (1 / 4)
  have hp0 : 0 < p := by
    dsimp [p]
    exact lt_min (by positivity) (by norm_num)
  have hpp : p ≤ p₀ := (min_le_left _ _).trans (by linarith)
  have hph : p < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp0
  have hq2 : ENNReal.ofReal p ≤ 2⁻¹ :=
    (ENNReal.ofReal_le_ofReal hph.le).trans_eq ofReal_half_eq'
  let κ : ℝ := ε * Real.log 2 / (16 * (ξ : ℝ))
  let κ' : ℝ := ε * Real.log 2 / 16
  have hκ : 0 < κ := by
    dsimp [κ]
    exact div_pos (mul_pos hε (Real.log_pos (by norm_num)))
      (mul_pos (by norm_num) ξ.property)
  have hκ' : 0 < κ' := by dsimp [κ']; positivity
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let C : ℝ := Real.sqrt (2 * (ξ : ℝ) ^ 2 * Real.log 2) / p
  have hC : 0 ≤ C := div_nonneg (Real.sqrt_nonneg _) hp0.le
  have hgap : (ξ : ℝ) * κ + κ' < (ε - δ) * Real.log 2 := by
    dsimp [κ, κ', δ]
    have hξ : (ξ : ℝ) ≠ 0 := ne_of_gt ξ.property
    have hh : (ξ : ℝ) * (ε * Real.log 2 / (16 * (ξ : ℝ))) =
        ε * Real.log 2 / 16 := by
      calc
        _ = ((ξ : ℝ) * (ε * Real.log 2) / (ξ : ℝ)) / 16 := by ring
        _ = _ := by rw [mul_div_cancel_left₀ _ hξ]
    rw [hh]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith only [mul_pos hε hlog]
  have hpower : ∀ᶠ n : ℕ in atTop,
      Real.exp (((ξ : ℝ) * κ + κ') * (n : ℝ)) *
          LambdaN (ξ : ℝ) W P (n-3) (ENNReal.ofReal p) *
          ellN (ξ : ℝ) W P (n-3) (ENNReal.ofReal p) ≤
        (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε) * (n : ℝ)) := by
    apply shifted_quantile_le_power
      (a := lambdaN (ξ : ℝ) W P)
      (b := fun m => LambdaN (ξ : ℝ) W P m (ENNReal.ofReal p))
      (c := fun m => ellN (ξ : ℝ) W P m (ENNReal.ofReal p))
      (α := 1 - (ξ : ℝ) * Q) (δ := δ)
      (s := (ξ : ℝ) * κ + κ') (C := C) hgap
    · exact Exponent.Inputs.Gaussian.quantile_ratio_sqrt hW (ξ : ℝ) hp0 hph
    · intro m
      exact ⟨(T20B.ellN_pos hW hq0 (hq2.trans_lt inv_two_lt_one') m).le,
        T20B.ellN_le_lambdaN hq0 hq2 m⟩
    · filter_upwards [hmedian ξ Q hQ P W hW δ hδ] with m hm
      exact hm.2
  have htail := hp p hp0 hpp κ κ' hκ hκ'
  have hmeas : ∀ n : ℕ, Measurable (fun ω =>
      (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal) := by
    intro n
    have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
    exact (measurable_crossLenIn upperAnnulus_isCompact hφ.cont hφ.meas).ennreal_toReal
  have hbad : Tendsto (fun n : ℕ =>
      P {ω | (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε) * (n : ℝ)) <
        (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
          upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal}) atTop (𝓝 0) := by
    apply Filter.Tendsto.squeeze' tendsto_const_nhds htail
      (Filter.Eventually.of_forall fun n => bot_le) ?_
    filter_upwards [hpower] with n hn
    apply measure_mono
    intro ω hω
    have hΛ : 0 < LambdaN (ξ : ℝ) W P (n-3) (ENNReal.ofReal p) :=
      T20B.LambdaN_pos hW hq0 hq2 _
    have hℓ : 0 < ellN (ξ : ℝ) W P (n-3) (ENNReal.ofReal p) :=
      T20B.ellN_pos hW hq0 (hq2.trans_lt inv_two_lt_one') _
    have hth : Real.exp ((ξ : ℝ) * (κ * (n : ℝ))) *
        ((2 : ℝ)⁻¹ ^ 3 *
          (Real.exp (κ' * (n : ℝ)) * LambdaN (ξ : ℝ) W P (n - 3) (ENNReal.ofReal p) *
            ellN (ξ : ℝ) W P (n - 3) (ENNReal.ofReal p))) ≤
      Real.exp (((ξ : ℝ) * κ + κ') * (n : ℝ)) *
          LambdaN (ξ : ℝ) W P (n-3) (ENNReal.ofReal p) *
          ellN (ξ : ℝ) W P (n-3) (ENNReal.ofReal p) := by
      rw [show ((ξ : ℝ) * κ + κ') * (n : ℝ) =
        (ξ : ℝ) * (κ * (n : ℝ)) + κ' * (n : ℝ) by ring, Real.exp_add]
      have hf : (2 : ℝ)⁻¹ ^ 3 ≤ 1 := by norm_num
      nlinarith [mul_nonneg (Real.exp_pos ((ξ : ℝ) * (κ * (n : ℝ)))).le
        (mul_nonneg (Real.exp_pos (κ' * (n : ℝ))).le
          (mul_nonneg hΛ.le hℓ.le))]
    exact lt_of_le_of_lt (hth.trans hn) hω
  have hsub : Tendsto (fun n : ℕ => (1 : ENNReal) -
      P {ω | (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε) * (n : ℝ)) <
        (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
          upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal}) atTop (𝓝 1) := by
    have hpair : Tendsto (fun n : ℕ => ((1 : ENNReal),
        P {ω | (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε) * (n : ℝ)) <
          (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
            upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal}))
        atTop (𝓝 ((1 : ENNReal), (0 : ENNReal))) :=
      by simpa only [nhds_prod_eq] using
        (show Tendsto (fun _ : ℕ => (1 : ENNReal)) atTop (𝓝 1)
          from tendsto_const_nhds).prodMk hbad
    simpa only [Function.comp_def, tsub_zero] using
      (ENNReal.tendsto_sub (Or.inl ENNReal.one_ne_top)).comp hpair
  apply hsub.congr'
  filter_upwards [] with n
  have hm : MeasurableSet {ω | (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε) * (n : ℝ)) <
      (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal} :=
    (hmeas n) measurableSet_Ioi
  have hset : {ω | (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal ≤
        (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε) * (n : ℝ))} =
      {ω | (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε) * (n : ℝ)) <
        (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
          upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal}ᶜ := by
    ext ω; simp
  rw [hset]
  have hcomp := (measure_compl hm (by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (show P {ω | (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε) * (n : ℝ)) <
        (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
          upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal} ≤ 1 from prob_le_one))).symm
  rw [show P Set.univ = (1 : ENNReal) from measure_univ] at hcomp
  exact hcomp

end SupercriticalLQGUniqueness.B2.QPos
