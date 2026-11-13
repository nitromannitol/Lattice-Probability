/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.Median.Bridge at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.HeatVersion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Inputs.Gaussian
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Lvl
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGOsc
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mul
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Inputs.WhiteNoise




 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.Median

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem octave_crossing_cdf_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (ξ : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ((2 : ℝ) ^ m)⁻¹ / 2 ≤ ε → ε ≤ ((2 : ℝ) ^ m)⁻¹ →
      ∀ a : ℝ≥0∞,
        P {ω | rectLen ξ (fun z => phiVer W P ε 1 z ω) (rectAB 1 1) < a} ≤
          P {ω | rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) <
            ENNReal.ofReal (Real.exp (|ξ| * (B * Real.sqrt (m + 1 : ℝ)))) * a} +
            ENNReal.ofReal (1 / 8 : ℝ) ∧
        P {ω | rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) ≤ a} ≤
          P {ω | rectLen ξ (fun z => phiVer W P ε 1 z ω) (rectAB 1 1) ≤
            ENNReal.ofReal (Real.exp (|ξ| * (B * Real.sqrt (m + 1 : ℝ)))) * a} +
            ENNReal.ofReal (1 / 8 : ℝ) := by
  letI := hW.isProbabilityMeasure
  obtain ⟨B, hB, htail⟩ := Inputs.Gaussian.octave_sup_sqrt hW
  refine ⟨B, hB, ?_⟩
  intro m ε hε hεlo hεhi a
  let b : ℝ := ((2 : ℝ) ^ m)⁻¹
  let d : ℝ := B * Real.sqrt (m + 1 : ℝ)
  let bad : Set Ω :=
    {ω | d ≤ ⨆ z : SupTail.ferniqueBox 0 1, |phiVer W P ε b z ω|}
  have hb : 0 < b := by dsimp [b]; positivity
  have hv := isPhiVersion_phiVer hW hε (show ε ≤ b from hεhi)
  have hbad : P bad ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
    have hsub := Inputs.Gaussian.real_sup_event_subset
      (Y := phiVer W P ε b) hv.cont d
    have ht := htail m hε hεlo hεhi hv.cont hv.ae_eq
    exact (measure_mono hsub).trans ht
  have hadd : ∀ᵐ ω ∂P, ∀ z,
      phiVer W P ε 1 z ω = phiMN W P 0 m z ω + phiVer W P ε b z ω := by
    simpa only [b, inv_pow] using
      (S6P28U.ae_phiVer_split hW hε
        (show ε ≤ (2 : ℝ)⁻¹ ^ m by simpa only [inv_pow] using hεhi))
  have hcmp : ∀ᵐ ω ∂P, ω ∉ bad →
      ∀ z ∈ Blueprint.closedUnitSquare,
        |phiVer W P ε 1 z ω - phiMN W P 0 m z ω| ≤ d := by
    filter_upwards [hadd] with ω hω hgood z hz
    have hz' : z ∈ SupTail.ferniqueBox 0 1 := by
      apply S6DG.unit_subset_fernique
      simpa [Blueprint.closedUnitSquare, MarkedRect.toSet, rectAB,
        Complex.mem_reProdIm, and_assoc] using hz
    have hs : |phiVer W P ε b z ω| ≤
        ⨆ z : SupTail.ferniqueBox 0 1, |phiVer W P ε b z ω| := by
      exact le_ciSup (SupTail.bddAbove_abs_of_compact
        (SupTail.isCompact_ferniqueBox 0 1) (hv.cont ω)) ⟨z, hz'⟩
    rw [hω z, add_sub_cancel_left]
    exact hs.trans (not_le.mp hgood).le
  constructor
  · have hinc : {ω | rectLen ξ (fun z => phiVer W P ε 1 z ω) (rectAB 1 1) < a} ≤ᵐ[P]
        ({ω | rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) <
          ENNReal.ofReal (Real.exp (|ξ| * d)) * a} ∪ bad) := by
      filter_upwards [hcmp] with ω hω hlt
      by_cases hb : ω ∈ bad
      · exact Or.inr hb
      · exact Or.inl (Exponent.HeatVersion.rectLen_lt_exp_of_abs_sub_le ξ d _ _ a (hω hb) hlt)
    calc
      P {ω | rectLen ξ (fun z => phiVer W P ε 1 z ω) (rectAB 1 1) < a}
          ≤ P ({ω | rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) <
              ENNReal.ofReal (Real.exp (|ξ| * d)) * a} ∪ bad) := measure_mono_ae hinc
      _ ≤ P {ω | rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) <
              ENNReal.ofReal (Real.exp (|ξ| * d)) * a} + P bad :=
        measure_union_le _ _
      _ ≤ _ := by simpa only [d] using add_le_add_right hbad _
  · have hinc : {ω | rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) ≤ a} ≤ᵐ[P]
        ({ω | rectLen ξ (fun z => phiVer W P ε 1 z ω) (rectAB 1 1) ≤
          ENNReal.ofReal (Real.exp (|ξ| * d)) * a} ∪ bad) := by
      filter_upwards [hcmp] with ω hω hle
      by_cases hb : ω ∈ bad
      · exact Or.inr hb
      · exact Or.inl (Exponent.HeatVersion.rectLen_le_exp_of_abs_sub_le ξ d _ _ a
          (by intro z hz; simpa only [abs_sub_comm] using hω hb z hz) hle)
    calc
      P {ω | rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) ≤ a}
          ≤ P ({ω | rectLen ξ (fun z => phiVer W P ε 1 z ω) (rectAB 1 1) ≤
              ENNReal.ofReal (Real.exp (|ξ| * d)) * a} ∪ bad) := measure_mono_ae hinc
      _ ≤ P {ω | rectLen ξ (fun z => phiVer W P ε 1 z ω) (rectAB 1 1) ≤
              ENNReal.ofReal (Real.exp (|ξ| * d)) * a} + P bad :=
        measure_union_le _ _
      _ ≤ _ := by simpa only [d] using add_le_add_right hbad _


 

theorem dyadic_quantile_sandwich
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ξ : ℝ) (m : ℕ) :
    let K := Real.sqrt (2 * ξ ^ 2 * Real.log 2) / (1 / 8 : ℝ)
    Real.exp (-K * Real.sqrt m) * lambdaN ξ W P m ≤
      ellN ξ W P m (ENNReal.ofReal (1 / 8 : ℝ)) ∧
    ellBarN ξ W P m (ENNReal.ofReal (1 / 8 : ℝ)) ≤
      Real.exp (K * Real.sqrt m) * lambdaN ξ W P m := by
  letI := hW.isProbabilityMeasure
  dsimp
  let q : ℝ≥0∞ := ENNReal.ofReal (1 / 8 : ℝ)
  have hq0 : 0 < q := ENNReal.ofReal_pos.mpr (by norm_num)
  have hqhalf : q ≤ 2⁻¹ := by
    have heq : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [← heq]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hq1 : q < 1 := hqhalf.trans_lt inv_two_lt_one'
  have hlow0 : 0 < ellN ξ W P m q := T20B.ellN_pos hW hq0 hq1 m
  have hLoMed : ellN ξ W P m q ≤ lambdaN ξ W P m :=
    T20B.ellN_le_lambdaN hq0 hqhalf m
  have hMedHi : lambdaN ξ W P m ≤ ellBarN ξ W P m q :=
    T20B.lambdaN_le_ellBarN hq0 hqhalf m
  let K : ℝ := Real.sqrt (2 * ξ ^ 2 * Real.log 2) / (1 / 8 : ℝ)
  let e : ℝ := Real.exp (K * Real.sqrt m)
  have he : 0 < e := Real.exp_pos _
  have hratio : ellBarN ξ W P m q / ellN ξ W P m q ≤ e := by
    have hpoint : ellBarN ξ W P m q / ellN ξ W P m q ≤
        LambdaN ξ W P m q := Finset.le_sup'
          (fun k => ellBarN ξ W P k q / ellN ξ W P k q)
          (Finset.mem_range.mpr (Nat.lt_succ_self m))
    exact hpoint.trans (Inputs.Gaussian.quantile_ratio_sqrt hW ξ (by norm_num)
      (by norm_num) m)
  have hHiLo : ellBarN ξ W P m q ≤ e * ellN ξ W P m q :=
    (div_le_iff₀ hlow0).mp hratio
  have hMedLo : lambdaN ξ W P m ≤ e * ellN ξ W P m q :=
    hMedHi.trans hHiLo
  constructor
  · change Real.exp (-K * Real.sqrt m) * lambdaN ξ W P m ≤ ellN ξ W P m q
    calc
      Real.exp (-K * Real.sqrt m) * lambdaN ξ W P m =
          lambdaN ξ W P m / e := by
            rw [show -K * Real.sqrt m = -(K * Real.sqrt m) by ring, Real.exp_neg]
            simp only [e, div_eq_mul_inv, mul_comm]
      _ ≤ ellN ξ W P m q := (div_le_iff₀ he).mpr (by simpa [mul_comm] using hMedLo)
  · change ellBarN ξ W P m q ≤ Real.exp (K * Real.sqrt m) * lambdaN ξ W P m
    exact hHiLo.trans (mul_le_mul_of_nonneg_left hLoMed he.le)

 

theorem dyadic_octave_of_floor {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    let m := Nat.floor (Real.logb 2 (1 / ε))
    ((2 : ℝ) ^ m)⁻¹ / 2 ≤ ε ∧ ε ≤ ((2 : ℝ) ^ m)⁻¹ := by
  dsimp
  let r : ℝ := Real.logb 2 (1 / ε)
  let m : ℕ := Nat.floor r
  have hrec : 1 ≤ 1 / ε := by
    apply (le_div_iff₀ hε).mpr
    linarith
  have hr0 : 0 ≤ r := by
    change 0 ≤ Real.logb 2 (1 / ε)
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg hrec) (Real.log_pos (by norm_num)).le
  have hmle : (m : ℝ) ≤ r := Nat.floor_le hr0
  have hrle : r ≤ (m : ℝ) + 1 := by
    exact (Nat.lt_floor_add_one r).le
  have heps : ε = (2 : ℝ) ^ (-r) := by
    have hpow : (2 : ℝ) ^ r = 1 / ε :=
      Real.rpow_logb (by norm_num) (by norm_num) (div_pos one_pos hε)
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), hpow]
    field_simp
  have hb : ((2 : ℝ) ^ m)⁻¹ = (2 : ℝ) ^ (-(m : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hb2 : ((2 : ℝ) ^ m)⁻¹ / 2 =
      (2 : ℝ) ^ (-((m : ℝ) + 1)) := by
    rw [hb, neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  change ((2 : ℝ) ^ m)⁻¹ / 2 ≤ ε ∧ ε ≤ ((2 : ℝ) ^ m)⁻¹
  constructor
  · calc
      ((2 : ℝ) ^ m)⁻¹ / 2 = (2 : ℝ) ^ (-((m : ℝ) + 1)) := hb2
      _ ≤ (2 : ℝ) ^ (-r) := Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
      _ = ε := heps.symm
  · calc
      ε = (2 : ℝ) ^ (-r) := heps
      _ ≤ (2 : ℝ) ^ (-(m : ℝ)) := Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
      _ = ((2 : ℝ) ^ m)⁻¹ := hb.symm

 

theorem phiVer_crossing_cdf_eq_of_whiteNoise
    {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    {P : Measure Ω} {P₂ : Measure Ω₂}
    {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V)
    (ξ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (a : ℝ≥0∞) :
    P {ω | rectLen ξ (fun z => phiVer W P ε 1 z ω) (rectAB 1 1) < a} =
      P₂ {ω | rectLen ξ (fun z => phiVer V P₂ ε 1 z ω) (rectAB 1 1) < a} ∧
    P {ω | rectLen ξ (fun z => phiVer W P ε 1 z ω) (rectAB 1 1) ≤ a} =
      P₂ {ω | rectLen ξ (fun z => phiVer V P₂ ε 1 z ω) (rectAB 1 1) ≤ a} := by
  constructor
  · simpa only [rectLen, Set.mem_Iio] using
      (measure_crossLenIn_phiVer_eq (ξ := ξ) (K := (rectAB 1 1).toSet)
        (A := (rectAB 1 1).side₁) (B := (rectAB 1 1).side₂)
        (rectAB 1 1).isCompact_toSet hW hV hε hε1
        (S := Set.Iio a) measurableSet_Iio)
  · simpa only [rectLen, Set.mem_Iic] using
      (measure_crossLenIn_phiVer_eq (ξ := ξ) (K := (rectAB 1 1).toSet)
        (A := (rectAB 1 1).side₁) (B := (rectAB 1 1).side₂)
        (rectAB 1 1).isCompact_toSet hW hV hε hε1
        (S := Set.Iic a) measurableSet_Iic)

 

theorem dyadic_crossing_quantile_cdf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ξ : ℝ) (m : ℕ) (q : ℝ≥0∞) (hq0 : 0 < q) (hq1 : q < 1) :
    P {ω | rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) <
      ENNReal.ofReal (ellN ξ W P m q)} ≤ q ∧
    1 - q ≤ P {ω | rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) ≤
      ENNReal.ofReal (ellBarN ξ W P m q)} := by
  letI := hW.isProbabilityMeasure
  have hv := isPhiVersion_phiMN hW (Nat.zero_le m)
  have hfin (ω : Ω) : rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) ≠ ∞ :=
    rectLen_ne_top (rectAB 1 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) (hv.cont ω)
  have hqbar0 : 0 < 1 - q := tsub_pos_iff_lt.mpr hq1
  have hqbar1 : 1 - q < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0.ne'
  have hqhi : 0 < ellBarN ξ W P m q :=
    (Inputs.WhiteNoise.dyadic_square_quantile (ξ := ξ) hW m hqbar0 hqbar1).1
  have hlow := (Inputs.WhiteNoise.dyadic_square_quantile (ξ := ξ) hW m hq0 hq1).2.1
  have hhigh := (Inputs.WhiteNoise.dyadic_square_quantile (ξ := ξ) hW m hqbar0 hqbar1).2.2
  constructor
  · have he : {ω | rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) <
        ENNReal.ofReal (ellN ξ W P m q)} =
      {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 1) ω < ellN ξ W P m q} := by
      ext ω
      exact ENNReal.lt_ofReal_iff_toReal_lt (hfin ω)
    rw [he]
    exact hlow
  · have he : {ω | rectLen ξ (fun z => phiMN W P 0 m z ω) (rectAB 1 1) ≤
        ENNReal.ofReal (ellBarN ξ W P m q)} =
      {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 1) ω ≤ ellBarN ξ W P m q} := by
      ext ω
      exact ENNReal.le_ofReal_iff_toReal_le (hfin ω) hqhi.le
    rw [he]
    exact hhigh


end SupercriticalLQGUniqueness.Exponent.Median
