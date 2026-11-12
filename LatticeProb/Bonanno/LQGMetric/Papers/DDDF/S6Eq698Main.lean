/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Eq698Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Eq698
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CGather

/-!
# DDDF (6.98) (`eq:AprioriMul`, l. 1608–1613) (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`.
`s6_eq6_98_of_Lambda`: (6.98) from bounded quantile ratios `Λ_∞(φ, p) < ∞`, following DDDF's
proof (see `S6Eq698.lean`). `s6_eq6_98`: the same from the hypotheses of DDDF Theorem 20
(`dddf_thm20_of_num_den`: Condition (T) and the two pathwise estimates of Step 4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise S6

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

lemma two_rpow_split (n : ℕ) (r : ℝ) :
    (2 : ℝ) ^ (-((n : ℝ) + r)) = (2 : ℝ) ^ (-r) * (2 : ℝ)⁻¹ ^ n := by
  rw [neg_add, Real.rpow_add two_pos, Real.rpow_neg two_pos.le (n : ℝ), Real.rpow_natCast,
    ← inv_pow, mul_comm]

lemma ofReal_half_eq' : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

lemma three_eighths_lt_half :
    0 + ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) < (2⁻¹ : ℝ≥0∞) := by
  rw [zero_add, ← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ofReal_half_eq',
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- **DDDF (6.98)** from `Λ_∞(φ, p) < ∞` for small `p` (DDDF l. 1608–1613). -/
theorem s6_eq6_98_of_Lambda (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) :
    S6Eq6_98 ξ W P := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨p₁, hp₁, h17⟩ := dddf_cor17 (P := P) hW hξ
  obtain ⟨p₂, hp₂, h18⟩ := dddf_prop18 (P := P) hW hξ
  obtain ⟨p₀, hp₀, hΛp⟩ := hΛ
  set p : ℝ := min (min p₁ p₂) (min p₀ (1 / 2))
  have hp : 0 < p := lt_min (lt_min hp₁ hp₂) (lt_min hp₀ (by norm_num))
  have hp1 : p ≤ p₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hp2 : p ≤ p₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hp0 : p ≤ p₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hph : p ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C₇, c₇, hC₇, hc₇, t17⟩ := h17 p hp hp1
  obtain ⟨C₈, c₈, hC₈, hc₈, t18⟩ := h18 p hp hp2
  obtain ⟨B₀, hB₀⟩ := hΛp p hp hp0
  set B := max B₀ 1
  have hB1 : 1 ≤ B := le_max_right _ _
  have hB : ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B :=
    fun n => (hB₀ n).trans (le_max_left _ _)
  obtain ⟨M, hM0, hMt⟩ := low_sup_tail hW (ε := 1 / 8) (by norm_num)
  set s : ℝ := max 3 (max (Real.log (2 * C₇ / (1 / 4)) / c₇) (Real.log (2 * C₈ / (1 / 4)) / c₈))
  have hs3 : 3 ≤ s := le_max_left _ _
  have hs7 : Real.log (2 * C₇ / (1 / 4)) / c₇ ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hs8 : Real.log (2 * C₈ / (1 / 4)) / c₈ ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  have e7 : C₇ * Real.exp (-c₇ * s ^ 2) ≤ 1 / 8 := by
    have h := T20B.mul_exp_neg_le_half hC₇ hc₇ (by norm_num : (0 : ℝ) < 1 / 4) hs7
    have h' : C₇ * Real.exp (-c₇ * s ^ 2) ≤ C₇ * Real.exp (-(c₇ * s)) := by
      gcongr
      have hss : s ≤ s ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hss hc₇.le]
    linarith
  have e8 : C₈ * Real.exp (-c₈ * s ^ 2 / Real.log s) ≤ 1 / 8 := by
    have h := T20B.mul_exp_neg_le_half hC₈ hc₈ (by norm_num : (0 : ℝ) < 1 / 4) hs8
    have hl : 0 < Real.log s := Real.log_pos (by linarith)
    have hls : Real.log s ≤ s := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hq : s ≤ s ^ 2 / Real.log s := by rw [le_div_iff₀ hl]; nlinarith
    have h' : C₈ * Real.exp (-c₈ * s ^ 2 / Real.log s) ≤ C₈ * Real.exp (-(c₈ * s)) := by
      gcongr
      rw [neg_mul, neg_div, neg_le_neg_iff, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hq hc₈.le
    linarith
  set K := |ξ| * M + s + Real.log B + Real.log 2
  refine ⟨K, fun n r hr0 hr1 => ?_⟩
  set a : ℝ := (2 : ℝ) ^ (-r)
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have ha12 : 1 / 2 ≤ a := by
    have : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (-r) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at this
  have ha0 : 0 < a := by positivity
  rw [two_rpow_split n r]
  have hd0 : 0 < a * (2 : ℝ)⁻¹ ^ n := by positivity
  have hda : a * (2 : ℝ)⁻¹ ^ n ≤ a :=
    mul_le_of_le_one_right ha0.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hY := isPhiVersion_phiVer hW hd0 (hda.trans ha1)
  have hLo := isPhiVersion_phiVer hW ha0 ha1
  have hHi := isPhiVersion_phiVer hW hd0 hda
  have hZ := isPhiVersion_phiMN hW (Nat.zero_le n)
  set Y := phiVer W P (a * (2 : ℝ)⁻¹ ^ n) 1
  set Lo := phiVer W P a 1
  set Hi := phiVer W P (a * (2 : ℝ)⁻¹ ^ n) a
  set Z := phiMN W P 0 n
  -- a.s. `Y = Lo + Hi` (DDDF l. 1613, `φ_{0,n+r} = φ_{0,r} + φ_{r,n+r}`)
  have hG : ∀ᵐ ω ∂P, ∀ x, Y x ω = Lo x ω + Hi x ω := by
    refine ae_eq_of_continuous_modification (Y₂ := fun x ω => Lo x ω + Hi x ω) hY.cont
      (fun ω => (hLo.cont ω).add (hHi.cont ω)) fun x => ?_
    filter_upwards [hY.ae_eq x, hLo.ae_eq x, hHi.ae_eq x, phi_add_ae hW hd0 hda ha1 x] with
      ω h1 h2 h3 h4
    rw [h1, h4, h2, h3]; ring
  have hGc : P {ω | ¬ ∀ x, Y x ω = Lo x ω + Hi x ω} = 0 := ae_iff.1 hG
  -- quantiles
  set lamn := lambdaN ξ W P n
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp
  have hpq : ENNReal.ofReal p ≤ 2⁻¹ := (ENNReal.ofReal_le_ofReal hph).trans_eq ofReal_half_eq'
  have hℓ0 : 0 < ellN ξ W P n (ENNReal.ofReal p) :=
    T20B.ellN_pos hW hpq0 (lt_of_le_of_lt hpq inv_two_lt_one') n
  have hℓlam_ : ellN ξ W P n (ENNReal.ofReal p) ≤ lamn := T20B.ellN_le_lambdaN hpq0 hpq n
  have hlam_ℓb : lamn ≤ ellBarN ξ W P n (ENNReal.ofReal p) := T20B.lambdaN_le_ellBarN hpq0 hpq n
  have hΛn : ellBarN ξ W P n (ENNReal.ofReal p) / ellN ξ W P n (ENNReal.ofReal p) ≤
      LambdaN ξ W P n (ENNReal.ofReal p) :=
    Finset.le_sup' (fun k => ellBarN ξ W P k (ENNReal.ofReal p) / ellN ξ W P k (ENNReal.ofReal p))
      (Finset.self_mem_range_succ n)
  have hlam_B : lamn ≤ B * ellN ξ W P n (ENNReal.ofReal p) := by
    have := (div_le_iff₀ hℓ0).1 (hΛn.trans (hB n)); linarith
  have hlam_0 : 0 < lamn := hℓ0.trans_le hℓlam_
  -- the shapes
  set c := a⁻¹
  have hc1 : 1 ≤ c := one_le_inv_iff₀.2 ⟨ha0, ha1⟩
  have hc2 : c ≤ 2 := by
    rw [inv_le_comm₀ ha0 (by norm_num)]; linarith
  -- Prop 18 + Λ bounded: `P(L^{(n)}_{c,c} > e^s B lam__n) ≤ 1/8`
  have hup : P {ω | Real.exp s * B * lamn < lenObs ξ Z (rectAB c c) ω} ≤
      ENNReal.ofReal (1 / 8) := by
    refine (measure_mono fun ω hω => ?_).trans
      ((t18 n s (by linarith)).trans (ENNReal.ofReal_le_ofReal e8))
    have h1 := lenObs_rectAB_mono (ξ := ξ) hZ.cont (x := c) (X := 3) (y := 1) (y' := c)
      (by linarith) (by linarith) zero_le_one hc1 ω
    have h2 : Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
        Real.exp s * B * lamn := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hB n) hℓlam_ hℓ0.le (by linarith))
        (Real.exp_pos _).le
    have hω' : Real.exp s * B * lamn < lenObs ξ Z (rectAB c c) ω := hω
    show Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
      lenObs ξ Z (rectAB 3 1) ω
    linarith
  -- Cor 17 + Λ bounded: `P(L^{(n)}_{c,c} < e^{-s} lam__n / B) ≤ 1/8`
  have hlow : P {ω | lenObs ξ Z (rectAB c c) ω < Real.exp (-s) * lamn / B} ≤
      ENNReal.ofReal (1 / 8) := by
    refine (measure_mono fun ω hω => ?_).trans
      ((t17 n s (by linarith)).trans (ENNReal.ofReal_le_ofReal e7))
    have h1 := lenObs_rectAB_mono (ξ := ξ) hZ.cont (x := 1) (X := c) (y := c) (y' := 3)
      zero_le_one hc1 (by linarith) (by linarith) ω
    have h2 : Real.exp (-s) * lamn / B ≤ Real.exp (-s) * ellN ξ W P n (ENNReal.ofReal p) := by
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [div_le_iff₀ (by linarith)]; linarith
    have hω' : lenObs ξ Z (rectAB c c) ω < Real.exp (-s) * lamn / B := hω
    show lenObs ξ Z (rectAB 1 3) ω ≤ Real.exp (-s) * ellN ξ W P n (ENNReal.ofReal p)
    linarith
  -- transfer to `Hi` by scaling
  have hlaw : ∀ (S : Set ℝ), MeasurableSet S →
      P {ω | lenObs ξ Hi (rectAB 1 1) ω ∈ S} = P {ω | a * lenObs ξ Z (rectAB c c) ω ∈ S} :=
    fun S hS => law_hi hW n ha0 hS
  have hupH : P {ω | a * (Real.exp s * B * lamn) < lenObs ξ Hi (rectAB 1 1) ω} ≤
      ENNReal.ofReal (1 / 8) := by
    have := hlaw (Ioi (a * (Real.exp s * B * lamn))) measurableSet_Ioi
    simp only [mem_Ioi] at this
    rw [this]
    refine le_of_eq_of_le (congrArg P (Set.ext fun ω => ?_)) hup
    exact ⟨fun h => lt_of_mul_lt_mul_left h ha0.le, fun h => mul_lt_mul_of_pos_left h ha0⟩
  have hlowH : P {ω | lenObs ξ Hi (rectAB 1 1) ω < a * (Real.exp (-s) * lamn / B)} ≤
      ENNReal.ofReal (1 / 8) := by
    have := hlaw (Iio (a * (Real.exp (-s) * lamn / B))) measurableSet_Iio
    simp only [mem_Iio] at this
    rw [this]
    refine le_of_eq_of_le (congrArg P (Set.ext fun ω => ?_)) hlow
    exact ⟨fun h => lt_of_mul_lt_mul_left h ha0.le, fun h => mul_lt_mul_of_pos_left h ha0⟩
  set E1 := {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |Lo x ω| ≤ M}
  have hE1 : P E1 ≤ ENNReal.ofReal (1 / 8) := hMt a ha12 ha1
  have hYm : Measurable (lenObs ξ Y (rectAB 1 1)) := measurable_lenObs hY.cont hY.meas _
  have eK : Real.exp K = Real.exp (|ξ| * M) * Real.exp s * B * 2 := by
    simp only [K]
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by linarith),
      Real.exp_log two_pos]
  have eK' : Real.exp (-K) = Real.exp (-(|ξ| * M)) * Real.exp (-s) * B⁻¹ * 2⁻¹ := by
    rw [Real.exp_neg, eK, Real.exp_neg, Real.exp_neg]; field_simp
  constructor
  · -- lower bound
    set t := a * (Real.exp (-s) * lamn / B)
    have hmain : Real.exp (-K) * lamn ≤ Real.exp (-(|ξ| * M)) * t := by
      rw [eK']
      have hX : 0 ≤ Real.exp (-(|ξ| * M)) * Real.exp (-s) * lamn * B⁻¹ := by positivity
      simp only [t, div_eq_mul_inv]
      nlinarith
    refine hmain.trans (le_lowerMedian_of hYm ?_)
    have hsub : {ω | lenObs ξ Y (rectAB 1 1) ω < Real.exp (-(|ξ| * M)) * t} ⊆
        {ω | ¬ ∀ x, Y x ω = Lo x ω + Hi x ω} ∪ E1 ∪
          {ω | lenObs ξ Hi (rectAB 1 1) ω < t} := by
      intro ω hω
      by_contra hn
      simp only [mem_union, not_or] at hn
      obtain ⟨⟨h1, h2⟩, h3⟩ := hn
      simp only [mem_ofPred_eq, not_not, E1] at h1 h2 h3
      have hcmp := (len_cmp (ξ := ξ) (hY.cont ω) (hHi.cont ω) h1 h2).1
      have hω' : lenObs ξ Y (rectAB 1 1) ω < Real.exp (-(|ξ| * M)) * t := hω
      have h3' : t ≤ lenObs ξ Hi (rectAB 1 1) ω := not_lt.1 h3
      have := mul_le_mul_of_nonneg_left h3' (Real.exp_pos (-(|ξ| * M))).le
      linarith
    calc P {ω | lenObs ξ Y (rectAB 1 1) ω < Real.exp (-(|ξ| * M)) * t}
        ≤ P {ω | ¬ ∀ x, Y x ω = Lo x ω + Hi x ω} + P E1 +
            P {ω | lenObs ξ Hi (rectAB 1 1) ω < t} :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) le_rfl))
      _ ≤ 0 + ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) := by
          rw [hGc]; gcongr
      _ < 2⁻¹ := three_eighths_lt_half
  · -- upper bound
    set t := a * (Real.exp s * B * lamn)
    have hmain : Real.exp (|ξ| * M) * t ≤ Real.exp K * lamn := by
      rw [eK]
      have hX : 0 ≤ Real.exp (|ξ| * M) * Real.exp s * B * lamn := by positivity
      simp only [t]
      nlinarith
    refine (lowerMedian_le_of hYm ?_).trans hmain
    have hsub : {ω | Real.exp (|ξ| * M) * t < lenObs ξ Y (rectAB 1 1) ω} ⊆
        {ω | ¬ ∀ x, Y x ω = Lo x ω + Hi x ω} ∪ E1 ∪
          {ω | t < lenObs ξ Hi (rectAB 1 1) ω} := by
      intro ω hω
      by_contra hn
      simp only [mem_union, not_or] at hn
      obtain ⟨⟨h1, h2⟩, h3⟩ := hn
      simp only [mem_ofPred_eq, not_not, E1] at h1 h2 h3
      have hcmp := (len_cmp (ξ := ξ) (hY.cont ω) (hHi.cont ω) h1 h2).2
      have hω' : Real.exp (|ξ| * M) * t < lenObs ξ Y (rectAB 1 1) ω := hω
      have h3' : lenObs ξ Hi (rectAB 1 1) ω ≤ t := not_lt.1 h3
      have := mul_le_mul_of_nonneg_left h3' (Real.exp_pos (|ξ| * M)).le
      linarith
    calc P {ω | Real.exp (|ξ| * M) * t < lenObs ξ Y (rectAB 1 1) ω}
        ≤ P {ω | ¬ ∀ x, Y x ω = Lo x ω + Hi x ω} + P E1 +
            P {ω | t < lenObs ξ Hi (rectAB 1 1) ω} :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) le_rfl))
      _ ≤ 0 + ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) := by
          rw [hGc]; gcongr
      _ < 2⁻¹ := three_eighths_lt_half

/-- **DDDF (6.98)** from the hypotheses of DDDF Theorem 20 (`dddf_thm20_of_num_den`). -/
theorem s6_eq6_98 (hW : IsWhiteNoise P W) (Q : PsiParams) (hQ : PsiSmall Q)
    (hε : Q.ε₀ < 1 / 2) (hξ : 0 < ξ) (hT : ConditionT ξ Q W P)
    (hN : T20Step4Num ξ Q W P) (hD : T20Step4Den ξ Q W P) : S6Eq6_98 ξ W P := by
  obtain ⟨p₀, hp₀, h⟩ := dddf_thm20_of_num_den hW Q hQ hε hξ hT hN hD
  exact s6_eq6_98_of_Lambda hW hξ ⟨p₀, hp₀, fun p hp hpp => (h p hp hpp).1⟩

end DDDF
end LQGMetric
