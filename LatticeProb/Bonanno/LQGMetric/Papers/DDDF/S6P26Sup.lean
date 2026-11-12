/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P26Sup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Eq698Main
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Obig
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mul

/-!
# DDDF Prop 26, Step 2: weak supermultiplicativity of `λ_n` for large `k` (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1311–1329. The pathwise inequality (5.75) (`eq:WeakSuperMul`, l. 1325–1328),
`L^{(n+k)}_{1,1} ≥ L^{(k)}_{1,1} (min_{P, i} 2^k L^{(k,k+n)}(R_i^S(P))) e^{-2ξ max_P osc_P(φ_{0,k})}`,
is the open node `S6Eq5_75` (constants as in (5.67) = `T20Step4Den`; the oscillation through
`T20C.Obig`). `s6_eq5_76_low_large` is DDDF's probabilistic step (l. 1329): Cor 17 for the
`≤ C 4^k` short rectangles (union bound, scaling `T20B.law_mrectLen`) and for `L^{(k)}_{1,1}`,
the gradient bound (`S6.obig_tail`), `Λ_∞ < ∞`, and the median. DDDF's last sentence
("with probability `≥ 1/2`, `L^{(n)}_{1,1} ≤ e^{-C√k} λ_n λ_k`") is read as
`P(L^{(n+k)}_{1,1} < e^{-C√k} λ_n λ_k) < 1/2`; we use `P(L^{(k)}_{1,1} < e^{-A√k} λ_k / B)` small
(instead of `L^{(k)} ≥ λ_k` with probability `1/2`, which does not give a median bound).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise S6 T20C

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- **DDDF (5.75)** (`eq:WeakSuperMul`, l. 1316–1328), pathwise, with the short rectangles
`R_i^S(P)` given as a family `J'` of `≤ C₁ 4^k` similarities `u 2^{-k} R_{1,3} + c`. Open. -/
def S6Eq5_75 (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ n : ℕ, 1 ≤ n →
    ∃ (J' : Finset (Circle × ℂ)) (hJ' : J'.Nonempty), ((J'.card : ℝ) ≤ C₁ * 4 ^ k) ∧
      ∀ Y : ℂ → Ω → ℝ, (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ k)⁻¹ 1 x) →
        (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
        ∀ᵐ ω ∂P, Real.exp (-(C₁ * Obig k Y ω)) *
          ((2 : ℝ) ^ k * minShort ξ W P k (n + k) J' hJ' ω) * lenN ξ W P 1 1 k ω ≤
            C₁ * lenN ξ W P 1 1 (n + k) ω

/-- **DDDF Prop 26, Step 2** (l. 1329) for `k` large: `λ_{n+k} ≥ e^{-C√k} λ_n λ_k`. -/
theorem s6_eq5_76_low_large (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B)
    (h75 : S6Eq5_75 ξ W P) :
    ∃ C : ℝ, ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k → ∀ n : ℕ, 1 ≤ n →
      Real.exp (-(C * √(k : ℝ))) * lambdaN ξ W P n * lambdaN ξ W P k ≤ lambdaN ξ W P (n + k) := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨p₁, hp₁, h17⟩ := dddf_cor17 (P := P) hW hξ
  obtain ⟨p₀, hp₀, hΛp⟩ := hΛ
  set p : ℝ := min p₁ (min p₀ (1 / 2))
  have hp : 0 < p := lt_min hp₁ (lt_min hp₀ (by norm_num))
  have hp1 : p ≤ p₁ := min_le_left _ _
  have hp0 : p ≤ p₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hph : p ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C₇, c₇, hC₇, hc₇, t17⟩ := h17 p hp hp1
  obtain ⟨B₀, hB₀⟩ := hΛp p hp hp0
  set B := max B₀ 1
  have hB1 : 1 ≤ B := le_max_right _ _
  have hB : ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B :=
    fun n => (hB₀ n).trans (le_max_left _ _)
  obtain ⟨C₁, hC₁, k₀, h75⟩ := h75
  obtain ⟨M, hM0, k₂, hob⟩ := obig_tail (ε := 1 / 8) (by norm_num)
  -- `A` with `(C₁ + 1) C₇ 4^k e^{-c₇ A² k} ≤ 1/8` for `k ≥ 1`
  set D : ℝ := 8 * ((C₁ + 1) * C₇) + 1
  have hD1 : 1 ≤ D := by have : 0 ≤ (C₁ + 1) * C₇ := by positivity
                         simp only [D]; linarith
  set A : ℝ := √((Real.log 4 + Real.log D) / c₇)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hA2 : A ^ 2 = (Real.log 4 + Real.log D) / c₇ := Real.sq_sqrt (by positivity)
  have hA0 : 0 < A := Real.sqrt_pos.2 (by positivity)
  have htail : ∀ k : ℕ, 1 ≤ k →
      (C₁ + 1) * C₇ * 4 ^ k * Real.exp (-c₇ * (A * √(k : ℝ)) ^ 2) ≤ 1 / 8 := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have e1 : -c₇ * (A * √(k : ℝ)) ^ 2 = -(k * Real.log 4) - k * Real.log D := by
      rw [mul_pow, hA2, Real.sq_sqrt (by positivity)]; field_simp; ring
    have e2 : Real.exp (-(k * Real.log 4)) = (4 ^ k)⁻¹ := by
      rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity)]
    have e3 : Real.exp (-(k * Real.log D)) ≤ D⁻¹ := by
      rw [Real.exp_neg, mul_comm, Real.exp_mul, Real.exp_log (by linarith)]
      exact inv_anti₀ (by linarith) (by
        calc D = D ^ (1 : ℝ) := (Real.rpow_one D).symm
          _ ≤ D ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 hk1)
    rw [e1, sub_eq_add_neg, Real.exp_add, e2]
    have h4 : (0 : ℝ) < 4 ^ k := by positivity
    calc (C₁ + 1) * C₇ * 4 ^ k * ((4 ^ k)⁻¹ * Real.exp (-(k * Real.log D)))
        = (C₁ + 1) * C₇ * Real.exp (-(k * Real.log D)) := by field_simp
      _ ≤ (C₁ + 1) * C₇ * D⁻¹ := mul_le_mul_of_nonneg_left e3 (by positivity)
      _ ≤ 1 / 8 := by
          rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]; simp only [D]; linarith
  set k₁ := max k₀ (max k₂ 1)
  refine ⟨C₁ * M + 2 * A + |Real.log C₁| + 2 * Real.log B, k₁, fun k hk n hn => ?_⟩
  have hk0 : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk2 : k₂ ≤ k := ((le_max_left _ _).trans (le_max_right _ _)).trans hk
  have hk1' : 1 ≤ k := ((le_max_right _ _).trans (le_max_right _ _)).trans hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1'
  have hsk : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.2 hk1
  set s := A * √(k : ℝ)
  have hs0 : 0 < s := by positivity
  obtain ⟨J', hJ', hcard, hpath⟩ := h75 k hk0 n hn
  obtain ⟨Y, -, hYa, -, hYc, -⟩ := exists_C1_modification_phi hW (a := ((2 : ℝ) ^ k)⁻¹) (b := 1)
    (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hH := hpath Y hYa hYc
  -- quantile facts
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp
  have hpq : ENNReal.ofReal p ≤ 2⁻¹ := (ENNReal.ofReal_le_ofReal hph).trans_eq ofReal_half_eq'
  have hlamB : ∀ m : ℕ, lambdaN ξ W P m ≤ B * ellN ξ W P m (ENNReal.ofReal p) := fun m => by
    have hℓ0 := T20B.ellN_pos hW hpq0 (lt_of_le_of_lt hpq inv_two_lt_one') m (ξ := ξ)
    have hΛm : ellBarN ξ W P m (ENNReal.ofReal p) / ellN ξ W P m (ENNReal.ofReal p) ≤
        LambdaN ξ W P m (ENNReal.ofReal p) :=
      Finset.le_sup' (fun k => ellBarN ξ W P k (ENNReal.ofReal p) / ellN ξ W P k (ENNReal.ofReal p))
        (Finset.self_mem_range_succ m)
    have := (div_le_iff₀ hℓ0).1 (hΛm.trans (hB m))
    linarith [T20B.lambdaN_le_ellBarN (ξ := ξ) (W := W) (P := P) hpq0 hpq m]
  have hlam0 : ∀ m : ℕ, 0 < lambdaN ξ W P m := fun m => lambdaN_pos hW m
  -- Cor 17 in the form `P(L^{(m)}_{1,3} < e^{-s} λ_m / B) ≤ C₇ e^{-c₇ s²}`
  have hc17 : ∀ m : ℕ, P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω <
      Real.exp (-s) * lambdaN ξ W P m / B} ≤ ENNReal.ofReal (C₇ * Real.exp (-c₇ * s ^ 2)) := by
    intro m
    refine (measure_mono fun ω hω => ?_).trans (t17 m s hs0)
    have hω' : lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω < Real.exp (-s) * lambdaN ξ W P m / B := hω
    have h2 : Real.exp (-s) * lambdaN ξ W P m / B ≤ Real.exp (-s) * ellN ξ W P m (ENNReal.ofReal p) := by
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [div_le_iff₀ (by linarith)]; linarith [hlamB m]
    show lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω ≤ Real.exp (-s) * ellN ξ W P m (ENNReal.ofReal p)
    linarith
  have e17 : C₇ * Real.exp (-c₇ * s ^ 2) ≤ 1 / 8 := by
    have := htail k hk1'
    have h4 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have hX : 0 ≤ C₇ * Real.exp (-c₇ * s ^ 2) := by positivity
    nlinarith
  -- bad events
  set t₁ := Real.exp (-s) * lambdaN ξ W P n / B
  set t₃ := Real.exp (-s) * lambdaN ξ W P k / B
  set B1 := {ω | (2 : ℝ) ^ k * minShort ξ W P k (n + k) J' hJ' ω < t₁}
  set B2 := {ω | M * √(k : ℝ) ≤ Obig k Y ω}
  set B3 := {ω | lenN ξ W P 1 1 k ω < t₃}
  set B0 := {ω | ¬ (Real.exp (-(C₁ * Obig k Y ω)) *
          ((2 : ℝ) ^ k * minShort ξ W P k (n + k) J' hJ' ω) * lenN ξ W P 1 1 k ω ≤
            C₁ * lenN ξ W P 1 1 (n + k) ω)}
  have hPB0 : P B0 = 0 := ae_iff.1 hH
  have hPB2 : P B2 ≤ ENNReal.ofReal (1 / 8) := hob hW k hk2 Y hYa hYc
  have hPB3 : P B3 ≤ ENNReal.ofReal (1 / 8) := by
    refine (measure_mono fun ω hω => ?_).trans ((hc17 k).trans (ENNReal.ofReal_le_ofReal e17))
    have hω' : lenN ξ W P 1 1 k ω < t₃ := hω
    have := T20B.lenObs_13_le_11 (ξ := ξ) (isPhiVersion_phiMN hW (Nat.zero_le k)).cont ω
    show lenObs ξ (phiMN W P 0 k) (rectAB 1 3) ω < t₃
    exact lt_of_le_of_lt this hω'
  have hPB1 : P B1 ≤ ENNReal.ofReal (1 / 8) := by
    have hsub : B1 ⊆ ⋃ j ∈ J', {ω | T20B.mrectLen ξ (fun x => phiMN W P k (n + k) x ω) k j.1 j.2 1 3
        ∈ Iio ((2 : ℝ)⁻¹ ^ k * t₁)} := by
      intro ω hω
      have hω' : (2 : ℝ) ^ k * minShort ξ W P k (n + k) J' hJ' ω < t₁ := hω
      have h2 : minShort ξ W P k (n + k) J' hJ' ω < (2 : ℝ)⁻¹ ^ k * t₁ := by
        rw [inv_pow, ← div_eq_inv_mul, lt_div_iff₀ (by positivity), mul_comm]; exact hω'
      obtain ⟨j, hj, hjlt⟩ := (Finset.inf'_lt_iff hJ').1 h2
      exact mem_biUnion hj hjlt
    have hone : ∀ j ∈ J', P {ω | T20B.mrectLen ξ (fun x => phiMN W P k (n + k) x ω) k j.1 j.2 1 3
        ∈ Iio ((2 : ℝ)⁻¹ ^ k * t₁)} ≤ ENNReal.ofReal (C₇ * Real.exp (-c₇ * s ^ 2)) := by
      intro j _
      rw [T20B.law_mrectLen hW (by omega) j.1 j.2 1 3 measurableSet_Iio]
      refine le_trans (le_of_eq ?_) (hc17 n)
      congr 1; ext ω
      simp only [mem_ofPred_eq, mem_Iio, Nat.add_sub_cancel]
      exact mul_lt_mul_iff_right₀ (by positivity)
    refine (measure_mono (μ := P) hsub).trans ((measure_biUnion_finset_le (μ := P) J' _).trans ?_)
    refine (Finset.sum_le_sum hone).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := htail k hk1'
    have hX : 0 ≤ C₇ * Real.exp (-c₇ * s ^ 2) := by positivity
    calc (J'.card : ℝ) * (C₇ * Real.exp (-c₇ * s ^ 2))
        ≤ (C₁ * 4 ^ k) * (C₇ * Real.exp (-c₇ * s ^ 2)) := mul_le_mul_of_nonneg_right hcard hX
      _ ≤ (C₁ + 1) * C₇ * 4 ^ k * Real.exp (-c₇ * (A * √(k : ℝ)) ^ 2) := by
          have h4 : (0 : ℝ) ≤ 4 ^ k := by positivity
          have : C₁ * 4 ^ k * (C₇ * Real.exp (-c₇ * s ^ 2)) ≤
              (C₁ + 1) * 4 ^ k * (C₇ * Real.exp (-c₇ * s ^ 2)) := by gcongr; linarith
          linarith
      _ ≤ 1 / 8 := this
  -- the median bound
  set m := C₁⁻¹ * Real.exp (-(C₁ * (M * √(k : ℝ)))) * t₁ * t₃
  have hlenm : Measurable (lenN ξ W P 1 1 (n + k)) := measurable_lenMN hW 1 1 (Nat.zero_le _)
  have hmed : m ≤ lambdaN ξ W P (n + k) := by
    refine le_lowerMedian_of hlenm ?_
    have hsub : {ω | lenN ξ W P 1 1 (n + k) ω < m} ⊆ B0 ∪ B1 ∪ B2 ∪ B3 := by
      intro ω hω
      by_contra hn
      simp only [mem_union, not_or] at hn
      obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hn
      simp only [B0, B1, B2, B3, mem_ofPred_eq, not_not, not_lt, not_le] at h0 h1 h2 h3
      have hω' : lenN ξ W P 1 1 (n + k) ω < m := hω
      have hexp : Real.exp (-(C₁ * (M * √(k : ℝ)))) ≤ Real.exp (-(C₁ * Obig k Y ω)) :=
        Real.exp_le_exp.2 (by nlinarith)
      have ht₁ : 0 ≤ t₁ := div_nonneg (mul_nonneg (Real.exp_pos _).le (hlam0 n).le) (by linarith)
      have ht₃ : 0 ≤ t₃ := div_nonneg (mul_nonneg (Real.exp_pos _).le (hlam0 k).le) (by linarith)
      have hprod : Real.exp (-(C₁ * (M * √(k : ℝ)))) * t₁ * t₃ ≤
          Real.exp (-(C₁ * Obig k Y ω)) * ((2 : ℝ) ^ k * minShort ξ W P k (n + k) J' hJ' ω) *
            lenN ξ W P 1 1 k ω := by
        apply mul_le_mul (mul_le_mul hexp h1 ht₁ (Real.exp_pos _).le) h3 ht₃
        exact mul_nonneg (Real.exp_pos _).le (ht₁.trans h1)
      have : m * C₁ ≤ C₁ * lenN ξ W P 1 1 (n + k) ω := by
        calc m * C₁ = Real.exp (-(C₁ * (M * √(k : ℝ)))) * t₁ * t₃ := by
              simp only [m]; field_simp
          _ ≤ _ := hprod.trans h0
      nlinarith
    calc P {ω | lenN ξ W P 1 1 (n + k) ω < m} ≤ P B0 + P B1 + P B2 + P B3 :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add
            ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))
      _ ≤ 0 + ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) := by
          rw [hPB0]; gcongr
      _ < 2⁻¹ := by
          rw [zero_add, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ofReal_half_eq',
            ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
          norm_num
  refine le_trans ?_ hmed
  -- `e^{-C√k} λ_n λ_k ≤ m`
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hm : m = Real.exp (-(C₁ * M * √(k : ℝ) + 2 * s + Real.log C₁ + 2 * Real.log B)) *
      lambdaN ξ W P n * lambdaN ξ W P k := by
    simp only [m, t₁, t₃]
    rw [show -(C₁ * M * √(k : ℝ) + 2 * s + Real.log C₁ + 2 * Real.log B) =
        -(C₁ * (M * √(k : ℝ))) + -s + -s + -Real.log C₁ + -Real.log B + -Real.log B by ring]
    simp only [Real.exp_add, Real.exp_neg, Real.exp_log hC₁, Real.exp_log (by linarith : (0:ℝ) < B)]
    field_simp
  rw [hm]
  have hl0 := hlam0 n
  have hl0' := hlam0 k
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
    hl0.le) hl0'.le
  have h1 : Real.log C₁ ≤ |Real.log C₁| * √(k : ℝ) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hsk)
  have h2 : 2 * Real.log B ≤ 2 * Real.log B * √(k : ℝ) :=
    le_mul_of_one_le_right (by positivity) hsk
  simp only [s]
  nlinarith

end DDDF
end LQGMetric
