/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Comb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Max
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Zero

/-!
# DDDF Proposition 18: Step 2 completion and the combination (task P2-DDDF16c)

DDDF (arXiv:1904.08021, `tightness.tex` l. 868–945, Prop 18 = (4.49), upper tails for `φ`).

* `p18_mid` (Step 2 + Step 3, l. 912–929): for `1 ≤ m < n`, with `M := α(m + C√m)`,
  `α := log 4 + √(2^m m)/m` (DDDF: "`a = C + s m^{-1/2}` in Proposition 2", with `s = 2^{m/2}`),
  the split `dddf_p18_step2_split`, Prop 2 on `R_{3,1}` (`prop2_tail_R31`) for the first term,
  Step 1 at `n − m`, `k = 2^m` for the second term, and the threshold chain of l. 928
  `ℓ̄_{n−m}(p) ≤ Λ_{n−m}(p) ℓ_{n−m}(p) ≤ 2^{2ξm} e^{C√m} Λ_n(p) ℓ_n(p)` (Step 3).
  All exponents are bounded by `D √(2^m m)`.
* `dddf_prop18_of_steps` (l. 929, 937–938): `s² = 2^m` up to the factor `B log s` (DDDF take
  `s² = 2^m`, getting `e^{c s√log s}`; we invert that relation: `2^m ≍ s²/(B log s)`), Step 4
  (`dddf_p18_step4`) for `2^n ≤ s²`, `n = 0` from `dddf_p18_zero`, small `s` absorbed into `C`.

Step 1 (percolation, l. 900–910) and Step 3 (a priori bound, l. 921–927) enter through the
named statements `P18Step1`, `P18Step3` (verbatim the displays of DDDF l. 908 and l. 921), not
yet proved. The parameter bookkeeping is our own (DDDF give it in one line).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}

/-- **DDDF Prop 18, Step 1** (display after l. 908): `P(L^{(n)}_{3k,k}(φ) ≥ e^{ξC√k} C k²
ℓ̄_n(φ,p/2)) ≤ C e^{-ck}` (`C_p` absorbed into `C`). -/
def P18Step1 (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (n k : ℕ), 1 ≤ k →
    P {ω | Real.exp (ξ * C * √k) * C * k ^ 2 * ellBarN ξ W P n (ENNReal.ofReal (p / 2)) ≤
        lenObs ξ (phiMN W P 0 n) (rectAB (3 * k) k) ω} ≤
      ENNReal.ofReal (C * Real.exp (-(c * k)))

/-- **DDDF Prop 18, Step 3** (l. 921): `ℓ_n(φ,p) ≥ 2^{-2ξk} ℓ_{n−k}(φ,p) e^{-C√k}`, for `p`
small (DDDF use Cor 17, which holds for `p ≤ p₀`). -/
def P18Step3 (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, k ≤ n →
    (2 : ℝ) ^ (-(2 * ξ * k)) * ellN ξ W P (n - k) (ENNReal.ofReal p) *
        Real.exp (-(C * √k)) ≤ ellN ξ W P n (ENNReal.ofReal p)

/-- **DDDF Prop 18, Steps 2–3 for one scale `m`** (l. 912–929). -/
lemma p18_mid {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ) {p : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 1 / 2) {C₁ c₁ C₂ C₃ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hC₃ : 0 < C₃)
    (h1 : ∀ n k : ℕ, 1 ≤ k →
      P {ω | Real.exp (ξ * C₁ * √k) * C₁ * k ^ 2 * ellBarN ξ W P n (ENNReal.ofReal p) ≤
        lenObs ξ (phiMN W P 0 n) (rectAB (3 * k) k) ω} ≤
        ENNReal.ofReal (C₁ * Real.exp (-(c₁ * k))))
    (h2 : ∀ (m : ℕ) (α : ℝ), 0 < α →
      P.real {ω | α * (m + C₂ * Real.sqrt m) ≤
        ⨆ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω|} ≤
        3 * (C₂ * 4 ^ m * Real.exp (-α ^ 2 * m / Real.log 4)))
    (h3 : ∀ n k : ℕ, k ≤ n → (2 : ℝ) ^ (-(2 * ξ * k)) * ellN ξ W P (n - k) (ENNReal.ofReal p) *
        Real.exp (-(C₃ * √k)) ≤ ellN ξ W P n (ENNReal.ofReal p))
    (hℓ : ∀ n : ℕ, 1 ≤ n → 0 < ellN ξ W P n (ENNReal.ofReal p))
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {s : ℝ}
    (hs : (ξ * (1 + C₂) * (Real.log 4 + 1) + Real.log 2 + ξ * C₁ + |Real.log C₁| +
      2 * ξ * Real.log 2 + C₃) * √((2 : ℝ) ^ m * m) ≤ s) :
    P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
        lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
      ENNReal.ofReal (3 * C₂ * Real.exp (-((2 : ℝ) ^ m / Real.log 4))) +
        ENNReal.ofReal (C₁ * Real.exp (-(c₁ * (2 : ℝ) ^ m))) := by
  have := hW.isProbabilityMeasure
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2m : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hm2 : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  set Q : ℝ := √((2 : ℝ) ^ m * m) with hQ
  have hQ2 : Q ^ 2 = 2 ^ m * m := Real.sq_sqrt (by positivity)
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have hmQ : (m : ℝ) ≤ Q := by
    have e : (m : ℝ) = √((m : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    rw [e, hQ]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsmQ : √(m : ℝ) ≤ Q := Real.sqrt_le_sqrt (by nlinarith)
  have hs2Q : √((2 : ℝ) ^ m) ≤ Q := Real.sqrt_le_sqrt (by nlinarith)
  have h1Q : 1 ≤ Q := hm'.trans hmQ
  have hsm : √(m : ℝ) ≤ m := by rw [Real.sqrt_le_left (by positivity)]; nlinarith
  -- the Prop 2 level
  set α : ℝ := Real.log 4 + Q / m with hα
  have hQm : 0 ≤ Q / m := by positivity
  have hα0 : 0 < α := by positivity
  set M : ℝ := α * (m + C₂ * √m) with hMdef
  have hαm : α * m = Real.log 4 * m + Q := by
    simp only [α]; field_simp
  have hM : M ≤ (1 + C₂) * (Real.log 4 + 1) * Q := by
    have e1 : M ≤ α * ((1 + C₂) * m) := mul_le_mul_of_nonneg_left (by nlinarith) hα0.le
    have e2 : α * ((1 + C₂) * m) = (1 + C₂) * (Real.log 4 * m + Q) := by
      rw [← hαm]; ring
    have e3 : Real.log 4 * m + Q ≤ (Real.log 4 + 1) * Q := by
      nlinarith [mul_le_mul_of_nonneg_left hmQ hl4.le]
    nlinarith
  have hα2 : Real.log 4 ^ 2 * m + 2 ^ m ≤ α ^ 2 * m := by
    have e : (Q / m) ^ 2 * m = 2 ^ m := by
      rw [div_pow, hQ2]; field_simp
    have e' : α ^ 2 * m = Real.log 4 ^ 2 * m + 2 * Real.log 4 * (Q / m) * m + (Q / m) ^ 2 * m := by
      simp only [α]; ring
    rw [e', e]
    nlinarith [mul_nonneg (mul_nonneg hl4.le hQm) (by positivity : (0 : ℝ) ≤ m)]
  have hT1 : 3 * (C₂ * 4 ^ m * Real.exp (-α ^ 2 * m / Real.log 4)) ≤
      3 * C₂ * Real.exp (-((2 : ℝ) ^ m / Real.log 4)) := by
    have e4 : (4 : ℝ) ^ m = Real.exp (m * Real.log 4) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [e4, mul_assoc, ← Real.exp_add, ← mul_assoc]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have h := div_le_div_of_nonneg_right hα2 hl4.le
    have e5 : (Real.log 4 ^ 2 * m + 2 ^ m) / Real.log 4 = m * Real.log 4 + 2 ^ m / Real.log 4 := by
      field_simp
    rw [e5] at h
    rw [neg_mul, neg_div]
    linarith
  -- the Step 1 threshold
  set k : ℕ := 2 ^ m with hkdef
  have hk : (k : ℝ) = 2 ^ m := by simp [k]
  have hk1 : 1 ≤ k := Nat.one_le_two_pow
  set T : ℝ := Real.exp (ξ * C₁ * √k) * C₁ * k ^ 2 * ellBarN ξ W P (n - m) (ENNReal.ofReal p)
    with hTdef
  have hsplit := dddf_p18_step2_split (ξ := ξ) hW hmn.le (a := 3) (b := 1) (by norm_num)
    (by norm_num) M ((2 : ℝ)⁻¹ ^ m * T)
  have hR : rectAB ((2 : ℝ) ^ m * 3) ((2 : ℝ) ^ m * 1) = rectAB (3 * (k : ℝ)) k := by
    rw [hk]; congr 1 <;> ring
  have hE2 : {ω | (2 : ℝ)⁻¹ ^ m * T ≤ (2 : ℝ)⁻¹ ^ m *
      lenMN ξ W P ((2 : ℝ) ^ m * 3) ((2 : ℝ) ^ m * 1) 0 (n - m) ω} =
      {ω | T ≤ lenObs ξ (phiMN W P 0 (n - m)) (rectAB (3 * k) k) ω} := by
    ext ω
    simp only [mem_ofPred_eq, lenMN, hR]
    exact mul_le_mul_iff_of_pos_left (by positivity)
  rw [hE2] at hsplit
  -- the threshold chain (l. 928)
  have hℓn := hℓ n (by omega)
  have hℓnm := hℓ (n - m) (by omega)
  have hΛ1 : 1 ≤ LambdaN ξ W P n (ENNReal.ofReal p) := by
    have h := ellN_le_LambdaN_mul (ξ := ξ) (P := P) (W := W) hp0 hp hℓn
    exact le_of_mul_le_mul_right (by rw [one_mul]; exact h) hℓn
  have hbar : ellBarN ξ W P (n - m) (ENNReal.ofReal p) ≤
      LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P (n - m) (ENNReal.ofReal p) := by
    have h : ellBarN ξ W P (n - m) (ENNReal.ofReal p) / ellN ξ W P (n - m) (ENNReal.ofReal p) ≤
        LambdaN ξ W P n (ENNReal.ofReal p) :=
      Finset.le_sup' (fun j => ellBarN ξ W P j (ENNReal.ofReal p) / ellN ξ W P j (ENNReal.ofReal p))
        (Finset.mem_range.2 (by omega : n - m < n + 1))
    calc ellBarN ξ W P (n - m) (ENNReal.ofReal p)
        = ellBarN ξ W P (n - m) (ENNReal.ofReal p) / ellN ξ W P (n - m) (ENNReal.ofReal p) *
            ellN ξ W P (n - m) (ENNReal.ofReal p) := (div_mul_cancel₀ _ hℓnm.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h hℓnm.le
  set E₁ : ℝ := 2 * ξ * m * Real.log 2 + C₃ * √m with hE₁
  have hsc : ellN ξ W P (n - m) (ENNReal.ofReal p) ≤
      Real.exp E₁ * ellN ξ W P n (ENNReal.ofReal p) := by
    have h := h3 n m hmn.le
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    have h0 : Real.exp E₁ * Real.exp (Real.log 2 * -(2 * ξ * m)) * Real.exp (-(C₃ * √m)) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; convert Real.exp_zero using 2; simp only [E₁]; ring
    have e : ellN ξ W P (n - m) (ENNReal.ofReal p) = Real.exp E₁ *
        (Real.exp (Real.log 2 * -(2 * ξ * m)) * ellN ξ W P (n - m) (ENNReal.ofReal p) *
          Real.exp (-(C₃ * √m))) := by
      linear_combination (-ellN ξ W P (n - m) (ENNReal.ofReal p)) * h0
    rw [e]
    exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hk2 : (2 : ℝ)⁻¹ ^ m * (k : ℝ) ^ 2 = Real.exp (m * Real.log 2) := by
    have e2 : (2 : ℝ) ^ m = Real.exp (m * Real.log 2) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul,
        Real.exp_log (by norm_num)]
    rw [hk, ← e2, inv_pow]; field_simp
  have hthr : Real.exp (|ξ| * M) * ((2 : ℝ)⁻¹ ^ m * T) ≤
      Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) := by
    have hT : T ≤ Real.exp (ξ * C₁ * √k) * C₁ * k ^ 2 * (LambdaN ξ W P n (ENNReal.ofReal p) *
        (Real.exp E₁ * ellN ξ W P n (ENNReal.ofReal p))) :=
      mul_le_mul_of_nonneg_left (hbar.trans (mul_le_mul_of_nonneg_left hsc (by linarith)))
        (by positivity)
    have hkey : Real.exp (|ξ| * M) * ((2 : ℝ)⁻¹ ^ m * (Real.exp (ξ * C₁ * √k) * C₁ * k ^ 2 *
        (LambdaN ξ W P n (ENNReal.ofReal p) * (Real.exp E₁ * ellN ξ W P n (ENNReal.ofReal p))))) =
        Real.exp (ξ * M + m * Real.log 2 + ξ * C₁ * √k + Real.log C₁ + E₁) *
          (LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p)) := by
      simp only [Real.exp_add, Real.exp_log hC₁, abs_of_pos hξ]
      linear_combination (Real.exp (ξ * M) * Real.exp (ξ * C₁ * √k) * C₁ *
        LambdaN ξ W P n (ENNReal.ofReal p) * Real.exp E₁ * ellN ξ W P n (ENNReal.ofReal p)) * hk2
    have hexp : ξ * M + m * Real.log 2 + ξ * C₁ * √k + Real.log C₁ + E₁ ≤ s := by
      have a1 := mul_le_mul_of_nonneg_left hM hξ.le
      have a2 := mul_le_mul_of_nonneg_left hmQ hl2.le
      have a3 : ξ * C₁ * √k ≤ ξ * C₁ * Q := by
        rw [hk]; exact mul_le_mul_of_nonneg_left hs2Q (by positivity)
      have a4 : Real.log C₁ ≤ |Real.log C₁| * Q :=
        (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) h1Q)
      have a5 := mul_le_mul_of_nonneg_left hmQ (by positivity : (0 : ℝ) ≤ 2 * ξ * Real.log 2)
      have a6 := mul_le_mul_of_nonneg_left hsmQ hC₃.le
      simp only [E₁]
      linarith
    calc Real.exp (|ξ| * M) * ((2 : ℝ)⁻¹ ^ m * T)
        ≤ Real.exp (|ξ| * M) * ((2 : ℝ)⁻¹ ^ m * (Real.exp (ξ * C₁ * √k) * C₁ * k ^ 2 *
          (LambdaN ξ W P n (ENNReal.ofReal p) * (Real.exp E₁ * ellN ξ W P n (ENNReal.ofReal p))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT (by positivity)) (by positivity)
      _ = _ := hkey
      _ ≤ Real.exp s * (LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p)) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hexp) (by positivity)
      _ = _ := by ring
  -- assemble
  have hP2 : P {ω | M < ⨆ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω|} ≤
      ENNReal.ofReal (3 * C₂ * Real.exp (-((2 : ℝ) ^ m / Real.log 4))) := by
    have hsub : {ω | M < ⨆ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω|} ⊆
        {ω | M ≤ ⨆ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω|} := fun ω hω => by
      simp only [mem_ofPred_eq] at hω ⊢; exact le_of_lt hω
    refine (measure_mono hsub).trans ?_
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal ((h2 m α hα0).trans hT1)
  have hP1 := (h1 (n - m) k hk1).trans (le_of_eq (by rw [hk]))
  calc P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
        lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω}
      ≤ P {ω | Real.exp (|ξ| * M) * ((2 : ℝ)⁻¹ ^ m * T) ≤
          lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} :=
        measure_mono fun ω (hω : _ ≤ _) => (hthr.trans hω : _ ≤ _)
    _ ≤ _ := hsplit
    _ ≤ _ := add_le_add hP2 hP1

/-- **DDDF Proposition 18** ((4.49), upper tails for `φ`), from Steps 1 and 3:
`P(L^{(n)}_{3,1}(φ) ≥ e^s Λ_n(φ,p) ℓ_n(φ,p)) ≤ C e^{-c s²/log s}` for all `n ≥ 0`, `s > 2`
(sign of the exponent: reading D-DDDF-9). -/
theorem dddf_prop18_of_steps {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (h1 : P18Step1 ξ W P) (h3 : P18Step3 ξ W P) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (s : ℝ), 2 < s →
      P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
          lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨p₁, hp₁, h1'⟩ := h1
  obtain ⟨p₃, hp₃, h3'⟩ := h3
  refine ⟨min (min (p₁ / 2) p₃) (1 / 4), by positivity, fun p hp0 hp => ?_⟩
  have hpp₁ : 2 * p ≤ p₁ := by have := (le_min_iff.1 (le_min_iff.1 hp).1).1; linarith
  have hpp₃ : p ≤ p₃ := (le_min_iff.1 (le_min_iff.1 hp).1).2
  have hp4 : p ≤ 1 / 4 := (le_min_iff.1 hp).2
  obtain ⟨C₁, c₁, hC₁, hc₁, hS1⟩ := h1' (2 * p) (by positivity) hpp₁
  have e2p : 2 * p / 2 = p := by ring
  rw [e2p] at hS1
  obtain ⟨C₃, hC₃, hS3⟩ := h3' p hp0 hpp₃
  obtain ⟨C₂, hC₂, hS2⟩ := prop2_tail_R31 (Ω := Ω) (P := P)
  obtain ⟨Cℓ, -, hell⟩ := dddf_p18_ell_lower hW hξ hp0 (by linarith : p < 1)
  have hℓ : ∀ n : ℕ, 1 ≤ n → 0 < ellN ξ W P n (ENNReal.ofReal p) :=
    fun n hn => lt_of_lt_of_le (Real.exp_pos _) (hell n hn)
  obtain ⟨C₄, c₄, hC₄, hc₄, hS4⟩ := dddf_p18_step4 hW hξ hp0 (by linarith : p ≤ 1 / 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ξ * (1 + C₂) * (Real.log 4 + 1) + Real.log 2 + ξ * C₁ +
    |Real.log C₁| + 2 * ξ * Real.log 2 + C₃ := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (2 * D ^ 2 + 1) / Real.log 2 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  have hBl2 : B * Real.log 2 = 2 * D ^ 2 + 1 := by rw [hB]; field_simp
  obtain ⟨c', hc'def⟩ : ∃ c' : ℝ, c' = min (1 / Real.log 4) c₁ := ⟨_, rfl⟩
  have hc' : 0 < c' := by rw [hc'def]; exact lt_min (by positivity) hc₁
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min c₄ (c' / (2 * B)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact lt_min hc₄ (by positivity)
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, s₀ = 2 * B := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = C₄ + (3 * C₂ + C₁) + Real.exp (c * s₀ ^ 2 / Real.log 2) :=
    ⟨_, rfl⟩
  have hCe := Real.exp_pos (c * s₀ ^ 2 / Real.log 2)
  have hC0 : 0 < C := by rw [hCdef]; positivity
  refine ⟨C, c, hC0, hc, fun n s hs => ?_⟩
  have hs0 : 0 < s := by linarith
  have hls : Real.log 2 < Real.log s := Real.log_lt_log (by norm_num) hs
  have hls0 : 0 < Real.log s := hl2.trans hls
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = s ^ 2 / Real.log s := ⟨_, rfl⟩
  have hX : 0 < X := by rw [hXdef]; positivity
  have hform : ∀ c₀ : ℝ, -c₀ * s ^ 2 / Real.log s = -(c₀ * X) := fun c₀ => by
    rw [hXdef]; ring
  rw [hform c]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dddf_p18_zero hW hp0 (by linarith) hs]; exact bot_le
  by_cases hns : (2 : ℝ) ^ n ≤ s ^ 2
  · refine (hS4 n s hn hs hns).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hform c₄]
    refine mul_le_mul (by rw [hCdef]; linarith) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      hC0.le
    have := mul_le_mul_of_nonneg_right (min_le_left c₄ (c' / (2 * B))) hX.le
    rw [← hcdef] at this
    linarith
  push Not at hns
  by_cases hss : s < s₀
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : c * X ≤ c * s₀ ^ 2 / Real.log 2 := by
      have hsq : s ^ 2 ≤ s₀ ^ 2 := pow_le_pow_left₀ hs0.le hss.le 2
      rw [hXdef, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      calc s ^ 2 / Real.log s ≤ s₀ ^ 2 / Real.log s := div_le_div_of_nonneg_right hsq hls0.le
        _ ≤ s₀ ^ 2 / Real.log 2 := div_le_div_of_nonneg_left (by positivity) hl2 hls.le
    calc (1 : ℝ) ≤ Real.exp (c * s₀ ^ 2 / Real.log 2 + -(c * X)) := Real.one_le_exp (by linarith)
      _ = Real.exp (c * s₀ ^ 2 / Real.log 2) * Real.exp (-(c * X)) := Real.exp_add _ _
      _ ≤ C * Real.exp (-(c * X)) :=
          mul_le_mul_of_nonneg_right (by rw [hCdef]; linarith) (Real.exp_pos _).le
  push Not at hss
  -- the scale `m`: `2^m ≤ s²/(B log s) < 2^{m+1}`
  have hBl : 1 ≤ B * Real.log s := by
    have h := mul_le_mul_of_nonneg_left hls.le hB0.le
    rw [hBl2] at h
    linarith [sq_nonneg D]
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = s ^ 2 / (B * Real.log s) := ⟨_, rfl⟩
  have hlogs : Real.log s ≤ s := (Real.log_le_sub_one_of_pos hs0).trans (by linarith)
  have hy2 : 2 ≤ y := by
    rw [hydef, le_div_iff₀ (mul_pos hB0 hls0)]
    have h1 := mul_le_mul_of_nonneg_left hlogs hB0.le
    have h2 := mul_le_mul_of_nonneg_right hss hs0.le
    rw [hs₀] at h2
    linarith
  have hys : y ≤ s ^ 2 := by rw [hydef]; exact div_le_self (by positivity) hBl
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ y)
    (by norm_num : (1 : ℝ) < 2)
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp only [zero_add, pow_one] at hm2; linarith
    · exact h
  have hmn : m < n := by
    have : (2 : ℝ) ^ m < 2 ^ n := by linarith
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
  have hml : (m : ℝ) * Real.log 2 ≤ 2 * Real.log s := by
    have := Real.log_le_log (by positivity) (hm1.trans hys)
    rwa [Real.log_pow, Real.log_pow] at this
  have hDQ : D * √((2 : ℝ) ^ m * m) ≤ s := by
    have hsq : (D * √((2 : ℝ) ^ m * m)) ^ 2 ≤ s ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hm' : (m : ℝ) ≤ 2 * Real.log s / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
      have hne1 := hls0.ne'
      have hne2 := hl2.ne'
      have hne3 := hB0.ne'
      calc D ^ 2 * (2 ^ m * m) ≤ D ^ 2 * (y * (2 * Real.log s / Real.log 2)) := by
            gcongr
        _ = s ^ 2 * (2 * D ^ 2 / (B * Real.log 2)) := by rw [hydef]; field_simp
        _ ≤ s ^ 2 * 1 := by
            gcongr
            rw [div_le_one (mul_pos hB0 hl2), hBl2]; linarith
        _ = s ^ 2 := mul_one _
    exact (pow_le_pow_iff_left₀ (mul_nonneg hD0 (Real.sqrt_nonneg _)) hs0.le two_ne_zero).1 hsq
  rw [hD] at hDQ
  have hmid := p18_mid hW hξ hp0 (by linarith) hC₁ hC₂ hC₃ hS1 (fun m α hα => hS2 hW m α hα)
    hS3 hℓ hm hmn hDQ
  refine hmid.trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hym : y / 2 < 2 ^ m := by rw [pow_succ] at hm2; linarith
  have hcX : c * X ≤ c' * 2 ^ m := by
    have h1 : c * X ≤ c' / (2 * B) * X := by
      rw [hcdef]; exact mul_le_mul_of_nonneg_right (min_le_right _ _) hX.le
    have e : c' / (2 * B) * X = c' * (y / 2) := by
      rw [hXdef, hydef]; field_simp
    have h2 := mul_le_mul_of_nonneg_left hym.le hc'.le
    linarith
  have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
  have ha : Real.exp (-((2 : ℝ) ^ m / Real.log 4)) ≤ Real.exp (-(c * X)) := by
    refine Real.exp_le_exp.2 ?_
    have h := mul_le_mul_of_nonneg_right (min_le_left (1 / Real.log 4) c₁) h2m
    rw [← hc'def] at h
    have e : (2 : ℝ) ^ m / Real.log 4 = 1 / Real.log 4 * 2 ^ m := by ring
    rw [e]; linarith
  have hb : Real.exp (-(c₁ * (2 : ℝ) ^ m)) ≤ Real.exp (-(c * X)) := by
    refine Real.exp_le_exp.2 ?_
    have h := mul_le_mul_of_nonneg_right (min_le_right (1 / Real.log 4) c₁) h2m
    rw [← hc'def] at h
    linarith
  calc 3 * C₂ * Real.exp (-((2 : ℝ) ^ m / Real.log 4)) + C₁ * Real.exp (-(c₁ * (2 : ℝ) ^ m))
      ≤ 3 * C₂ * Real.exp (-(c * X)) + C₁ * Real.exp (-(c * X)) := by gcongr
    _ = (3 * C₂ + C₁) * Real.exp (-(c * X)) := by ring
    _ ≤ C * Real.exp (-(c * X)) :=
        mul_le_mul_of_nonneg_right (by rw [hCdef]; linarith) (Real.exp_pos _).le

end DDDF
end LQGMetric
