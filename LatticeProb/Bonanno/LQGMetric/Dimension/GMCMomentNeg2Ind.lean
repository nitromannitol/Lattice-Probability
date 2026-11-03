/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentNeg2Ind at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg2Base

/-!
# Polynomial decay of the Laplace transform of discrete GMC sums (P2-NEGMOM)

`DGMC.LogCorr.exists_lapGM_le_rpow` : for a `β`-log-correlated family with `0 < β < 4` there are
`δ ∈ (0,1]` and `T ≥ 1` with `E e^{-t gM_n([0,1]²)} ≤ (T/t)^δ` for all `t ≥ T`, uniformly in
the grid level `j ≥ n`.

Induction on `n` with the recursion `LogCorr.lapGM_rec` (one checkerboard group of `N` level-`m`
squares, decoupled by Kahane), started by the Paley–Zygmund bound
`LogCorr.exists_lapGM_le_one_sub` (`E e^{-t gM} ≤ 1 − ε`, `t ≥ 2`) on the window `[T, T']`,
and by the fixed-scale bound `LogCorr.lapGM_le_div` for `n < m`.  This is Molchan's argument for
cascades (CMP 179 (1996)) in the form adapted by Robert–Vargas (arXiv:0807.1030, proof of
Prop. 3.6, `main.tex` l. 1031–1037); it yields BP's (`laplace_useful`) (arXiv:2404.16642,
`GMCproperties.tex` l. 1699–1703) for the discrete approximations.  The bookkeeping of the
constants is our own (decision D63).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → ℂ → Ω → ℝ} {β c : ℝ}

/-- `(A √x)^δ = A^δ √(x^δ)` -/
lemma rpow_mul_sqrt {A x δ : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x) :
    (A * Real.sqrt x) ^ δ = A ^ δ * Real.sqrt (x ^ δ) := by
  rw [Real.mul_rpow hA (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hx, ← Real.rpow_mul hx, mul_comm (1 / 2 : ℝ) δ]

/-- **polynomial decay of the Laplace transform**, uniformly in `n ≤ j` -/
theorem LogCorr.exists_lapGM_le_rpow (hZ : LogCorr Z P β c) (hβ : 0 < β) (hβ4 : β < 4) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ T : ℝ, 1 ≤ T ∧
      ∀ n j : ℕ, n ≤ j → ∀ t : ℝ, T ≤ t → lapGM Z P n j t ≤ (T / t) ^ δ := by
  have hc := hZ.c_nonneg
  obtain ⟨ε, hε0, hε1, hPZ⟩ := hZ.exists_lapGM_le_one_sub hβ hβ4
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 4)
    (by linarith : 1 - ε < 1)
  set m := 2 * k₀ + 3
  set N := (grp0 m).card
  have hN : 2 * k₀ + 2 ≤ N := (le_card_grp0 m).trans' (by omega)
  set V := β * (m * Real.log 2) + 2 * c
  set K := Real.exp (3 * V)
  set B := Real.exp (β * (m * Real.log 2) + c)
  set T := max (max 2 B) (2 * K)
  have hT2 : 2 ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hTB : B ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hTK : 2 * K ≤ T := le_max_right _ _
  have hT0 : 0 < T := by linarith
  set A := (4 : ℝ) ^ m * Real.sqrt T
  have hA1 : 1 ≤ A := by
    have h1 : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
    have h2 : 1 ≤ Real.sqrt T := Real.one_le_sqrt.2 (by linarith)
    nlinarith
  have hA0 : 0 < A := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨D₁, hD₁⟩ := exists_nat_ge (N * Real.log A / Real.log 2)
  have h16 : 0 < (16 : ℝ) ^ m * T := by positivity
  obtain ⟨D₂, hD₂⟩ := exists_pow_lt_of_lt_one (inv_pos.2 h16) (by linarith : 1 - ε < 1)
  set D := max (max 1 D₁) D₂
  have hD1 : 1 ≤ D := (le_max_left _ _).trans (le_max_left _ _)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hDA : (N : ℝ) * Real.log A ≤ D * Real.log 2 := by
    have : (D₁ : ℝ) ≤ D := by exact_mod_cast (le_max_right _ _).trans (le_max_left _ _)
    have := (div_le_iff₀ hlog2).1 (hD₁.trans this)
    linarith
  have hDε : (1 - ε) ^ D ≤ ((16 : ℝ) ^ m * T)⁻¹ :=
    (pow_le_pow_of_le_one (by linarith) (by linarith) (le_max_right _ _)).trans hD₂.le
  set δ : ℝ := (D : ℝ)⁻¹
  have hδ0 : 0 < δ := inv_pos.2 hD0
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hD1)
  have hAδ : (A ^ δ) ^ N ≤ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA0.le, Real.rpow_def_of_pos hA0]
    calc Real.exp (Real.log A * (δ * N)) ≤ Real.exp (Real.log 2) := by
          refine Real.exp_le_exp.2 ?_
          have : Real.log A * (δ * N) = (N * Real.log A) / D := by
            simp only [δ]; field_simp
          rw [this, div_le_iff₀ hD0]
          linarith
      _ = 2 := Real.exp_log (by norm_num)
  have hεD : 0 < (1 - ε) ^ D := pow_pos (by linarith) _
  set T' := T / (1 - ε) ^ D
  have hT' : (16 : ℝ) ^ m * T ^ 2 ≤ T' := by
    rw [le_div_iff₀ hεD]
    have := mul_le_mul_of_nonneg_left hDε (by positivity : 0 ≤ (16 : ℝ) ^ m * T ^ 2)
    calc (16 : ℝ) ^ m * T ^ 2 * (1 - ε) ^ D ≤ (16 : ℝ) ^ m * T ^ 2 * ((16 : ℝ) ^ m * T)⁻¹ := this
      _ = T := by field_simp
  have hwin : (T / T') ^ δ = 1 - ε := by
    rw [show T / T' = (1 - ε) ^ D by simp only [T']; field_simp]
    exact Real.pow_rpow_inv_natCast (by linarith) (by omega)
  refine ⟨δ, hδ0, hδ1, T, by linarith, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hnj t ht
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < T / t := div_pos hT0 ht0
  have hx1 : T / t ≤ 1 := (div_le_one ht0).2 ht
  have hxδ : T / t ≤ (T / t) ^ δ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hδ1
  by_cases hnm : n < m
  · refine (hZ.lapGM_le_div n j ht0).trans (le_trans ?_ hxδ)
    refine div_le_div_of_nonneg_right ((Real.exp_le_exp.2 ?_).trans hTB) ht0.le
    have : (n : ℝ) ≤ m := by exact_mod_cast hnm.le
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hlog2.le) hβ.le
    linarith
  · push Not at hnm
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hnm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (hnm.trans hnj)
    have hlk : l ≤ k := by omega
    by_cases htT : t ≤ T'
    · refine (hPZ _ _ hnj t (hT2.trans ht)).trans ?_
      rw [← hwin]
      exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left hT0.le ht0 htT) hδ0.le
    · push Not at htT
      set s := Real.sqrt t * (4 : ℝ)⁻¹ ^ m
      have hsq : (4 : ℝ) ^ m * T ≤ Real.sqrt t := by
        rw [Real.le_sqrt (by positivity) ht0.le]
        calc ((4 : ℝ) ^ m * T) ^ 2 = (16 : ℝ) ^ m * T ^ 2 := by
              rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul]; norm_num
          _ ≤ t := hT'.trans htT.le
      have h4m : (0 : ℝ) < 4 ^ m := by positivity
      have hs : T ≤ s := by
        simp only [s, inv_pow]
        rw [le_mul_inv_iff₀ h4m]
        linarith [mul_comm T ((4 : ℝ) ^ m)]
      have hrec : lapGM Z P (m + l) (m + k) t ≤ K / t + lapGM Z P l k s ^ N :=
        hZ.lapGM_rec hβ.le ht0 m l k
      have hih := ih l (by omega) k hlk s hs
      set y := (T / t) ^ δ
      have hy0 : 0 ≤ y := by positivity
      have hyε : y ≤ 1 - ε := by
        rw [← hwin]
        exact Real.rpow_le_rpow (by positivity)
          (div_le_div_of_nonneg_left hT0.le (lt_of_lt_of_le (by positivity) hT') htT.le) hδ0.le
      have hTs : T / s = A * Real.sqrt (T / t) := by
        have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
        have hsT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
        simp only [s, A, Real.sqrt_div' T ht0.le, inv_pow]
        field_simp
        rw [Real.sq_sqrt hT0.le]
      have hTsδ : (T / s) ^ δ = A ^ δ * Real.sqrt y := by
        rw [hTs, rpow_mul_sqrt hA0.le hx0.le]
      have hsy0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
      have hsy1 : Real.sqrt y ≤ 1 := Real.sqrt_le_one.2 (by linarith)
      have hpowN : (Real.sqrt y) ^ N ≤ y * (1 / 4) := by
        have e : (Real.sqrt y) ^ N = y * (Real.sqrt y) ^ (N - 2) := by
          have : N = 2 + (N - 2) := by omega
          conv_lhs => rw [this, pow_add, Real.sq_sqrt hy0]
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ hy0
        calc (Real.sqrt y) ^ (N - 2) ≤ (Real.sqrt y) ^ (2 * k₀) :=
              pow_le_pow_of_le_one hsy0 hsy1 (by omega)
          _ = y ^ k₀ := by rw [pow_mul, Real.sq_sqrt hy0]
          _ ≤ (1 - ε) ^ k₀ := pow_le_pow_left₀ hy0 hyε _
          _ ≤ 1 / 4 := hk₀.le
      have hsecond : lapGM Z P l k s ^ N ≤ y / 2 := by
        calc lapGM Z P l k s ^ N ≤ ((T / s) ^ δ) ^ N := pow_le_pow_left₀ (lapGM_nonneg _ _ _) hih _
          _ = (A ^ δ) ^ N * (Real.sqrt y) ^ N := by rw [hTsδ, mul_pow]
          _ ≤ 2 * (y * (1 / 4)) := mul_le_mul hAδ hpowN (by positivity) (by norm_num)
          _ = y / 2 := by ring
      have hfirst : K / t ≤ y / 2 := by
        have : K / t ≤ (T / t) / 2 := by
          rw [div_div, div_le_div_iff₀ ht0 (by positivity)]
          nlinarith
        linarith
      linarith

end DGMC

end LQGMetric
