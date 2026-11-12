/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P26Low at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Sup

/-!
# DDDF Prop 26 (5.76), lower half, for all `n, k ≥ 1` (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1311–1329. `s6_eq5_76_low_large` gives `λ_{n+k} ≥ e^{-C√k} λ_n λ_k` for `k ≥ k₁`; for the
finitely many `1 ≤ k < k₁` we use (6.98) with `r = 1` (`λ_{m+1} ≥ e^{-C} λ_m`, DDDF l. 1608–1612),
iterated `k` times (DDDF does not treat small `k` separately; own bookkeeping).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Real

namespace LQGMetric
namespace DDDF

open WhiteNoise S6

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- the lower half of **DDDF (5.76)** -/
def S6Eq5_76Low (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ C : ℝ, ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    Real.exp (-(C * √(k : ℝ))) * lambdaN ξ W P n * lambdaN ξ W P k ≤ lambdaN ξ W P (n + k)

/-- the upper half of **DDDF (5.76)** (DDDF Prop 26, Step 1, l. 1283–1309). Open. -/
def S6Eq5_76Up (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ C : ℝ, ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    lambdaN ξ W P (n + k) ≤ Real.exp (C * √(k : ℝ)) * lambdaN ξ W P n * lambdaN ξ W P k

theorem s6Eq5_76_of_halves (hW : IsWhiteNoise P W) (hL : S6Eq5_76Low ξ W P)
    (hU : S6Eq5_76Up ξ W P) : S6Eq5_76 ξ W P := by
  obtain ⟨C₁, h₁⟩ := hL
  obtain ⟨C₂, h₂⟩ := hU
  refine ⟨max C₁ C₂, fun n k hn hk => ⟨(le_trans ?_ (h₁ n k hn hk)), (h₂ n k hn hk).trans ?_⟩⟩
  · have e : Real.exp (-(max C₁ C₂ * √(k : ℝ))) ≤ Real.exp (-(C₁ * √(k : ℝ))) :=
      Real.exp_le_exp.2 (neg_le_neg
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e (lambdaN_pos hW n).le)
      (lambdaN_pos hW k).le
  · have e : Real.exp (C₂ * √(k : ℝ)) ≤ Real.exp (max C₁ C₂ * √(k : ℝ)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e (lambdaN_pos hW n).le)
      (lambdaN_pos hW k).le

/-- (6.98) with `r = 1`, iterated: `λ_{n+k} ≥ e^{-Ck} λ_n` -/
theorem lambdaN_add_ge (hW : IsWhiteNoise P W) (h98 : S6Eq6_98 ξ W P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n k : ℕ, Real.exp (-(C * k)) * lambdaN ξ W P n ≤ lambdaN ξ W P (n + k) := by
  obtain ⟨C, hC⟩ := h98
  refine ⟨|C|, abs_nonneg C, fun n k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := (hC (n + k) 1 zero_le_one le_rfl).1
    have e : lambdaDelta ξ W P ((2 : ℝ) ^ (-(((n + k : ℕ) : ℝ) + 1))) = lambdaN ξ W P (n + (k + 1)) := by
      rw [← lamT_nat (ξ := ξ) (W := W) (P := P) (n + (k + 1))]
      simp only [lamT]; push_cast; ring_nf
    rw [e] at h1
    have hl := lambdaN_pos (ξ := ξ) hW n
    have hl' := lambdaN_pos (ξ := ξ) hW (n + k)
    calc Real.exp (-(|C| * ((k + 1 : ℕ) : ℝ))) * lambdaN ξ W P n
        = Real.exp (-|C|) * (Real.exp (-(|C| * k)) * lambdaN ξ W P n) := by
          push_cast; rw [← mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-C) * lambdaN ξ W P (n + k) := by
          gcongr
          exact le_abs_self C
      _ ≤ lambdaN ξ W P (n + (k + 1)) := h1

/-- **DDDF (5.76), lower half** (Prop 26, Step 2) from the pathwise (5.75), (6.98) and
`Λ_∞ < ∞`. -/
theorem s6_eq5_76_low (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B)
    (h75 : S6Eq5_75 ξ W P) : S6Eq5_76Low ξ W P := by
  obtain ⟨C₁, k₁, hbig⟩ := s6_eq5_76_low_large hW hξ hΛ h75
  obtain ⟨C₉, hC₉, hsmall⟩ := lambdaN_add_ge hW (s6_eq6_98_of_Lambda hW hξ hΛ)
  set S : ℝ := ∑ j ∈ Finset.range k₁, lambdaN ξ W P j
  have hpos : ∀ j, 0 < lambdaN ξ W P j := fun j => lambdaN_pos hW j
  set C₂ : ℝ := C₉ * k₁ + |Real.log (S + 1)|
  refine ⟨max C₁ C₂, fun n k hn hk => ?_⟩
  have hsk : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hk)
  rcases le_or_gt k₁ k with hkk | hkk
  · refine le_trans ?_ (hbig k hkk n hn)
    have e : Real.exp (-(max C₁ C₂ * √(k : ℝ))) ≤ Real.exp (-(C₁ * √(k : ℝ))) :=
      Real.exp_le_exp.2 (neg_le_neg
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e (hpos n).le) (hpos k).le
  · -- `k < k₁`: `λ_k ≤ S + 1` and `λ_{n+k} ≥ e^{-C₉ k₁} λ_n`
    have hS : lambdaN ξ W P k ≤ S + 1 := by
      have := Finset.single_le_sum (f := fun j => lambdaN ξ W P j) (fun j _ => (hpos j).le)
        (Finset.mem_range.2 hkk)
      linarith
    have hS0 : 0 < S + 1 := (hpos k).trans_le hS
    have hC₂0 : 0 ≤ C₂ := add_nonneg (mul_nonneg hC₉ (Nat.cast_nonneg _)) (abs_nonneg _)
    clear_value S
    have h1 := hsmall n k
    have hk1 : (k : ℝ) ≤ k₁ := by exact_mod_cast hkk.le
    have e1 : Real.exp (-(C₉ * k₁)) ≤ Real.exp (-(C₉ * k)) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hk1 hC₉))
    have e2 : Real.exp (-(max C₁ C₂ * √(k : ℝ))) ≤ Real.exp (-(C₉ * k₁)) * (S + 1)⁻¹ := by
      rw [← Real.exp_log (inv_pos.2 hS0), ← Real.exp_add, Real.log_inv]
      refine Real.exp_le_exp.2 ?_
      have h3 : C₂ ≤ max C₁ C₂ * √(k : ℝ) :=
        (le_max_right C₁ C₂).trans (le_mul_of_one_le_right
          ((le_max_right _ _).trans' hC₂0) hsk)
      have h4 : Real.log (S + 1) ≤ |Real.log (S + 1)| := le_abs_self _
      simp only [C₂] at h3
      linarith
    have hl := hpos n
    have hlk := hpos k
    calc Real.exp (-(max C₁ C₂ * √(k : ℝ))) * lambdaN ξ W P n * lambdaN ξ W P k
        ≤ Real.exp (-(C₉ * k₁)) * (S + 1)⁻¹ * lambdaN ξ W P n * (S + 1) :=
          mul_le_mul (mul_le_mul_of_nonneg_right e2 hl.le) hS hlk.le
            (mul_nonneg (mul_nonneg (Real.exp_pos _).le (inv_pos.2 hS0).le) hl.le)
      _ = Real.exp (-(C₉ * k₁)) * lambdaN ξ W P n * ((S + 1)⁻¹ * (S + 1)) := by ring
      _ = Real.exp (-(C₉ * k₁)) * lambdaN ξ W P n := by
          rw [inv_mul_cancel₀ hS0.ne', mul_one]
      _ ≤ Real.exp (-(C₉ * k)) * lambdaN ξ W P n := mul_le_mul_of_nonneg_right e1 hl.le
      _ ≤ lambdaN ξ W P (n + k) := h1

end DDDF
end LQGMetric
