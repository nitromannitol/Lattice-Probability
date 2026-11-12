/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28L1D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28L1C

/-!
# DDDF Prop 28 Part 2 Step 1 for the family: the probability at one scale (task P2-DDDF28L)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1462–1472. For `δ = 2^{-(n+r)}`, `1 ≤ K < n`,
`h = 2^{-K}`: `level_prob` bounds `P(E_K)` by `e^{-2u} + 16·4^K C₁ e^{-c₁ s²}`, from
`level_bound`, the sup tail (2.11) of `φ_{h,1} = φ_{0,K}` (`phiVer_sup_tail_unif`), the left
tail (6.103) of `L(φ_{δ/h,1}, R_{1,3})` and weak multiplicativity (DDDF `eq:BoundHolderLow`):
`λ_δ ≤ e^{C₀} λ_n ≤ e^{C₀} e^{C√K} λ_{n−K} λ_K ≤ e^{2C₀} e^{C√K} λ_{δ/h} λ_K` ((6.98), (5.76))
and `λ_K ≤ C' 2^{-K(1−ξQ−ζ)}` ((5.78)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28L

open WhiteNoise SupTail Blueprint LFPP S6P28

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

lemma inv_two_pow_eq_exp (K : ℕ) : (2 : ℝ)⁻¹ ^ K = Real.exp (-(K * Real.log 2)) := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, inv_pow]

lemma two_rpow_div {n K : ℕ} (hKn : K ≤ n) (r : ℝ) :
    (2 : ℝ) ^ (-((n : ℝ) + r)) / (2 : ℝ)⁻¹ ^ K = (2 : ℝ) ^ (-(((n - K : ℕ) : ℝ) + r)) := by
  rw [Nat.cast_sub hKn, inv_pow, div_eq_mul_inv, inv_inv, ← Real.rpow_natCast,
    ← Real.rpow_add (by norm_num)]
  congr 1; ring

lemma two_rpow_le {n K : ℕ} (hKn : K ≤ n) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (2 : ℝ) ^ (-((n : ℝ) + r)) ≤ (2 : ℝ)⁻¹ ^ K := by
  refine (split_bounds n hr0 hr1).2.trans ?_
  rw [← inv_pow]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn

/-- **The probability of `E_K`** (DDDF l. 1462–1472). -/
theorem level_prob (hW : IsWhiteNoise P W) (hξ : 0 < ξ) {q C0 Cm ζ C' c₁ C₁ : ℝ}
    (hC0 : ∀ (n : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 →
      Real.exp (-C0) * lambdaN ξ W P n ≤ lambdaDelta ξ W P ((2 : ℝ) ^ (-((n : ℝ) + r))) ∧
        lambdaDelta ξ W P ((2 : ℝ) ^ (-((n : ℝ) + r))) ≤ Real.exp C0 * lambdaN ξ W P n)
    (hCm : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      lambdaN ξ W P (n + k) ≤ Real.exp (Cm * √(k : ℝ)) * lambdaN ξ W P n * lambdaN ξ W P k)
    (hC' : 0 < C')
    (hlam : ∀ K : ℕ, lambdaN ξ W P K ≤ C' * Real.exp (-(Real.log 2) * (1 - ξ * q - ζ) * K))
    (htail : ∀ s : ℝ, 2 < s → ∀ δ : ℝ, 0 < δ → δ < 1 →
      P {ω | lenObs ξ (phiVer W P δ 1) (rectAB 1 3) ω ≤ Real.exp (-s) * lambdaDelta ξ W P δ} ≤
        ENNReal.ofReal (C₁ * Real.exp (-c₁ * s ^ 2)))
    {n : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {K : ℕ} (hK1 : 1 ≤ K) (hKn : K < n)
    {α D u : ℝ} (hα : 0 ≤ α) (hu : 0 ≤ u)
    (hs : 2 < D - ξ * (ferniqueCF * Real.sqrt 6 + (2 * (K + 1) * Real.log 2 + u)) -
      Cm * √(K : ℝ) + K * Real.log 2 * (α - ξ * q - ζ)) :
    P {ω | ∃ x y : closedUnitSquare, 4 * (2 : ℝ)⁻¹ ^ K ≤ ‖(x : ℂ) - y‖ ∧
        ‖(x : ℂ) - y‖ ≤ 8 * (2 : ℝ)⁻¹ ^ K ∧
        (lambdaDelta ξ W P ((2 : ℝ) ^ (-((n : ℝ) + r))))⁻¹ * lenMetricOn ξ
          (fun z => phiVer W P ((2 : ℝ) ^ (-((n : ℝ) + r))) 1 z ω) closedUnitSquare x y <
        Real.exp (-D - α * Real.log 8 - Real.log C' - 2 * C0) * ‖(x : ℂ) - y‖ ^ α}
      ≤ ENNReal.ofReal (Real.exp (-(2 * u))) + ENNReal.ofReal (4 * (4 * 4 ^ K)) *
        ENNReal.ofReal (C₁ * Real.exp (-c₁ * (D - ξ * (ferniqueCF * Real.sqrt 6 +
          (2 * (K + 1) * Real.log 2 + u)) - Cm * √(K : ℝ) +
            K * Real.log 2 * (α - ξ * q - ζ)) ^ 2)) := by
  have hP := hW.isProbabilityMeasure
  set L := Real.log 2 with hL_def
  set δ : ℝ := (2 : ℝ) ^ (-((n : ℝ) + r)) with hδ_def
  set h : ℝ := (2 : ℝ)⁻¹ ^ K with hh_def
  set M := ferniqueCF * Real.sqrt 6 + (2 * (K + 1) * L + u) with hM_def
  set s := D - ξ * M - Cm * √(K : ℝ) + K * L * (α - ξ * q - ζ) with hs_def
  set c := Real.exp (-D - α * Real.log 8 - Real.log C' - 2 * C0) with hc_def
  have hh : 0 < h := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδh : δ ≤ h := two_rpow_le hKn.le hr0 hr1
  set δ' := δ / h with hδ'_def
  have hδ'e : δ' = (2 : ℝ) ^ (-(((n - K : ℕ) : ℝ) + r)) := two_rpow_div hKn.le r
  have hnK : 1 ≤ n - K := by omega
  have hδ'0 : 0 < δ' := by positivity
  have hδ'1 : δ' < 1 := by
    rw [hδ'e]
    refine (two_rpow_le (K := 1) hnK hr0 hr1).trans_lt (by norm_num)
  have hlamδ : 0 < lambdaDelta ξ W P δ :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) (lambdaN_pos hW n)) (hC0 n r hr0 hr1).1
  set t := Real.exp (ξ * M) * lambdaDelta ξ W P δ * (c * (8 * h) ^ α) with ht_def
  have hct : c * (8 * h) ^ α ≤ (lambdaDelta ξ W P δ)⁻¹ * (Real.exp (-(ξ * M)) * t) := by
    rw [ht_def, Real.exp_neg]
    have := Real.exp_pos (ξ * M)
    apply le_of_eq; field_simp
  have hlb := level_bound hW hξ hδ0 K hδh hα (by positivity) hlamδ hct
  refine hlb.trans (add_le_add ?_ (mul_le_mul' le_rfl ?_))
  · -- the sup tail (2.11) of `φ_{h,1}`
    have hK0 : K ≠ 0 := by omega
    have e : h = ((2 : ℝ) ^ K)⁻¹ := by rw [hh_def, inv_pow]
    have h1 : ((2 : ℝ) ^ K)⁻¹ ≤ 2 * h := by rw [← e]; linarith
    have h3 : h < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hK0
    have := phiVer_sup_tail_unif hW K h1 e.le h3 hu
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal this
  · -- the left tail (6.103) of `L(φ_{δ',1}, R_{1,3})`
    refine le_trans (measure_mono ?_) (htail s hs δ' hδ'0 hδ'1)
    -- weak multiplicativity: `t ≤ h e^{-s} λ_{δ'}`
    have l1 := (hC0 n r hr0 hr1).2
    have l2 := hCm (n - K) K hnK hK1
    rw [Nat.sub_add_cancel hKn.le] at l2
    have l3 : lambdaN ξ W P (n - K) ≤ Real.exp C0 * lambdaDelta ξ W P δ' := by
      have := (hC0 (n - K) r hr0 hr1).1
      rw [← hδ'e] at this
      have e2 : Real.exp C0 * (Real.exp (-C0) * lambdaN ξ W P (n - K)) =
          lambdaN ξ W P (n - K) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      calc lambdaN ξ W P (n - K) = _ := e2.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    have l4 := hlam K
    have hK0' := lambdaN_pos (ξ := ξ) hW K
    have hnK0 := lambdaN_pos (ξ := ξ) hW (n - K)
    have hb : lambdaDelta ξ W P δ ≤ Real.exp C0 * (Real.exp (Cm * √(K : ℝ)) *
        (Real.exp C0 * lambdaDelta ξ W P δ') *
          (C' * Real.exp (-L * (1 - ξ * q - ζ) * K))) := by
      refine l1.trans (mul_le_mul_of_nonneg_left (l2.trans ?_) (Real.exp_pos _).le)
      rw [mul_assoc, mul_assoc]
      have hδ'pos : 0 ≤ Real.exp C0 * lambdaDelta ξ W P δ' := hnK0.le.trans l3
      gcongr
    have e8 : (8 * h) ^ α = Real.exp (α * (Real.log 8 - K * L)) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_mul (by norm_num) hh.ne',
        hh_def, inv_two_pow_eq_exp, Real.log_exp, hL_def]; ring_nf
    have hid : Real.exp (ξ * M) * (Real.exp C0 * (Real.exp (Cm * √(K : ℝ)) * Real.exp C0 *
        (C' * Real.exp (-L * (1 - ξ * q - ζ) * K)))) * (c * (8 * h) ^ α) =
        h * Real.exp (-s) := by
      rw [e8, hc_def, hh_def, inv_two_pow_eq_exp, ← Real.exp_log hC']
      simp only [← Real.exp_add, Real.log_exp]
      congr 1
      rw [hs_def, hL_def]; ring
    have hkey : t ≤ h * (Real.exp (-s) * lambdaDelta ξ W P δ') := by
      calc t ≤ Real.exp (ξ * M) * (Real.exp C0 * (Real.exp (Cm * √(K : ℝ)) *
            (Real.exp C0 * lambdaDelta ξ W P δ') *
              (C' * Real.exp (-L * (1 - ξ * q - ζ) * K)))) * (c * (8 * h) ^ α) := by
            rw [ht_def]; gcongr
        _ = (Real.exp (ξ * M) * (Real.exp C0 * (Real.exp (Cm * √(K : ℝ)) * Real.exp C0 *
            (C' * Real.exp (-L * (1 - ξ * q - ζ) * K)))) * (c * (8 * h) ^ α)) *
              lambdaDelta ξ W P δ' := by ring
        _ = h * (Real.exp (-s) * lambdaDelta ξ W P δ') := by rw [hid]; ring
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    exact le_of_mul_le_mul_left (hω.trans hkey) hh

end S6P28L
end DDDF
end LQGMetric
