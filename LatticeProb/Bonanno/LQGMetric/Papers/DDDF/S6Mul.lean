/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Mul at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Real
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BTight
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L25
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputs

/-!
# DDDF (5.77), (6.99) and (1.3) from (5.76), (6.98) and the DG bounds (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`.

* `lambdaN_pos` — `λ_n > 0` (implicit in DDDF; from `T20B.ellN_pos`).
* `s6_eq5_77` — **DDDF (5.77)** (Prop 26, l. 1268–1281): Lemma 25 (`dddf_lemma25`) applied to
  (5.76) gives `λ_n = ρ^{n + O(√n)}`; (5.54) and (5.78) identify `ρ = 2^{-(1−ξQ)}`.
* `s6_eq6_99`, `dddfEq6_99_of_s6` — **DDDF (6.99)** (`eq:MulCont`, l. 1615–1638) from (5.76) and
  (6.98), following DDDF's computation (`S6.mulCont_log`).
* `s6_eq1_3`, `dddfEq1_3_of_s6` — **DDDF (1.3)** (l. 162–166) from (5.77) and (6.98).

The inputs (5.76), (6.98) (open, DDDF §§5.4, 6.2) and (5.54), (5.78) (DG chain) are the named
statements of `S6Defs`; see `blueprint/DDDF6-STATUS.md`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Real

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- `λ_n > 0` -/
theorem lambdaN_pos (hW : IsWhiteNoise P W) (n : ℕ) : 0 < lambdaN ξ W P n := by
  have := hW.isProbabilityMeasure
  exact T20B.ellN_pos hW inv_two_pos' inv_two_lt_one' n

namespace S6

/-- `λ_{2^{-t}}` -/
def lamT (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (t : ℝ) : ℝ :=
  lambdaDelta ξ W P ((2 : ℝ) ^ (-t))

lemma lamT_nat (n : ℕ) : lamT ξ W P n = lambdaN ξ W P n := by
  rw [lamT, lambdaN_eq_lambdaDelta, Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]

lemma two_rpow_neg_log (δ : ℝ) (hδ : 0 < δ) : (2 : ℝ) ^ (-(-Real.log δ / Real.log 2)) = δ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos (by norm_num)]
  rw [show Real.log 2 * -(-Real.log δ / Real.log 2) = Real.log δ by field_simp]
  exact Real.exp_log hδ

/-- (6.98) in log form, with positivity -/
lemma log98 (hW : IsWhiteNoise P W) (h98 : S6Eq6_98 ξ W P) :
    ∃ C₁ : ℝ, ∀ (n : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 → 0 < lamT ξ W P ((n : ℝ) + r) ∧
      |Real.log (lamT ξ W P ((n : ℝ) + r)) - Real.log (lamT ξ W P n)| ≤ C₁ := by
  obtain ⟨C, hC⟩ := h98
  refine ⟨|C|, fun n r hr0 hr1 => ?_⟩
  obtain ⟨h1, h2⟩ := hC n r hr0 hr1
  have hl := lambdaN_pos (ξ := ξ) hW n
  rw [lamT_nat]
  change exp (-C) * lambdaN ξ W P n ≤ lamT ξ W P ((n : ℝ) + r) at h1
  change lamT ξ W P ((n : ℝ) + r) ≤ exp C * lambdaN ξ W P n at h2
  have hx : 0 < lamT ξ W P ((n : ℝ) + r) := lt_of_lt_of_le (by positivity) h1
  refine ⟨hx, ?_⟩
  have l1 := Real.log_le_log (by positivity) h1
  have l2 := Real.log_le_log hx h2
  rw [Real.log_mul (by positivity) hl.ne', Real.log_exp] at l1 l2
  rw [abs_le]; constructor <;> linarith [le_abs_self C, neg_abs_le C]

/-- positivity of `λ_{2^{-t}}`, `t ≥ 0`, from (6.98) -/
lemma lamT_pos (hW : IsWhiteNoise P W) (h98 : S6Eq6_98 ξ W P) {t : ℝ} (ht : 0 ≤ t) :
    0 < lamT ξ W P t := by
  obtain ⟨C₁, hC₁⟩ := log98 hW h98
  obtain ⟨hr0, hr1, -⟩ := floor_decomp ht
  have := (hC₁ ⌊t⌋₊ (t - ⌊t⌋₊) hr0 hr1).1
  rwa [add_sub_cancel] at this

/-- (5.76) in log form -/
lemma log76 (hW : IsWhiteNoise P W) (h76 : S6Eq5_76 ξ W P) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      |Real.log (lamT ξ W P ((n : ℝ) + k)) - Real.log (lamT ξ W P n) -
        Real.log (lamT ξ W P k)| ≤ C₂ * √(k : ℝ) := by
  obtain ⟨C, hC⟩ := h76
  refine ⟨|C|, abs_nonneg C, fun n k hn hk => ?_⟩
  obtain ⟨h1, h2⟩ := hC n k hn hk
  have hn0 := lambdaN_pos (ξ := ξ) hW n
  have hk0 := lambdaN_pos (ξ := ξ) hW k
  have hnk0 := lambdaN_pos (ξ := ξ) hW (n + k)
  have e : ((n : ℝ) + k) = ((n + k : ℕ) : ℝ) := by push_cast; ring
  rw [e, lamT_nat, lamT_nat, lamT_nat]
  have l1 := Real.log_le_log (by positivity) h1
  have l2 := Real.log_le_log hnk0 h2
  rw [Real.log_mul (by positivity) hk0.ne', Real.log_mul (by positivity) hn0.ne',
    Real.log_exp] at l1 l2
  have hs := Real.sqrt_nonneg (k : ℝ)
  have a1 : C * √(k : ℝ) ≤ |C| * √(k : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self C) hs
  have a2 : -(C * √(k : ℝ)) ≤ |C| * √(k : ℝ) := by
    rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs C) hs
  rw [abs_le]; constructor <;> linarith

end S6

open S6

/-- **DDDF (6.99)** (`eq:MulCont`, l. 1615–1638) from (5.76) and (6.98). -/
theorem s6_eq6_99 (hW : IsWhiteNoise P W) (h76 : S6Eq5_76 ξ W P) (h98 : S6Eq6_98 ξ W P) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ δ' ∈ Ioo (0 : ℝ) 1,
      C⁻¹ * Real.exp (-C * Real.sqrt |Real.log (max δ δ')|) *
          (lambdaDelta ξ W P δ * lambdaDelta ξ W P δ') ≤ lambdaDelta ξ W P (δ * δ') ∧
        lambdaDelta ξ W P (δ * δ') ≤
          C * Real.exp (C * Real.sqrt |Real.log (max δ δ')|) *
            (lambdaDelta ξ W P δ * lambdaDelta ξ W P δ') := by
  obtain ⟨C₁, hC₁⟩ := log98 hW h98
  obtain ⟨C₂, hC₂, hC₂'⟩ := log76 hW h76
  set a : ℝ → ℝ := fun t => Real.log (lamT ξ W P t)
  have hmc := mulCont_log (a := a) hC₂ (fun n r h0 h1 => (hC₁ n r h0 h1).2)
    (fun n k hn hk => hC₂' n k hn hk)
  set B := 4 * C₁ + |a 0|
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs2 : 0 < √(Real.log 2) := Real.sqrt_pos.2 hl2
  set C := Real.exp B + C₂ / √(Real.log 2) + 1
  have hCpos : 0 < C := by positivity
  have hlogC : B ≤ Real.log C := by
    rw [Real.le_log_iff_exp_le hCpos]; have : 0 ≤ C₂ / √(Real.log 2) := by positivity
    linarith
  have hC2C : C₂ / √(Real.log 2) ≤ C := by have := Real.exp_pos B; linarith
  refine ⟨C, hCpos, fun δ hδ δ' hδ' => ?_⟩
  set t := -Real.log δ / Real.log 2
  set t' := -Real.log δ' / Real.log 2
  have hlδ : Real.log δ < 0 := Real.log_neg hδ.1 hδ.2
  have hlδ' : Real.log δ' < 0 := Real.log_neg hδ'.1 hδ'.2
  have ht : 0 ≤ t := div_nonneg (by linarith) hl2.le
  have ht' : 0 ≤ t' := div_nonneg (by linarith) hl2.le
  have eδ : (2 : ℝ) ^ (-t) = δ := two_rpow_neg_log δ hδ.1
  have eδ' : (2 : ℝ) ^ (-t') = δ' := two_rpow_neg_log δ' hδ'.1
  have eδδ : (2 : ℝ) ^ (-(t + t')) = δ * δ' := by
    rw [neg_add, Real.rpow_add (by norm_num), eδ, eδ']
  have hx : lambdaDelta ξ W P (δ * δ') = lamT ξ W P (t + t') := by rw [lamT, eδδ]
  have hy : lambdaDelta ξ W P δ = lamT ξ W P t := by rw [lamT, eδ]
  have hz : lambdaDelta ξ W P δ' = lamT ξ W P t' := by rw [lamT, eδ']
  -- `|log (δ ∨ δ')| = (t ∧ t') log 2`
  have hL : |Real.log (max δ δ')| = min t t' * Real.log 2 := by
    have et : Real.log δ = -(t * Real.log 2) := by simp only [t]; field_simp
    have et' : Real.log δ' = -(t' * Real.log 2) := by simp only [t']; field_simp
    rcases le_total t t' with h | h
    · have : δ' ≤ δ := by
        rw [← Real.log_le_log_iff hδ'.1 hδ.1, et, et']; nlinarith
      rw [max_eq_left this, min_eq_left h, et, abs_neg, abs_of_nonneg (by positivity)]
    · have : δ ≤ δ' := by
        rw [← Real.log_le_log_iff hδ.1 hδ'.1, et, et']; nlinarith
      rw [max_eq_right this, min_eq_right h, et', abs_neg, abs_of_nonneg (by positivity)]
  set L := |Real.log (max δ δ')|
  have hsm : C₂ * √(min t t') ≤ C * √L := by
    have : √(min t t') = √L / √(Real.log 2) := by
      rw [hL, Real.sqrt_mul (le_min ht ht'), mul_div_assoc, div_self hs2.ne', mul_one]
    rw [this]
    calc C₂ * (√L / √(Real.log 2)) = C₂ / √(Real.log 2) * √L := by ring
      _ ≤ C * √L := mul_le_mul_of_nonneg_right hC2C (Real.sqrt_nonneg _)
  have hxp := lamT_pos hW h98 (add_nonneg ht ht')
  have hyp := lamT_pos hW h98 ht
  have hzp := lamT_pos hW h98 ht'
  have hk := hmc t t' ht ht'
  obtain ⟨k1, k2⟩ := abs_le.1 hk
  simp only [a] at k1 k2
  rw [hx, hy, hz]
  constructor
  · rw [← Real.log_le_log_iff (by positivity) hxp, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul hyp.ne' hzp.ne', Real.log_inv,
      Real.log_exp]
    have : -C * √L = -(C * √L) := by ring
    rw [this]; linarith
  · rw [← Real.log_le_log_iff hxp (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul hyp.ne' hzp.ne', Real.log_exp]
    linarith

/-- **DDDF (6.99)** = `Blueprint.DDDFEq6_99`, from (5.76) and (6.98) for `ξ = γ/d_γ`. -/
theorem dddfEq6_99_of_s6
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        S6Eq5_76 (xiGamma γ) W P ∧ S6Eq6_98 (xiGamma γ) W P) :
    Blueprint.DDDFEq6_99 := by
  intro γ hγ hγ2 Ω _ P W hW
  obtain ⟨h76, h98⟩ := h γ hγ hγ2 P W hW
  exact s6_eq6_99 hW h76 h98

end DDDF
end LQGMetric
