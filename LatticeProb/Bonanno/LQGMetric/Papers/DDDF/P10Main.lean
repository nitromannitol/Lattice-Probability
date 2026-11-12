/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P10Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Core
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Space

/-!
# DDDF Proposition 10 (`Prop:RSWconf`, arXiv:1904.08021, `tightness.tex` l. 725–736)

`prop10`: for a white noise `W` and `ξ > 0`, `Prop10 ξ P W` holds. Proof (DF Props. 4.5–4.6,
arXiv:1809.02607, l. 534–608): on the enlarged space `(Ω × Ω, P ⊗ P)` with the independent
white noises `W ∘ fst`, `W ∘ snd` and the coupled noise `W̃` (DDDF l. 541–543), `p10_core` gives
`P(L ≤ l) ≤ P(L' ≤ ‖F'‖_K e^{ξx} e^s l) + C₆ e^{−c₆x²} + ε₁`; with
`x = √((log(4C₆) + log ε⁻¹)/c₆)` and `ε₁ = min(ε/4, e^{−ξ²σ²/2}/2)` both error terms are
`≤ ε/4`, and `ξx + s ≤ C √|log(ε/2C)|` (`p10_exponent_le`). The laws of `L`, `L'` on the enlarged
space are those of the statement (`measure_crossLenIn_le_eq`, D-DDDF-18).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise WNPush

/-- the exponent bound: `ξ x + s ≤ C √|log(ε/2C)|` for `ε < 1/2` -/
lemma p10_exponent_le {ξ c₆ σ C₆ : ℝ} (hξ : 0 < ξ) (hc₆ : 0 < c₆) (hC₆ : 1 ≤ C₆) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ξ * √((Real.log (4 * C₆) + Real.log ε⁻¹) / c₆) +
        √(2 * (ξ * σ) ^ 2 * Real.log (min (ε / 4) (Real.exp (-(ξ * σ) ^ 2 / 2) / 2))⁻¹) ≤
      C * √|Real.log (ε / (2 * C))| := by
  set τ := ξ * σ
  set a₁ := Real.log (4 * C₆)
  set a₂ := Real.log 8 + τ ^ 2 / 2
  have ha₁ : 0 ≤ a₁ := Real.log_nonneg (by linarith)
  have ha₂ : 0 ≤ a₂ := by have := Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num); positivity
  set K₀ := ξ * √((2 * a₁ + 1) / c₆) + √(2 * τ ^ 2 * (2 * a₂ + 1))
  refine ⟨max 1 K₀, le_max_left _ _, fun ε hε0 hε => ?_⟩
  set C := max 1 K₀
  have hC1 : 1 ≤ C := le_max_left _ _
  set ℓ := Real.log ε⁻¹
  have hℓ : 1 / 2 ≤ ℓ := by
    have h2 : Real.log 2 < ℓ := Real.log_lt_log (by norm_num) (by
      rw [lt_inv_comm₀ (by norm_num) hε0]; linarith)
    have := Real.log_two_gt_d9
    linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hx : √((a₁ + ℓ) / c₆) ≤ √((2 * a₁ + 1) / c₆) * √ℓ := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hc₆.le
    nlinarith
  set ε' := Real.exp (-τ ^ 2 / 2)
  have hε'0 : 0 < ε' := Real.exp_pos _
  have hε'1 : ε' ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg τ])
  set ε₁ := min (ε / 4) (ε' / 2)
  have hε₁ : ε / 4 * (ε' / 2) ≤ ε₁ := le_min
    (mul_le_of_le_one_right (by positivity) (by linarith))
    (mul_le_of_le_one_left (by positivity) (by linarith))
  have hlog : Real.log ε₁⁻¹ ≤ a₂ + ℓ := by
    rw [Real.log_inv]
    have h1 := Real.log_le_log (by positivity) hε₁
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by norm_num),
      Real.log_div (by positivity) (by norm_num), Real.log_exp] at h1
    have e8 : Real.log 8 = Real.log 4 + Real.log 2 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    simp only [a₂, ℓ, Real.log_inv]
    linarith
  have hs : √(2 * τ ^ 2 * Real.log ε₁⁻¹) ≤ √(2 * τ ^ 2 * (2 * a₂ + 1)) * √ℓ := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have : Real.log ε₁⁻¹ ≤ (2 * a₂ + 1) * ℓ := hlog.trans (by nlinarith)
    have h2 : 0 ≤ 2 * τ ^ 2 := by positivity
    calc 2 * τ ^ 2 * Real.log ε₁⁻¹ ≤ 2 * τ ^ 2 * ((2 * a₂ + 1) * ℓ) :=
          mul_le_mul_of_nonneg_left this h2
      _ = _ := by ring
  have hL : ℓ ≤ |Real.log (ε / (2 * C))| := by
    have h1 : Real.log (ε / (2 * C)) = -ℓ - Real.log (2 * C) := by
      rw [Real.log_div hε0.ne' (by positivity)]; simp [ℓ, Real.log_inv]
    have h2 : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
    rw [h1, abs_of_nonpos (by linarith)]
    linarith
  calc ξ * √((a₁ + ℓ) / c₆) + √(2 * τ ^ 2 * Real.log ε₁⁻¹)
      ≤ ξ * (√((2 * a₁ + 1) / c₆) * √ℓ) + √(2 * τ ^ 2 * (2 * a₂ + 1)) * √ℓ :=
        add_le_add (mul_le_mul_of_nonneg_left hx hξ.le) hs
    _ = K₀ * √ℓ := by ring
    _ ≤ C * √|Real.log (ε / (2 * C))| :=
        mul_le_mul (le_max_right _ _) (Real.sqrt_le_sqrt hL) (Real.sqrt_nonneg _)
          (by linarith)

/-- **DDDF Proposition 10** (`Prop:RSWconf`, l. 725–736; proof DF Props. 4.5–4.6). -/
theorem prop10 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) : Prop10 ξ P W := by
  have hP := hW.isProbabilityMeasure
  intro K A B U F hK hA hB hAK hBK hF
  have hW₁ := isWhiteNoise_fst hW
  have hW₂ := isWhiteNoise_snd hW
  have hind := indepFun_fst_snd_noise hW
  obtain ⟨C₆, c₆, σ, hC₆, hc₆, hσ, hcore⟩ := p10_core hξ hK hF hW₁ hW₂ hind
  set C₆' := max C₆ 1
  obtain ⟨C, hC1, hCexp⟩ := p10_exponent_le (σ := σ) hξ hc₆ (le_max_right C₆ 1)
  refine ⟨C, by linarith, fun n l ε hl hε0 hε => ?_⟩
  have hℓ : 0 < Real.log ε⁻¹ := Real.log_pos (by rw [lt_inv_comm₀ one_pos hε0]; linarith)
  have ha₁ : 0 ≤ Real.log (4 * C₆') := Real.log_nonneg (by
    have := le_max_right C₆ 1; linarith)
  set x := √((Real.log (4 * C₆') + Real.log ε⁻¹) / c₆)
  have hx : 0 < x := Real.sqrt_pos.2 (by positivity)
  set ε' := Real.exp (-(ξ * σ) ^ 2 / 2)
  set ε₁ := min (ε / 4) (ε' / 2)
  have hε₁ : 0 < ε₁ := lt_min (by positivity) (by positivity)
  have hε₁' : ε₁ < ε' := (min_le_right _ _).trans_lt (by have := Real.exp_pos (-(ξ * σ) ^ 2 / 2); linarith)
  have key := hcore n l x ε₁ hx hε₁ hε₁'
  have htail : C₆ * Real.exp (-c₆ * x ^ 2) ≤ ε / 4 := by
    have hx2 : c₆ * x ^ 2 = Real.log (4 * C₆') + Real.log ε⁻¹ := by
      rw [Real.sq_sqrt (by positivity)]; field_simp
    have e : Real.exp (-c₆ * x ^ 2) = ε / (4 * C₆') := by
      rw [neg_mul, hx2, neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg,
        Real.exp_log (by have := le_max_right C₆ 1; positivity), Real.exp_log (by positivity)]
      field_simp
    rw [e]
    have h1 : C₆ ≤ C₆' := le_max_left _ _
    have h2 : 0 < C₆' := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set S := derivSup F K
  have hS : 0 ≤ S := Real.sSup_nonneg (by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _)
  have hlen : S * Real.exp (ξ * x) * Real.exp (√(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹)) * l ≤
      p10Len C l ε S := by
    have hE := hCexp ε hε0 hε
    have h1 : Real.exp (ξ * x) * Real.exp (√(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹)) ≤
        C * Real.exp (C * √|Real.log (ε / (2 * C))|) := by
      rw [← Real.exp_add]
      calc Real.exp (ξ * x + √(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹))
          ≤ Real.exp (C * √|Real.log (ε / (2 * C))|) := Real.exp_le_exp.2 hE
        _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le hC1
    unfold p10Len
    calc S * Real.exp (ξ * x) * Real.exp (√(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹)) * l
        = (S * l) * (Real.exp (ξ * x) * Real.exp (√(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹))) := by
          ring
      _ ≤ (S * l) * (C * Real.exp (C * √|Real.log (ε / (2 * C))|)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hK' : IsCompact (F '' K) := hK.image_of_continuousOn (hF.diff.continuousOn.mono hF.sub)
  have hT1 := measure_crossLenIn_le_eq (ξ := ξ) (A := A) (B := B) hK hW hW₁ n (ENNReal.ofReal l)
  have hT2 := measure_crossLenIn_le_eq (ξ := ξ) (A := F '' A) (B := F '' B) hK' hW
    (isWhiteNoise_coupledNoise hF.confHyp hW₁ hW₂ hind) n (ENNReal.ofReal (p10Len C l ε S))
  have hmain : P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) K A B ≤ ENNReal.ofReal l} ≤
      P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (F '' K) (F '' A) (F '' B) ≤
        ENNReal.ofReal (p10Len C l ε S)} + ENNReal.ofReal (ε / 2) := by
    rw [hT1, hT2]
    refine key.trans ?_
    have e : ENNReal.ofReal (ε / 2) = ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    rw [e, ← add_assoc]
    refine add_le_add (add_le_add (measure_mono fun ω hω => ?_) (ENNReal.ofReal_le_ofReal htail))
      (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    exact hω.trans (ENNReal.ofReal_le_ofReal hlen)
  constructor
  · intro h1
    have h2 := tsub_le_iff_right.2 (h1.trans hmain)
    rw [← ENNReal.ofReal_sub _ (by positivity)] at h2
    exact (ENNReal.ofReal_le_ofReal (by linarith)).trans h2
  · intro h1
    have h2 := tsub_le_iff_right.2 (h1.trans hmain)
    rw [← ENNReal.ofReal_sub _ (by positivity)] at h2
    exact (ENNReal.ofReal_le_ofReal (by linarith)).trans h2

end DDDF
end LQGMetric
