/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7Mass at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3VarBdry
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3D6

/-!
# DZZ Lemma 3.7, first display: mass of small boxes near a light box (P2-DZZ3D, WP-113)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) proof of Lemma 3.7, l. 973–986: on
`{M_{γ,s}(B) ≤ δ²} ∩ 𝓔_{δ,α}`, for every `B̃ ∈ 𝓑(B, t) ∪ 𝓑_∂(B_large, t)`,
`M_{γ,ts}(B̃) ≤ δ² e^{2γα√L log L} t² e^{γ η^{ε²s}_{ts}(c̃) − γ²/2 Var η^{ε²s}_{ts}(c̃)}`.

* `approxLQG_fine_le` (deterministic): given the `𝓔_{δ,α}` bound
  `|η_s(c_B) − η_{ε²s}(c̃)| ≤ T`, the decomposition `η_{ts}(c̃) = η_{ε²s}(c̃) + η^{ε²s}_{ts}(c̃)` and
  `M_s(B) ≤ δ²`,
  `M_{ts}(B̃) ≤ δ² (s_{B̃}/s_B)² e^{γT + γ²/2 · 2√8608 √(log s⁻¹ + 4)} e^{γ η^{ε²s}_{ts}(c̃) − γ²/2 Var}`.
  The variance mismatch `Var η_s(c_B) − Var η_{ε²s}(c̃)` is `etaVar_sub_fine_le` (S3VarBdry).
* `approxLQG_fine_le_of_mem`: the same on `nbrFineEvent` (`𝓔_{δ,α}`'s η-part, D64a).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma DyBox.side_le_one (b : DyBox) : b.side ≤ 1 := by
  unfold DyBox.side; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma DyBox.side_pos' (b : DyBox) : 0 < b.side := by unfold DyBox.side; positivity

lemma inv_two_pow_le_side {b : DyBox} {N : ℕ} (h : N ≤ b.n) : b.side ≤ (2 : ℝ)⁻¹ ^ N := by
  unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

lemma side_le_inv_two_pow {b : DyBox} {N : ℕ} (h : b.n ≤ N) : (2 : ℝ)⁻¹ ^ N ≤ b.side := by
  unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- **DZZ l. 975 (deterministic part)**. With `e₂ = 2^{-(m+j)}` (`= ε² s`), `B̃` of level
`≥ m + j` at distance `≤ 8 s` from `c_B`. -/
theorem approxLQG_fine_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) {b bt : DyBox} {j : ℕ}
    (hj : b.n + j ≤ bt.n) (hc : ‖b.center - bt.center‖ ≤ 8 * b.side) {ω : Ω} {T δ : ℝ}
    (hT : |etaInf W b.side b.center ω - etaInf W ((2 : ℝ)⁻¹ ^ (b.n + j)) bt.center ω| ≤ T)
    (hdec : etaInf W bt.side bt.center ω = etaInf W ((2 : ℝ)⁻¹ ^ (b.n + j)) bt.center ω +
      eta W bt.side ((2 : ℝ)⁻¹ ^ (b.n + j)) bt.center ω)
    (hM : approxLQG γ W ω b ≤ δ ^ 2) :
    approxLQG γ W ω bt ≤ δ ^ 2 * (bt.side / b.side) ^ 2 *
      Real.exp (γ * T + γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4))) *
      Real.exp (γ * eta W bt.side ((2 : ℝ)⁻¹ ^ (b.n + j)) bt.center ω -
        γ ^ 2 / 2 * etaBandVar bt.side ((2 : ℝ)⁻¹ ^ (b.n + j)) bt.center) := by
  set e₂ : ℝ := (2 : ℝ)⁻¹ ^ (b.n + j)
  set s := b.side
  have hs0 : 0 < s := DyBox.side_pos' b
  have hs1 : s ≤ 1 := DyBox.side_le_one b
  have hbt0 : 0 < bt.side := DyBox.side_pos' bt
  have hbte : bt.side ≤ e₂ := inv_two_pow_le_side hj
  have he0 : 0 < e₂ := by positivity
  have hes : e₂ ≤ s := side_le_inv_two_pow (Nat.le_add_right _ _)
  -- variances
  have hsplit := etaVar_split hbt0 hbte bt.center
  have hD := etaVar_sub_fine_le hW he0 hes hs1 b.center bt.center
  have hsq : Real.sqrt (1076 * ‖b.center - bt.center‖ / s) ≤ Real.sqrt 8608 := by
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hs0]; nlinarith
  have hV0 : 0 ≤ Real.sqrt (Real.log s⁻¹ + 4) := Real.sqrt_nonneg _
  have hD' : etaVar s b.center - etaVar e₂ bt.center ≤
      2 * Real.sqrt 8608 * Real.sqrt (Real.log s⁻¹ + 4) := by
    refine hD.trans ?_
    have := mul_le_mul_of_nonneg_right hsq hV0
    nlinarith
  -- exponents
  set A := γ * etaInf W s b.center ω - γ ^ 2 / 2 * etaVar s b.center
  set Cb := γ * eta W bt.side e₂ bt.center ω - γ ^ 2 / 2 * etaBandVar bt.side e₂ bt.center
  set R := γ * T + γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log s⁻¹ + 4))
  have hTa := (abs_le.1 hT).2
  have hTb := (abs_le.1 hT).1
  have hexp : γ * etaInf W bt.side bt.center ω - γ ^ 2 / 2 * etaVar bt.side bt.center ≤
      A + R + Cb := by
    rw [hdec, hsplit]
    simp only [A, R, Cb, etaBandVar]
    have hγ2 : 0 ≤ γ ^ 2 / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hD' hγ2, mul_le_mul_of_nonneg_left hTb hγ.le]
  have hMb : s ^ 2 * Real.exp A ≤ δ ^ 2 := hM
  calc approxLQG γ W ω bt
      = bt.side ^ 2 * Real.exp (γ * etaInf W bt.side bt.center ω -
          γ ^ 2 / 2 * etaVar bt.side bt.center) := rfl
    _ ≤ bt.side ^ 2 * Real.exp (A + R + Cb) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) (by positivity)
    _ = (bt.side / s) ^ 2 * (s ^ 2 * Real.exp A) * Real.exp R * Real.exp Cb := by
        rw [Real.exp_add, Real.exp_add, div_pow]; field_simp
    _ ≤ (bt.side / s) ^ 2 * δ ^ 2 * Real.exp R * Real.exp Cb := by
        gcongr
    _ = δ ^ 2 * (bt.side / s) ^ 2 * Real.exp R * Real.exp Cb := by ring

end DZZ
end LQGMetric
