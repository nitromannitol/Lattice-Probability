/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate2L419B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422F
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasB4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det3

/-!
# GM Lemma 4.19: `s_{k+1} ≤ τ_{2ℓ𝕣}` in the form `𝓑^•_{s_{k+1}} ⊂ B_{3ℓ𝕣}(𝕫)` on `ℰ_𝕣`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.19 (`lem-holder-balls`,
l. 2318–2327; "if `F_k` occurs then `s_{k+1} ≤ τ_{2ℓ𝕣}`"), proof of Lemma 4.22 l. 2545
("By (4.36), we have `s_{k+1} ≤ τ_{2ℓ𝕣}`"). `gm_filledBall_s_subset_ball`: the step of
`gm_L4_22` without the auxiliary point `z` (from `gm_S4_3` and condition 2 at `𝕫`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **`𝓑^•_{s_{k+1}} ⊂ B_{3ℓ𝕣}(𝕫)` on `ℰ_𝕣`** for `k ≤ K` (`(k+1)ε^β ≤ a/c₂`) -/
theorem gm_filledBall_s_subset_ball {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric}
    {P : Measure Ω} {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} (R : RegPar) {𝕣 a ε β : ℝ}
    (h𝕣 : 0 < 𝕣) (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ R.ℓ) (hχ : 0 ≤ R.χ)
    (hUV : R.U ⊆ R.V) (hc : 0 < R.c 𝕣) (hξ : 0 ≤ R.ξ) (hε0 : 0 < ε)
    {ω : Ω} (hω : ω ∈ regEvent D P h H R 𝕣 a) {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.U)
    (hH0 : H 𝕣 0 ω = circleAvg (h ω) 𝕣 0) (hH𝕫 : H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫) {k : ℕ}
    (hk : ((k + 1 : ℕ) : ℝ) * ε ^ β ≤ a / regC2const R a) :
    filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) ⊆ ball 𝕫 (3 * (R.ℓ * 𝕣)) := by
  have hℓ : 0 < R.ℓ := lt_of_lt_of_le ha0 haℓ
  have hs'2 := gm_S4_3 hω hc hξ h𝕣 hℓ ha0 ha1 hχ hUV h𝕫 hH0 hH𝕫 hk
  obtain ⟨_, h2, _⟩ := gm_regEvent_mem.1 hω
  have h𝕫R : 𝕫 ∈ regRegion R 𝕣 :=
    Metric.self_subset_thickening (by positivity) _ (image_mono hUV h𝕫)
  have h2𝕫 := h2 𝕫 h𝕫R
  have hpos : 0 < a * max (R.c 𝕣 * Real.exp (R.ξ * H 𝕣 𝕫 ω))
      (R.c (R.ℓ * 𝕣) * Real.exp (R.ξ * H (R.ℓ * 𝕣) 𝕫 ω)) :=
    mul_pos ha0 (lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (le_max_left _ _))
  have hs'3 : s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω < tauR D h 𝕫 (3 * (R.ℓ * 𝕣)) ω := by
    have := h2𝕫.2.trans (min_le_right _ _)
    linarith
  have hs0 : 0 < s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω := by
    rw [gm_s4S_eq]
    have := gm_tauD_pos (D (h ω)) 𝕫 (mul_pos hℓ h𝕣)
    have : 0 ≤ ((k + 1 : ℕ) : ℝ) * ε ^ β :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hε0.le β)
    positivity
  exact gm_filledBall_subset_ball_of_lt_tauR hs0 hs'3

end LQGMetric.GM
