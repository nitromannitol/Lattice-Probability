/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.IterateRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodCount

/-!
# GM Lemma 4.21 and Proposition 4.17: the `o^∞_ε(ε)` rates

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.21
(l. 2378–2383: Lemma 4.18 with `m = ⌊4ε^θK⌋`, `α = 1/2`, `δ = 1/4`) and of Proposition 4.17
(l. 2404–2433: `α = 1 − ε^{2ν+ζ/2}`, `δ = ε^{2ν+ζ/2}/2`, the bound (4.43)
`exp(−½ε^{4ν+ζ}⌊(1−4ε^θ)K⌋)`, and "since `K ≍ ε^{-β}`, if `4ν < β` then for a small enough
`ζ` the quantity (4.43) is `o^∞_ε(ε)`").

`gm_P4_17_rate` collects the real-variable estimates which turn `gm_P4_17_core` into GM's
statement. We use `m₁ = ⌈4ε^θK⌉ + 4` (`p417m`) instead of `⌊4ε^θK⌋`: the corrected Lemma 4.18
(D29) has `n = K + 1` indices, and with this `m₁` the count threshold of Proposition 4.12,
`(1 − ε^θ)K`, dominates the threshold `n − m₁/4` of Lemma 4.18 (item 1). The hypotheses
`θ < β` and `4ν + ζ < β` are the paper's (`K ≍ ε^{-β}` and `m ≍ ε^{θ}K` must tend to `∞`;
GM's `θ < β/2` from Lemma 4.15 Step 4 gives the first).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology

namespace LQGMetric.GM

/-- `m₁ = ⌈4ε^θK⌉ + 4`, the parameter `m` of the first application of Lemma 4.18 -/
def p417m (ε θ : ℝ) (K : ℕ) : ℕ := ⌈4 * ε ^ θ * K⌉₊ + 4

theorem gm_tendsto_rpow_zero {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun ε : ℝ => ε ^ θ) (𝓝[>] 0) (𝓝 0) := by
  have := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto
  rw [Real.zero_rpow hθ.ne'] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **The rates of GM Lemma 4.21 and Proposition 4.17** (l. 2378–2433) -/
theorem gm_P4_17_rate {b β θ ν ζ : ℝ} (hb : 0 < b) (hθ : 0 < θ) (hθβ : θ < β)
    (hζ : 0 < ζ) (hβν : 4 * ν + ζ < β) (M : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ K : ℕ, b * ε ^ (-β) ≤ K + 2 →
      ((K + 1 : ℕ) : ℝ) - (p417m ε θ K : ℝ) / 4 ≤ (1 - ε ^ θ) * K ∧
      p417m ε θ K ≤ K + 1 ∧
      Real.exp (-2 * (1 / 4) ^ 2 * (p417m ε θ K : ℝ)) ≤ ε ^ M ∧
      ∀ p : ℝ, ε ^ (2 * ν + ζ / 2) ≤ p →
        Real.exp (-2 * (p / 4) ^ 2 * ((K + 1 - p417m ε θ K : ℕ) : ℝ)) ≤ ε ^ M ∧
        ε ^ (2 * ν + ζ) * K ≤ p / 4 * ((K + 1 - p417m ε θ K : ℕ) : ℝ) := by
  have hβ : 0 < β := by linarith
  obtain ⟨ε₁, hε₁, h₁⟩ := gm_exp_neg_rpow_le_rpow (b := b / 4) (by positivity)
    (show 0 < β - θ by linarith) M
  obtain ⟨ε₂, hε₂, h₂⟩ := gm_exp_neg_rpow_le_rpow (b := b / 32) (by positivity)
    (show 0 < β - (4 * ν + ζ) by linarith) M
  have hc2 : Tendsto (fun ε : ℝ => b * ε ^ (-β)) (𝓝[>] 0) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : -β < 0)).const_mul_atTop hb
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ θ ≤ 1 / 16 :=
    (gm_tendsto_rpow_zero hθ).eventually (Iic_mem_nhds (by norm_num))
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (ζ / 2) ≤ 1 / 8 :=
    (gm_tendsto_rpow_zero (by linarith : 0 < ζ / 2)).eventually (Iic_mem_nhds (by norm_num))
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 18 ≤ b * ε ^ (-β) := hc2.eventually_ge_atTop 18
  have e4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 (min (min ε₁ ε₂) 1) :=
    Ioo_mem_nhdsGT (lt_min (lt_min hε₁ hε₂) one_pos)
  obtain ⟨ε₀, hε₀, hε₀'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (e1.and (e2.and (e3.and e4)))
  refine ⟨ε₀, hε₀, fun ε hε K hK => ?_⟩
  obtain ⟨hθ16, hζ8, h18, hεm⟩ := hε₀' hε
  have hε0 := hε.1
  have hεε₁ : ε < ε₁ := lt_of_lt_of_le hεm.2 ((min_le_left _ _).trans (min_le_left _ _))
  have hεε₂ : ε < ε₂ := lt_of_lt_of_le hεm.2 ((min_le_left _ _).trans (min_le_right _ _))
  have hθp : 0 < ε ^ θ := Real.rpow_pos_of_pos hε0 _
  have hKb : b * ε ^ (-β) / 2 ≤ (K : ℝ) := by linarith
  have hK16 : (16 : ℝ) ≤ K := by linarith
  -- bounds on `m₁`
  have hm_lo : 4 * ε ^ θ * K + 4 ≤ (p417m ε θ K : ℝ) := by
    unfold p417m; push_cast
    have := Nat.le_ceil (4 * ε ^ θ * K); linarith
  have hm_hi : (p417m ε θ K : ℝ) < 4 * ε ^ θ * K + 5 := by
    unfold p417m; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ 4 * ε ^ θ * K by positivity); linarith
  have hθK : ε ^ θ * K ≤ K / 16 := by nlinarith
  have hmK : (p417m ε θ K : ℝ) ≤ K + 1 := by linarith
  have hmK' : p417m ε θ K ≤ K + 1 := by exact_mod_cast hmK
  have hnm : ((K + 1 - p417m ε θ K : ℕ) : ℝ) = K + 1 - p417m ε θ K := by
    push_cast [hmK']; ring
  have hnmK : (K : ℝ) / 2 ≤ ((K + 1 - p417m ε θ K : ℕ) : ℝ) := by rw [hnm]; linarith
  refine ⟨?_, hmK', ?_, fun p hp => ?_⟩
  · push_cast; linarith
  · refine le_trans (Real.exp_le_exp.2 ?_) (h₁ ε ⟨hε0, hεε₁⟩)
    have hpow : ε ^ θ * ε ^ (-β) = ε ^ (-(β - θ)) := by
      rw [← Real.rpow_add hε0]; congr 1; ring
    have : b / 4 * ε ^ (-(β - θ)) ≤ ε ^ θ * K / 2 := by
      rw [← hpow]
      have := mul_le_mul_of_nonneg_left hKb hθp.le
      nlinarith
    nlinarith
  · set q := ε ^ (2 * ν + ζ / 2)
    have hq : 0 < q := Real.rpow_pos_of_pos hε0 _
    have hpq : 0 < p := hq.trans_le hp
    have hq2 : q ^ 2 * ε ^ (-β) = ε ^ (-(β - (4 * ν + ζ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le, ← Real.rpow_add hε0]
      congr 1; push_cast; ring
    have hqζ : ε ^ (2 * ν + ζ) = q * ε ^ (ζ / 2) := by
      rw [← Real.rpow_add hε0]; congr 1; ring
    have hKn : 0 ≤ ((K + 1 - p417m ε θ K : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨le_trans (Real.exp_le_exp.2 ?_) (h₂ ε ⟨hε0, hεε₂⟩), ?_⟩
    · have hpp : q ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hq.le hp 2
      have h1 : b / 32 * (q ^ 2 * ε ^ (-β)) ≤ 2 * (p / 4) ^ 2 * ((K + 1 - p417m ε θ K : ℕ) : ℝ) := by
        have hKq : q ^ 2 * (b * ε ^ (-β) / 2) ≤ q ^ 2 * (K : ℝ) :=
          mul_le_mul_of_nonneg_left hKb (by positivity)
        have : p ^ 2 * ((K : ℝ) / 2) ≤ p ^ 2 * ((K + 1 - p417m ε θ K : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hnmK (by positivity)
        have : q ^ 2 * (K : ℝ) ≤ p ^ 2 * K := mul_le_mul_of_nonneg_right hpp (by positivity)
        nlinarith
      rw [hq2] at h1
      linarith
    · rw [hqζ]
      have h1 : q * ε ^ (ζ / 2) * K ≤ q * (1 / 8) * K :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hζ8 hq.le) (by positivity)
      have h2 : q / 4 * ((K : ℝ) / 2) ≤ p / 4 * ((K + 1 - p417m ε θ K : ℕ) : ℝ) :=
        mul_le_mul (by linarith) hnmK (by positivity) (by linarith)
      linarith

end LQGMetric.GM
