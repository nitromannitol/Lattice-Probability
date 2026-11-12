/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate5Rate at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The rate condition of Lemma 4.7 in Proposition 4.17 (DEC-89, packet C)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.7 (4.14) as used in
Lemma 4.21 (l. 2380–2390: `κ = ε^{2ν+o(1)}`, `e = o^∞_ε(ε)`) and Proposition 4.17 (l. 2404–2433:
`P[𝒵^𝔈_k ≠ ∅ | 𝓕_k] ≥ ε^{2ν+ζ/2}`). In `gm_h47_k`, `κ = (Λ X)⁻¹` and `e = g / X` with
`X = N c₁ ε^{-(2ν + 1/M₈)} + 1` (`N = #ℛ ≲ log ε⁻¹`, the count bound (4.19) with exponent `M₈`) and
`g = #(candidates) √δ`; for `M₈ > 2/ζ` and `g ≤ 1/(4Λ)` this gives `ε^{2ν+ζ/2} ≤ κ/2 − e` for small
`ε` (`gm_T42_rate_abs`). Own elementary proof of GM's "`κ = ε^{2ν+o(1)}`".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace LQGMetric.GM

theorem gm_tendsto_rpow_zero' {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun ε : ℝ => ε ^ θ) (𝓝[>] 0) (𝓝 0) := by
  have := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto
  rw [Real.zero_rpow hθ.ne'] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **`ε^{2ν+ζ/2} ≤ κ/2 − e`** for small `ε` (GM l. 2380–2433) -/
theorem gm_T42_rate_abs {Λ c₁ c₄ ν ζ M₈ : ℝ} (hΛ : 0 < Λ) (hc₁ : 0 ≤ c₁)
    (hν : 0 ≤ ν) (hζ : 0 < ζ) (hM0 : 0 < M₈) (hM : 2 / ζ < M₈) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₂, ∀ N g : ℝ, 0 ≤ N →
      N ≤ c₄ * Real.log ε⁻¹ + 1 → 0 ≤ g → g ≤ 1 / (4 * Λ) →
      ε ^ (2 * ν + ζ / 2) ≤ (Λ * (N * (c₁ * ε ^ (-(2 * ν + 1 / M₈))) + 1))⁻¹ / 2 -
        g / (N * (c₁ * ε ^ (-(2 * ν + 1 / M₈))) + 1) := by
  set s := 2 * ν + ζ / 2 with hs
  set t := ζ / 2 - 1 / M₈ with ht
  have hs0 : 0 < s := by rw [hs]; linarith
  have ht0 : 0 < t := by
    rw [ht]
    have : 1 / M₈ < ζ / 2 := by
      rw [div_lt_iff₀ hM0]
      rw [div_lt_iff₀ hζ] at hM
      linarith
    linarith
  have hlim : Tendsto (fun ε : ℝ => c₁ * (c₄ * (-(Real.log ε * ε ^ t)) + ε ^ t) + ε ^ s)
      (𝓝[>] 0) (𝓝 (c₁ * (c₄ * (-0) + 0) + 0)) :=
    (tendsto_const_nhds.mul ((tendsto_const_nhds.mul
      (tendsto_log_mul_rpow_nhdsGT_zero ht0).neg).add (gm_tendsto_rpow_zero' ht0))).add
      (gm_tendsto_rpow_zero' hs0)
  simp only [neg_zero, mul_zero, add_zero] at hlim
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c₁ * (c₄ * (-(Real.log ε * ε ^ t)) + ε ^ t) + ε ^ s < 1 / (4 * Λ) :=
    hlim.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨ε₂, hε₂, hε₂'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  refine ⟨ε₂, hε₂, fun ε hε N g hN hNl hg hg4 => ?_⟩
  have hε0 := hε.1
  have hf := hε₂' hε
  simp only [mem_setOf_eq] at hf
  set X := N * (c₁ * ε ^ (-(2 * ν + 1 / M₈))) + 1 with hX
  have hX1 : 1 ≤ X := by
    have : 0 ≤ N * (c₁ * ε ^ (-(2 * ν + 1 / M₈))) :=
      mul_nonneg hN (mul_nonneg hc₁ (Real.rpow_nonneg hε0.le _))
    linarith
  have hX0 : 0 < X := by linarith
  have hsX : ε ^ s * X = N * c₁ * ε ^ t + ε ^ s := by
    rw [hX, mul_add, mul_one]
    congr 1
    have : ε ^ s * ε ^ (-(2 * ν + 1 / M₈)) = ε ^ t := by
      rw [← Real.rpow_add hε0, hs, ht]; ring_nf
    calc ε ^ s * (N * (c₁ * ε ^ (-(2 * ν + 1 / M₈))))
        = N * c₁ * (ε ^ s * ε ^ (-(2 * ν + 1 / M₈))) := by ring
      _ = N * c₁ * ε ^ t := by rw [this]
  have hlog : Real.log ε⁻¹ = -Real.log ε := Real.log_inv ε
  have hbound : ε ^ s * X ≤ 1 / (4 * Λ) := by
    rw [hsX]
    have hεt : 0 ≤ ε ^ t := Real.rpow_nonneg hε0.le t
    have h1 : N * c₁ * ε ^ t ≤ (c₄ * Real.log ε⁻¹ + 1) * c₁ * ε ^ t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNl hc₁) hεt
    have h2 : (c₄ * Real.log ε⁻¹ + 1) * c₁ * ε ^ t =
        c₁ * (c₄ * (-(Real.log ε * ε ^ t)) + ε ^ t) := by rw [hlog]; ring
    linarith
  have hgoal : (Λ * X)⁻¹ / 2 - g / X = (1 / (2 * Λ) - g) / X := by
    field_simp
  rw [hgoal, le_div_iff₀ hX0]
  have : 1 / (4 * Λ) ≤ 1 / (2 * Λ) - g := by
    have e : 1 / (2 * Λ) = 2 * (1 / (4 * Λ)) := by field_simp; ring
    linarith
  linarith

end LQGMetric.GM
