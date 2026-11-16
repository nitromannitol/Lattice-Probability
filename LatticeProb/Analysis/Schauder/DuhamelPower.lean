import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A Duhamel-type bound from an integrable `t^{β-1}` derivative bound

The one-variable step of the heat-kernel Hölder estimates. A heat-kernel average `Φ(t)` has a
derivative bounded by `c t^{β-1}` with `β > 0`, which is integrable at `0`, and `Φ(t) → L` as
`t → 0⁺`. Then `|Φ(1) - L| ≤ c / β`. The case `β = 1/2` is the bound by `2c` of the `t^{-1/2}`
derivative estimate.

The proof does not integrate `Φ'` (no integrability of `Φ'` is assumed). Instead `Φ` is compared on
`[ε, 1]` with `G(t) = (c / β) t^β`, whose derivative is `c t^{β-1}`: the functions `Φ + G` and
`Φ - G` are monotone and antitone respectively, so
`|Φ(1) - Φ(ε)| ≤ G(1) - G(ε) ≤ c / β`, and the bound passes to the limit `ε → 0⁺`.
-/

namespace LatticeProb.Analysis.Schauder

open Real Filter Topology Set

noncomputable section

/-- The function `t ↦ (c / β) t^β` has derivative `c t^{β-1}` at every positive time, for
`β ≠ 0`. -/
theorem hasDerivAt_div_mul_rpow (c : ℝ) {β : ℝ} (hβ : β ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => c / β * s ^ β) (c * t ^ (β - 1)) t := by
  have h := (Real.hasDerivAt_rpow_const (p := β) (Or.inl ht.ne')).const_mul (c / β)
  refine h.congr_deriv ?_
  field_simp

/-- If `|Φ'(t)| ≤ c t^{β-1}` on `[ε, 1]`, where `0 < ε ≤ 1`, then
`Φ(ε) - Φ(1) ≤ (c / β)(1 - ε^β)`; this follows from the monotonicity of `Φ + (c / β) t^β` on
`[ε, 1]`. -/
theorem sub_le_of_hasDerivAt_le_rpow_of_monotone {Φ Φ' : ℝ → ℝ} {c β ε : ℝ} (hβ : 0 < β)
    (hΦ : ∀ t, 0 < t → HasDerivAt Φ (Φ' t) t)
    (hΦ' : ∀ t, 0 < t → t ≤ 1 → |Φ' t| ≤ c * t ^ (β - 1)) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Φ ε - Φ 1 ≤ c / β - c / β * ε ^ β := by
  have hd : ∀ t, 0 < t →
      HasDerivAt (fun s => Φ s + c / β * s ^ β) (Φ' t + c * t ^ (β - 1)) t :=
    fun t ht => (hΦ t ht).add (hasDerivAt_div_mul_rpow c hβ.ne' ht)
  have hmono : MonotoneOn (fun s => Φ s + c / β * s ^ β) (Icc ε 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc ε 1)
    · intro t ht
      exact (hd t (hε.trans_le ht.1)).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro t ht
      exact (hd t (hε.trans ht.1)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have ht0 : 0 < t := hε.trans ht.1
      rw [(hd t ht0).deriv]
      have := (abs_le.1 (hΦ' t ht0 ht.2.le)).1
      linarith
  have := hmono ⟨le_rfl, hε1⟩ ⟨hε1, le_rfl⟩ hε1
  simp only [Real.one_rpow, mul_one] at this
  linarith

/-- If `|Φ'(t)| ≤ c t^{β-1}` on `[ε, 1]`, where `0 < ε ≤ 1`, then
`Φ(1) - Φ(ε) ≤ (c / β)(1 - ε^β)`; this follows from the antitonicity of `Φ - (c / β) t^β` on
`[ε, 1]`. -/
theorem sub_le_of_hasDerivAt_le_rpow_of_antitone {Φ Φ' : ℝ → ℝ} {c β ε : ℝ} (hβ : 0 < β)
    (hΦ : ∀ t, 0 < t → HasDerivAt Φ (Φ' t) t)
    (hΦ' : ∀ t, 0 < t → t ≤ 1 → |Φ' t| ≤ c * t ^ (β - 1)) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Φ 1 - Φ ε ≤ c / β - c / β * ε ^ β := by
  have hd : ∀ t, 0 < t →
      HasDerivAt (fun s => Φ s - c / β * s ^ β) (Φ' t - c * t ^ (β - 1)) t :=
    fun t ht => (hΦ t ht).sub (hasDerivAt_div_mul_rpow c hβ.ne' ht)
  have hanti : AntitoneOn (fun s => Φ s - c / β * s ^ β) (Icc ε 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ε 1)
    · intro t ht
      exact (hd t (hε.trans_le ht.1)).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro t ht
      exact (hd t (hε.trans ht.1)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have ht0 : 0 < t := hε.trans ht.1
      rw [(hd t ht0).deriv]
      have := (abs_le.1 (hΦ' t ht0 ht.2.le)).2
      linarith
  have := hanti ⟨le_rfl, hε1⟩ ⟨hε1, le_rfl⟩ hε1
  simp only [Real.one_rpow, mul_one] at this
  linarith

/-- **Duhamel-type bound.** If `Φ` is differentiable on `(0, ∞)` with `|Φ'(t)| ≤ c t^{β-1}` for
`0 < t ≤ 1`, where `β > 0`, and `Φ(t) → L` as `t → 0⁺`, then `|Φ(1) - L| ≤ c / β`. No
integrability of `Φ'` is assumed: `Φ` is compared with `(c / β) t^β`. -/
theorem abs_sub_le_of_hasDerivAt_le_rpow {Φ Φ' : ℝ → ℝ} {L c β : ℝ} (hβ : 0 < β)
    (hΦ : ∀ t, 0 < t → HasDerivAt Φ (Φ' t) t)
    (hΦ' : ∀ t, 0 < t → t ≤ 1 → |Φ' t| ≤ c * t ^ (β - 1))
    (hlim : Tendsto Φ (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    |Φ 1 - L| ≤ c / β := by
  have hc : 0 ≤ c := by
    have h := hΦ' 1 one_pos le_rfl
    rw [Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → |Φ 1 - Φ ε| ≤ c / β := by
    intro ε hε hε1
    have h1 := sub_le_of_hasDerivAt_le_rpow_of_monotone hβ hΦ hΦ' hε hε1
    have h2 := sub_le_of_hasDerivAt_le_rpow_of_antitone hβ hΦ hΦ' hε hε1
    have hp : 0 ≤ c / β * ε ^ β := mul_nonneg (div_nonneg hc hβ.le) (Real.rpow_nonneg hε.le β)
    rw [abs_le]
    constructor <;> linarith
  have hT : Tendsto (fun ε => |Φ 1 - Φ ε|) (𝓝[>] (0 : ℝ)) (𝓝 |Φ 1 - L|) :=
    (continuous_abs.tendsto _).comp (hlim.const_sub (Φ 1))
  refine le_of_tendsto hT ?_
  filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
  exact key ε hε.1 hε.2

end

end LatticeProb.Analysis.Schauder
