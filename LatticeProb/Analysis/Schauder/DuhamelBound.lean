import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.Heat.DuhamelBound`.

# A Duhamel-type bound from an integrable `t^{-1/2}` derivative bound

The one-variable step of the heat-kernel Hessian bound. A heat-kernel average `Φ(t)` has a
derivative bounded by `c / √t`, which is integrable at `0`, and `Φ(t) → L` as `t → 0⁺`. Then
`|Φ(1) - L| ≤ 2c`.

The proof does not integrate `Φ'` (no integrability of `Φ'` is assumed). Instead `Φ` is compared on
`[ε, 1]` with `G(t) = 2c√t`, whose derivative is `c / √t`: the functions `Φ + G` and `Φ - G` are
monotone and antitone respectively, so `|Φ(1) - Φ(ε)| ≤ G(1) - G(ε) ≤ 2c`, and the bound passes to
the limit `ε → 0⁺`.
-/

namespace LatticeProb.Analysis.Schauder

open Real Filter Topology Set

noncomputable section

/-- The function `t ↦ 2c√t` has derivative `c / √t` at every positive time. -/
theorem hasDerivAt_two_mul_mul_sqrt (c : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => 2 * c * Real.sqrt s) (c / Real.sqrt t) t := by
  have h := (Real.hasDerivAt_sqrt ht.ne').const_mul (2 * c)
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  refine h.congr_deriv ?_
  field_simp

/-- If `|Φ'| ≤ c / √t` on `[ε, 1]`, where `0 < ε ≤ 1`, then `Φ(ε) - Φ(1) ≤ 2c(1 - √ε)`; this
follows from the monotonicity of `Φ + 2c√t` on `[ε, 1]`. -/
theorem sub_le_of_hasDerivAt_le_div_sqrt_of_monotone {Φ Φ' : ℝ → ℝ} {c ε : ℝ}
    (hΦ : ∀ t, 0 < t → HasDerivAt Φ (Φ' t) t)
    (hΦ' : ∀ t, 0 < t → t ≤ 1 → |Φ' t| ≤ c / Real.sqrt t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Φ ε - Φ 1 ≤ 2 * c - 2 * c * Real.sqrt ε := by
  have hd : ∀ t, 0 < t →
      HasDerivAt (fun s => Φ s + 2 * c * Real.sqrt s) (Φ' t + c / Real.sqrt t) t :=
    fun t ht => (hΦ t ht).add (hasDerivAt_two_mul_mul_sqrt c ht)
  have hmono : MonotoneOn (fun s => Φ s + 2 * c * Real.sqrt s) (Icc ε 1) := by
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
  simp only [Real.sqrt_one, mul_one] at this
  linarith

/-- If `|Φ'| ≤ c / √t` on `[ε, 1]`, where `0 < ε ≤ 1`, then `Φ(1) - Φ(ε) ≤ 2c(1 - √ε)`; this
follows from the antitonicity of `Φ - 2c√t` on `[ε, 1]`. -/
theorem sub_le_of_hasDerivAt_le_div_sqrt_of_antitone {Φ Φ' : ℝ → ℝ} {c ε : ℝ}
    (hΦ : ∀ t, 0 < t → HasDerivAt Φ (Φ' t) t)
    (hΦ' : ∀ t, 0 < t → t ≤ 1 → |Φ' t| ≤ c / Real.sqrt t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Φ 1 - Φ ε ≤ 2 * c - 2 * c * Real.sqrt ε := by
  have hd : ∀ t, 0 < t →
      HasDerivAt (fun s => Φ s - 2 * c * Real.sqrt s) (Φ' t - c / Real.sqrt t) t :=
    fun t ht => (hΦ t ht).sub (hasDerivAt_two_mul_mul_sqrt c ht)
  have hanti : AntitoneOn (fun s => Φ s - 2 * c * Real.sqrt s) (Icc ε 1) := by
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
  simp only [Real.sqrt_one, mul_one] at this
  linarith

/-- **Duhamel-type bound.** If `Φ` is differentiable on `(0, ∞)` with `|Φ'(t)| ≤ c / √t` for
`0 < t ≤ 1` and `Φ(t) → L` as `t → 0⁺`, then `|Φ(1) - L| ≤ 2c`. No integrability of `Φ'` is
assumed: `Φ` is compared with `2c√t`. -/
theorem abs_sub_le_of_hasDerivAt_le_div_sqrt {Φ Φ' : ℝ → ℝ} {L c : ℝ}
    (hΦ : ∀ t, 0 < t → HasDerivAt Φ (Φ' t) t)
    (hΦ' : ∀ t, 0 < t → t ≤ 1 → |Φ' t| ≤ c / Real.sqrt t)
    (hlim : Tendsto Φ (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    |Φ 1 - L| ≤ 2 * c := by
  have hc : 0 ≤ c := by
    have h := hΦ' 1 one_pos le_rfl
    rw [Real.sqrt_one, div_one] at h
    exact (abs_nonneg _).trans h
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → |Φ 1 - Φ ε| ≤ 2 * c := by
    intro ε hε hε1
    have h1 := sub_le_of_hasDerivAt_le_div_sqrt_of_monotone hΦ hΦ' hε hε1
    have h2 := sub_le_of_hasDerivAt_le_div_sqrt_of_antitone hΦ hΦ' hε hε1
    have hs : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
    rw [abs_le]
    constructor <;> nlinarith
  have hT : Tendsto (fun ε => |Φ 1 - Φ ε|) (𝓝[>] (0 : ℝ)) (𝓝 |Φ 1 - L|) :=
    (continuous_abs.tendsto _).comp (hlim.const_sub (Φ 1))
  refine le_of_tendsto hT ?_
  filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
  exact key ε hε.1 hε.2

end

end LatticeProb.Analysis.Schauder
