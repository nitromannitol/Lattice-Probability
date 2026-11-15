import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.LeftRightNhds

/-! # Power bounds from a ray asymptotic -/

set_option autoImplicit false

open Filter Set Asymptotics
open scoped Topology

namespace LatticeProb

/-- An asymptotic equivalent to a positive multiple of a power yields
positive two-sided power bounds on a sufficiently small right neighborhood. -/
theorem exists_power_bounds_of_isEquivalent {f : ℝ → ℝ} {c p : ℝ}
    (hc : 0 < c)
    (h : f ~[(𝓝[>] (0 : ℝ))] (fun r => c * r ^ p)) :
    ∃ a b δ : ℝ, 0 < a ∧ 0 < b ∧ 0 < δ ∧
      ∀ r, 0 < r → r < δ → a * r ^ p ≤ f r ∧ f r ≤ b * r ^ p := by
  obtain ⟨A, hA, hupper⟩ := isBigO_iff'.1 h.isBigO
  obtain ⟨D, hD, hlower⟩ := isBigO_iff'.1 h.isBigO_symm
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < f r := h.eventually_pos (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos hc (Real.rpow_pos_of_pos hr _))
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (inter_mem (inter_mem hupper hlower) hpos)
  refine ⟨c / D, A * c, δ, div_pos hc hD, mul_pos hA hc, hδ, ?_⟩
  intro r hr hrδ
  obtain ⟨⟨hu, hl⟩, hf⟩ := hbound ⟨hr, hrδ⟩
  change ‖f r‖ ≤ A * ‖c * r ^ p‖ at hu
  change ‖c * r ^ p‖ ≤ D * ‖f r‖ at hl
  change 0 < f r at hf
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr _
  have hcr : 0 < c * r ^ p := mul_pos hc hrp
  simp only [Real.norm_eq_abs, abs_of_pos hcr, abs_of_pos hf] at hu hl
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    nlinarith
  · nlinarith

end LatticeProb
