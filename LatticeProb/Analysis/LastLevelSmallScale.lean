import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! # Small levels of a continuous path -/

open Filter Set Topology

namespace LatticeProb

/-- The last time a continuous path hits a level tends to negative infinity
as the level tends to negative infinity, when its two tails have opposite limits. -/
theorem tendsto_sSup_level_atBot {f : ℝ → ℝ} (hf : Continuous f)
    (hleft : Tendsto f atBot atBot) (hright : Tendsto f atTop atTop) :
    Tendsto (fun y => sSup {x | f x = y}) atBot atBot := by
  rw [tendsto_atBot_atBot]
  intro a
  obtain ⟨b, hb⟩ := (tendsto_atTop_atTop.mp hright) 0
  obtain ⟨c, hc⟩ := (isCompact_Icc.bddBelow_image hf.continuousOn :
    BddBelow (f '' Icc a (max a b)))
  refine ⟨min c 0 - 1, fun y hy => ?_⟩
  have hne : {x | f x = y}.Nonempty := by
    obtain ⟨u, hu⟩ := (tendsto_atBot_atBot.mp hleft) y
    obtain ⟨v, hv⟩ := (tendsto_atTop_atTop.mp hright) y
    obtain ⟨x, hx⟩ := intermediate_value_univ u v hf ⟨hu u le_rfl, hv v le_rfl⟩
    exact ⟨x, hx⟩
  apply csSup_le hne
  intro x hx
  by_contra hxa
  have hax : a < x := lt_of_not_ge hxa
  have hbound : min c 0 ≤ f x := by
    by_cases hxb : x ≤ max a b
    · exact (min_le_left _ _).trans (hc ⟨x, ⟨hax.le, hxb⟩, rfl⟩)
    · exact (min_le_right _ _).trans (hb x (le_trans (le_max_right _ _) (le_of_not_ge hxb)))
  change f x = y at hx
  rw [hx] at hbound
  linarith

/-- Exponentiating the last-level time gives a positive scale tending to zero. -/
theorem tendsto_exp_sSup_level_atBot {f : ℝ → ℝ} (hf : Continuous f)
    (hleft : Tendsto f atBot atBot) (hright : Tendsto f atTop atTop) :
    Tendsto (fun y => Real.exp (sSup {x | f x = y})) atBot (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_sSup_level_atBot hf hleft hright)

end LatticeProb
