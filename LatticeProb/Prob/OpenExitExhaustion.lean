import LatticeProb.Prob.BallExitRadius
import LatticeProb.Prob.BrownianOpenExitStopping
import Mathlib.Topology.Order.MonotoneConvergence

/-! # First exits under increasing open exhaustion -/

set_option autoImplicit false

open Set Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- First exit times from increasing open sets converge to the finite first exit
from their union. -/
theorem tendsto_openExitTime_of_iUnion {Ω E : Type*} [TopologicalSpace E]
    {B : ℝ≥0 → Ω → E} {ω : Ω} {U : ℕ → Set E}
    (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hcont : Continuous fun t => B t ω)
    (hfin : openExitTime B (⋃ n, U n) ω ≠ ∞) :
    Tendsto (fun n => openExitTime B (U n) ω) atTop
      (𝓝 (openExitTime B (⋃ n, U n) ω)) := by
  let τ := openExitTime B (⋃ n, U n) ω
  have hτfin : τ ≠ ∞ := hfin
  let σ : ℕ → ℝ≥0∞ := fun n => openExitTime B (U n) ω
  have hσmono : Monotone σ := fun i j hij =>
    openExitTime_mono_set B ω (hmono hij)
  have hσle : ∀ n, σ n ≤ τ := fun n =>
    openExitTime_mono_set B ω (subset_iUnion U n)
  have hsup_le : (⨆ n, σ n) ≤ τ := iSup_le hσle
  have hsup_fin : (⨆ n, σ n) ≠ ∞ := ne_top_of_le_ne_top hτfin hsup_le
  have hτle : τ ≤ ⨆ n, σ n := by
    by_contra hn
    have hlt : (⨆ n, σ n) < τ := lt_of_not_ge hn
    have hlt' : (⨆ n, σ n).toNNReal < τ.toNNReal := by
      rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hsup_fin,
        ENNReal.coe_toNNReal hτfin]
      exact hlt
    obtain ⟨t, hst, htτ⟩ := exists_between hlt'
    have htτ' : (t : ℝ≥0∞) < τ := by
      rw [← ENNReal.coe_toNNReal hτfin]
      exact ENNReal.coe_lt_coe.mpr htτ
    have hcover : (fun s => B s ω) '' Icc (0 : ℝ≥0) t ⊆ ⋃ n, U n := by
      rintro _ ⟨s, hs, rfl⟩
      exact mem_of_lt_openExitTime ((ENNReal.coe_le_coe.mpr hs.2).trans_lt htτ')
    obtain ⟨n, hn⟩ := (isCompact_Icc.image hcont).elim_directed_cover U hU hcover
      (fun i j => ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩)
    have hmaps : MapsTo (fun s => B s ω) (Icc 0 t) (U n) := fun s hs => hn ⟨s, hs, rfl⟩
    have htσ : (t : ℝ≥0∞) < σ n :=
      lt_of_not_ge (fun h => (openExitTime_le_iff_not_mapsTo (hU n) hcont t).mp h hmaps)
    have : (t : ℝ≥0∞) ≤ ⨆ n, σ n := htσ.le.trans (le_iSup σ n)
    have : t ≤ (⨆ n, σ n).toNNReal := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hsup_fin]
      exact this
    exact (not_le_of_gt hst) this
  have heq : (⨆ n, σ n) = τ := le_antisymm hsup_le hτle
  simpa only [heq] using tendsto_atTop_iSup hσmono

/-- Along an increasing open exhaustion, a continuous path's finite exit
positions converge to its exit position from the union. -/
theorem tendsto_openExitPosition_of_iUnion {Ω E : Type*} [TopologicalSpace E]
    {B : ℝ≥0 → Ω → E} {ω : Ω} {U : ℕ → Set E}
    (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hcont : Continuous fun t => B t ω)
    (hfin : openExitTime B (⋃ n, U n) ω ≠ ∞) :
    Tendsto (fun n => B (openExitTime B (U n) ω).toNNReal ω) atTop
      (𝓝 (B (openExitTime B (⋃ n, U n) ω).toNNReal ω)) :=
  (hcont.tendsto _).comp ((ENNReal.tendsto_toNNReal hfin).comp
    (tendsto_openExitTime_of_iUnion hU hmono hcont hfin))

end LatticeProb
