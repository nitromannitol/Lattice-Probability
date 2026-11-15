import LatticeProb.Prob.BrownianOpenExit
import Mathlib

/-! # Real-time endpoints of finite first-exit traces -/

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- A finite forward exit clock gives the infimum of the outside times after the root. -/
theorem sInf_outside_eq_forward_openExitTime {E : Type*} [TopologicalSpace E]
    (η : ℝ → E) (U : Set E) (t₀ : ℝ) (hη : Continuous η) (hU : IsOpen U)
    (hfin : openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) U () ≠ ⊤) :
    sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ U} =
      t₀ + ((openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) U ()).toNNReal : ℝ) := by
  let τ := openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) U ()
  have hout : η (t₀ + (τ.toNNReal : ℝ)) ∉ U :=
    openExitTime_not_mem (B := fun s (_ : Unit) => η (t₀ + (s : ℝ))) (ω := ())
      hU (hη.comp (continuous_const.add NNReal.continuous_coe)) hfin
  apply IsLeast.csInf_eq
  refine ⟨⟨?_, hout⟩, ?_⟩
  · change t₀ ≤ t₀ + (τ.toNNReal : ℝ)
    exact le_add_of_nonneg_right τ.toNNReal.coe_nonneg
  intro t ht
  let s : ℝ≥0 := ⟨t - t₀, sub_nonneg.mpr ht.1⟩
  have heq : t₀ + (s : ℝ) = t := by
    change t₀ + (t - t₀) = t
    ring
  have hs : η (t₀ + (s : ℝ)) ∉ U := by rw [heq]; exact ht.2
  have hle : τ ≤ (s : ℝ≥0∞) := openExitTime_le_of_not_mem hs
  have hle' : τ.toNNReal ≤ s :=
    (ENNReal.toNNReal_le_toNNReal hfin ENNReal.coe_ne_top).2 hle
  have hreal : (τ.toNNReal : ℝ) ≤ (s : ℝ) := hle'
  change (τ.toNNReal : ℝ) ≤ t - t₀ at hreal
  change t₀ + (τ.toNNReal : ℝ) ≤ t
  linarith

/-- A finite backward exit clock gives the supremum of the outside times before the root. -/
theorem sSup_outside_eq_backward_openExitTime {E : Type*} [TopologicalSpace E]
    (η : ℝ → E) (U : Set E) (t₀ : ℝ) (hη : Continuous η) (hU : IsOpen U)
    (hfin : openExitTime (fun s (_ : Unit) => η (t₀ - (s : ℝ))) U () ≠ ⊤) :
    sSup {t : ℝ | t ≤ t₀ ∧ η t ∉ U} =
      t₀ - ((openExitTime (fun s (_ : Unit) => η (t₀ - (s : ℝ))) U ()).toNNReal : ℝ) := by
  let τ := openExitTime (fun s (_ : Unit) => η (t₀ - (s : ℝ))) U ()
  have hout : η (t₀ - (τ.toNNReal : ℝ)) ∉ U :=
    openExitTime_not_mem (B := fun s (_ : Unit) => η (t₀ - (s : ℝ))) (ω := ())
      hU (hη.comp (continuous_const.sub NNReal.continuous_coe)) hfin
  apply IsGreatest.csSup_eq
  refine ⟨⟨?_, hout⟩, ?_⟩
  · change t₀ - (τ.toNNReal : ℝ) ≤ t₀
    exact sub_le_self _ τ.toNNReal.coe_nonneg
  intro t ht
  let s : ℝ≥0 := ⟨t₀ - t, sub_nonneg.mpr ht.1⟩
  have heq : t₀ - (s : ℝ) = t := by
    change t₀ - (t₀ - t) = t
    ring
  have hs : η (t₀ - (s : ℝ)) ∉ U := by rw [heq]; exact ht.2
  have hle : τ ≤ (s : ℝ≥0∞) := openExitTime_le_of_not_mem hs
  have hle' : τ.toNNReal ≤ s :=
    (ENNReal.toNNReal_le_toNNReal hfin ENNReal.coe_ne_top).2 hle
  have hreal : (τ.toNNReal : ℝ) ≤ (s : ℝ) := hle'
  change (τ.toNNReal : ℝ) ≤ t₀ - t at hreal
  change t ≤ t₀ - (τ.toNNReal : ℝ)
  linarith

end LatticeProb
