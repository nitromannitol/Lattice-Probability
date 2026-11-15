import LatticeProb.Prob.AlternatingEntryExitClocks

/-! # Ordering and endpoints of exit clocks -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- An exit clock cannot precede its starting time. -/
theorem le_closedExitAfter {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    (U : Set (EuclideanSpace ℝ (Fin d))) (ω : Ω) :
    a ω ≤ closedExitAfter f a U ω := by
  classical
  by_cases ha : a ω = ⊤
  · simp [closedExitAfter, ha]
  · have hcoe (x : WithTop ℝ) (hx : x ≠ ⊤) :
        ((x.untopD 0 : ℝ) : WithTop ℝ) = x := by
      lift x to ℝ using hx
      rfl
    have heq := hcoe (a ω) ha
    let b := (a ω).untopD 0
    let τ := openExitTime (fun s (_ : Unit) => f ω (b + (s : ℝ))) U ()
    change a ω ≤ if a ω = ⊤ ∨ τ = ⊤ then ⊤
      else ((b + (τ.toNNReal : ℝ) : ℝ) : WithTop ℝ)
    by_cases hτ : τ = ⊤
    · simp [hτ]
    · simp only [ha, hτ, or_self, ↓reduceIte]
      rw [← heq]
      exact WithTop.coe_le_coe.mpr (le_add_of_nonneg_right τ.toNNReal.coe_nonneg)

/-- A finite exit from an open set is attained outside that set. -/
theorem closedExitAfter_not_mem {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (ω : Ω)
    (hfin : closedExitAfter f a U ω ≠ ⊤) :
    f ω ((closedExitAfter f a U ω).untopD 0) ∉ U := by
  classical
  let b := (a ω).untopD 0
  let τ := openExitTime (fun s (_ : Unit) => f ω (b + (s : ℝ))) U ()
  have hfin' : (if a ω = ⊤ ∨ τ = ⊤ then (⊤ : WithTop ℝ)
      else ((b + (τ.toNNReal : ℝ) : ℝ) : WithTop ℝ)) ≠ ⊤ := hfin
  have ha : a ω ≠ ⊤ := by
    intro h
    exact hfin' (by simp [h])
  have hτ : τ ≠ ⊤ := by
    intro h
    exact hfin' (by simp [h])
  have heq : closedExitAfter f a U ω = ((b + (τ.toNNReal : ℝ) : ℝ) : WithTop ℝ) := by
    change (if a ω = ⊤ ∨ τ = ⊤ then (⊤ : WithTop ℝ)
      else ((b + (τ.toNNReal : ℝ) : ℝ) : WithTop ℝ)) =
        ((b + (τ.toNNReal : ℝ) : ℝ) : WithTop ℝ)
    simp only [ha, hτ, or_self, ↓reduceIte]
  rw [heq]
  simp only [WithTop.untopD_coe]
  exact openExitTime_not_mem (B := fun s (_ : Unit) => f ω (b + (s : ℝ)))
    (ω := ()) hU ((f ω).continuous.comp
      (continuous_const.add NNReal.continuous_coe)) hτ

end LatticeProb
