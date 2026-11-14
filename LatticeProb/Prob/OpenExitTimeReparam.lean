import LatticeProb.Prob.BrownianOpenExit

/-! # Open-set exit under a change of clock -/

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- A continuous path's finite exit time transforms by the inverse clock. -/
theorem openExitTime_comp_orderIso_toNNReal {E : Type*} [TopologicalSpace E]
    (f : ℝ≥0 → E) (U : Set E) (φ : ℝ≥0 ≃o ℝ≥0)
    (hU : IsOpen U) (hf : Continuous f)
    (hfin : openExitTime (fun t (_ : Unit) => f t) U () ≠ ⊤) :
    (openExitTime (fun t (_ : Unit) => f (φ t)) U ()).toNNReal =
      φ.symm (openExitTime (fun t (_ : Unit) => f t) U ()).toNNReal := by
  let τ := openExitTime (fun t (_ : Unit) => f t) U ()
  let σ := openExitTime (fun t (_ : Unit) => f (φ t)) U ()
  have hout : f τ.toNNReal ∉ U := openExitTime_not_mem hU hf hfin
  have hsle : σ ≤ (φ.symm τ.toNNReal : ℝ≥0∞) := by
    apply openExitTime_le_of_not_mem
    simpa only [φ.apply_symm_apply] using hout
  have hsfin : σ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hsle
  have hsout : f (φ σ.toNNReal) ∉ U :=
    openExitTime_not_mem (B := fun t (_ : Unit) => f (φ t)) (ω := ())
      hU (hf.comp φ.continuous) hsfin
  have hτle : τ ≤ (φ σ.toNNReal : ℝ≥0∞) := openExitTime_le_of_not_mem hsout
  have h1 : σ.toNNReal ≤ φ.symm τ.toNNReal := ENNReal.toNNReal_le_toNNReal hsfin ENNReal.coe_ne_top |>.2 hsle
  have h2 : τ.toNNReal ≤ φ σ.toNNReal := ENNReal.toNNReal_le_toNNReal hfin ENNReal.coe_ne_top |>.2 hτle
  apply le_antisymm h1
  exact φ.symm_apply_le.mpr h2

/-- Oscillation between two finite exits is unchanged by an increasing clock. -/
theorem openExitTime_comp_orderIso_oscillation_iff {E : Type*} [PseudoMetricSpace E]
    (f : ℝ≥0 → E) (U V : Set E) (φ : ℝ≥0 ≃o ℝ≥0) (η : ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (hf : Continuous f)
    (hUfin : openExitTime (fun t (_ : Unit) => f t) U () ≠ ⊤)
    (hVfin : openExitTime (fun t (_ : Unit) => f t) V () ≠ ⊤) :
    (∀ s ∈ Icc (openExitTime (fun t (_ : Unit) => f (φ t)) U ()).toNNReal
        (openExitTime (fun t (_ : Unit) => f (φ t)) V ()).toNNReal,
      ∀ t ∈ Icc (openExitTime (fun t (_ : Unit) => f (φ t)) U ()).toNNReal
        (openExitTime (fun t (_ : Unit) => f (φ t)) V ()).toNNReal,
      dist (f (φ s)) (f (φ t)) ≤ η) ↔
    (∀ s ∈ Icc (openExitTime (fun t (_ : Unit) => f t) U ()).toNNReal
        (openExitTime (fun t (_ : Unit) => f t) V ()).toNNReal,
      ∀ t ∈ Icc (openExitTime (fun t (_ : Unit) => f t) U ()).toNNReal
        (openExitTime (fun t (_ : Unit) => f t) V ()).toNNReal,
      dist (f s) (f t) ≤ η) := by
  rw [openExitTime_comp_orderIso_toNNReal f U φ hU hf hUfin,
    openExitTime_comp_orderIso_toNNReal f V φ hV hf hVfin]
  constructor
  · intro h s hs t ht
    simpa only [φ.apply_symm_apply] using h (φ.symm s)
      ⟨φ.symm.monotone hs.1, φ.symm.monotone hs.2⟩ (φ.symm t)
      ⟨φ.symm.monotone ht.1, φ.symm.monotone ht.2⟩
  · intro h s hs t ht
    apply h (φ s) ?_ (φ t) ?_
    · constructor
      · simpa only [φ.apply_symm_apply] using φ.monotone hs.1
      · simpa only [φ.apply_symm_apply] using φ.monotone hs.2
    · constructor
      · simpa only [φ.apply_symm_apply] using φ.monotone ht.1
      · simpa only [φ.apply_symm_apply] using φ.monotone ht.2

end LatticeProb
