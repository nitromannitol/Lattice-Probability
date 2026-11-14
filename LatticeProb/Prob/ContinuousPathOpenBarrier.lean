/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib

/-!
# Measurability of weak barriers for continuous paths

A weak lower barrier on an open interval is determined by rational times.
-/

open Set MeasureTheory

namespace LatticeProb

/-- For continuous real paths, a weak lower barrier on an open interval is a
measurable event whenever the time evaluations and barrier are measurable. -/
theorem measurableSet_continuousPath_openBarrier {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ → ℝ) (Y : Ω → ℝ) (a b : ℝ)
    (hcont : ∀ ω, Continuous (X ω))
    (hX : ∀ t, Measurable (fun ω => X ω t)) (hY : Measurable Y) :
    MeasurableSet {ω | ∀ t ∈ Ioo a b, Y ω ≤ X ω t} := by
  have heq : {ω | ∀ t ∈ Ioo a b, Y ω ≤ X ω t} =
      {ω | ∀ q : ℚ, (q : ℝ) ∈ Ioo a b → Y ω ≤ X ω q} := by
    ext ω
    constructor
    · intro h q hq
      exact h q hq
    · intro h t ht
      by_contra hfail
      have hlt : X ω t < Y ω := lt_of_not_ge hfail
      have hopen : IsOpen (Ioo a b ∩ {s | X ω s < Y ω}) :=
        isOpen_Ioo.inter (isOpen_lt (hcont ω) continuous_const)
      obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hopen ⟨t, ht, hlt⟩
      exact (not_le_of_gt hq.2) (h q hq.1)
  rw [heq]
  exact measurableSet_setOfPred.2 (Measurable.forall fun q : ℚ =>
    measurable_const.imp (measurableSet_setOfPred.1 (measurableSet_le hY (hX q))))

end LatticeProb
