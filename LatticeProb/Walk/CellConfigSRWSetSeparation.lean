import LatticeProb.Walk.CellConfigSRWChain

/-!
# Hitting distributions and separation of a set of cells

For simple random walks on a cell configuration, a walk that separates a set of cells from a
hitting set controls the hitting distributions from every cell in that set. This is the set form
of the separation estimate used in Gwynne–Miller–Sheffield, Lemmas 3.12 and 3.14
(arXiv:1807.07515).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open ReflectedGMS.GMS MatedCRTHarmonic.Markov MatedCRTHarmonic.HarmonicInfinity

namespace LatticeProb.CellConfigSRW

variable (H : CellConfig) [Countable H.cells]

omit [Countable H.cells] in
/-- Separation of a set implies separation of each of its members. -/
theorem graphSeparates_singleton_of_mem {U B I : Set H.cells} {y : H.cells}
    (hy : y ∈ B) (h : GraphSeparates H.graph U B I) :
    GraphSeparates H.graph U {y} I := by
  intro a ha b hb w
  have hay : a = y := mem_singleton_iff.mp ha
  subst a
  exact h y hy b hb w

/-- The hitting-distribution bound with separation of a set of starting cells. -/
theorem abs_hit_sub_le_of_set_separation (hH : H.IsCellConfiguration) (I W B : Set H.cells) {x y : H.cells}
    {Qx Qy : Measure (ℕ → H.cells)} (hQx : H.IsSRWLaw x Qx) (hQy : H.IsSRWLaw y Qy)
    (hyB : y ∈ B) (hx : Qx {ω | hitTime I ω ≠ ⊤} = 1)
    (hy : Qy {ω | hitTime I ω ≠ ⊤} = 1) :
    |(Qx (hitEvent I W)).toReal - (Qy (hitEvent I W)).toReal| ≤
      1 - (Qx {ω | GraphSeparates H.graph (traceBefore id I ω) B I}).toReal := by
  let : IsProbabilityMeasure Qx := hQx.1
  refine (abs_hit_sub_le_of_isSRWLaw H hH I W hQx hQy hx hy).trans ?_
  apply sub_le_sub_left
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono fun _ hw => graphSeparates_singleton_of_mem H hyB hw

/-- A lower bound on the probability of set separation gives a uniform hitting-law estimate. -/
theorem abs_hit_sub_le_of_set_separation_prob (hH : H.IsCellConfiguration) (I W B : Set H.cells) {x y : H.cells} {δ : ℝ}
    {Qx Qy : Measure (ℕ → H.cells)} (hQx : H.IsSRWLaw x Qx) (hQy : H.IsSRWLaw y Qy)
    (hyB : y ∈ B) (hD : 1 - δ ≤
      (Qx {ω | GraphSeparates H.graph (traceBefore id I ω) B I}).toReal)
    (hx : Qx {ω | hitTime I ω ≠ ⊤} = 1) (hy : Qy {ω | hitTime I ω ≠ ⊤} = 1) :
    |(Qx (hitEvent I W)).toReal - (Qy (hitEvent I W)).toReal| ≤ δ := by
  have h := abs_hit_sub_le_of_set_separation H hH I W B hQx hQy hyB hx hy
  linarith

end LatticeProb.CellConfigSRW

end
