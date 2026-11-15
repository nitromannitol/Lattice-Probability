import LatticeProb.Prob.OpenEntryTime

/-! # Open-set hitting times after extended-real starting times -/

set_option autoImplicit false

open Set MeasureTheory Classical

namespace LatticeProb

/-- The first entry into an open set after a measurable extended-real time is
measurable. An infinite starting time and the absence of an entry both give `⊤`. -/
theorem measurable_open_hittingAfter_top {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : Ω → ℝ → E) (a : Ω → WithTop ℝ) {U : Set E} (hU : IsOpen U)
    (hf : ∀ ω, Continuous (f ω)) (hm : ∀ q : ℚ, Measurable fun ω => f ω q)
    (ha : Measurable a) :
    Measurable fun ω => if a ω = ⊤ then ⊤ else
      hittingAfter (fun t ω => f ω t) U ((a ω).untopD 0) ω := by
  have hs : MeasurableSet {ω | a ω = ⊤} :=
    measurableSet_eq_fun ha measurable_const
  exact Measurable.ite hs measurable_const
    (measurable_open_hittingAfter f (fun ω => (a ω).untopD 0) hU hf hm
      (ha.untopD 0))

end LatticeProb
