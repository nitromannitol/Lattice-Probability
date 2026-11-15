import LatticeProb.Prob.BrownianOpenExitStopping
import LatticeProb.Topology.RealFirstExitClock
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-! # Exit times after extended-real starting times -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- The first time after an extended-real starting time at which a continuous
path is outside an open set. No exit and an infinite starting time give `⊤`. -/
noncomputable def closedExitAfter {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    (U : Set (EuclideanSpace ℝ (Fin d))) (ω : Ω) : WithTop ℝ :=
  let b := (a ω).untopD 0
  let τ := openExitTime (fun s (_ : Unit) => f ω (b + (s : ℝ))) U ()
  if a ω = ⊤ ∨ τ = ⊤ then ⊤ else ((b + (τ.toNNReal : ℝ) : ℝ) : WithTop ℝ)

/-- Exit after a measurable extended-real starting time is measurable. -/
theorem measurable_closedExitAfter {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hf : Measurable f) (ha : Measurable a) :
    Measurable (closedExitAfter f a U) := by
  classical
  let b : Ω → ℝ := fun ω => (a ω).untopD 0
  let B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d) := fun s ω => f ω (b ω + (s : ℝ))
  have hb : Measurable b := ha.untopD 0
  have hm : ∀ s, StronglyMeasurable (B s) := by
    intro s
    apply Measurable.stronglyMeasurable
    exact continuous_eval.measurable.comp (hf.prodMk (hb.add measurable_const))
  have hc : ∀ ω, Continuous fun s => B s ω := by
    intro ω
    exact (f ω).continuous.comp (continuous_const.add NNReal.continuous_coe)
  let τ : Ω → ℝ≥0∞ := fun ω =>
    openExitTime (fun s (_ : Unit) => f ω (b ω + (s : ℝ))) U ()
  have hτ : Measurable τ := by
    convert measurable_openExitTime hm hc hU using 1
    funext ω
    rfl
  have hs : MeasurableSet {ω | a ω = ⊤ ∨ τ ω = ⊤} :=
    (measurableSet_eq_fun ha measurable_const).union
      (measurableSet_eq_fun hτ measurable_const)
  have hval : Measurable (fun ω => ((b ω + (τ ω).toNNReal : ℝ) : WithTop ℝ)) :=
    (hb.add (NNReal.continuous_coe.measurable.comp hτ.ennreal_toNNReal)).withTop_coe
  have hh : Measurable (fun ω => if a ω = ⊤ ∨ τ ω = ⊤ then (⊤ : WithTop ℝ)
      else ((b ω + (τ ω).toNNReal : ℝ) : WithTop ℝ)) :=
    Measurable.ite hs measurable_const hval
  change Measurable (fun ω => closedExitAfter f a U ω)
  simpa only [closedExitAfter, b, τ] using hh

/-- A finite exit is the infimum of the outside times after the starting time. -/
theorem closedExitAfter_eq_sInf {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (ω : Ω) (t : ℝ)
    (ha : a ω = (t : WithTop ℝ))
    (hfin : openExitTime (fun s (_ : Unit) => f ω (t + (s : ℝ))) U () ≠ ⊤) :
    closedExitAfter f a U ω =
      ((sInf {s : ℝ | t ≤ s ∧ f ω s ∉ U} : ℝ) : WithTop ℝ) := by
  rw [sInf_outside_eq_forward_openExitTime (f ω) U t (f ω).continuous hU hfin]
  simp [closedExitAfter, ha, hfin]

end LatticeProb
