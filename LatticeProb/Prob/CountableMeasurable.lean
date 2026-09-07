/-
Measurability through a countable-valued observable.

Every process built by reading an instruction whose INDEX is itself random is
measurable for the same reason: the index takes countably many values, and on
each of them the process agrees with a measurable function.  The four lemmas
here are that reason, stated once.  They are what makes the odometer, the
arrival counts and the fields built from them measurable, and they need nothing
about the lattice.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open MeasureTheory

/-- If a countable-valued measurable observable decides which of a family of
measurable functions computes `f`, then `f` is measurable. -/
theorem measurable_of_countable_partition {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (r : α → γ) (hr : Measurable r) (f : α → β) (g : γ → α → β)
    (hg : ∀ c, Measurable (g c)) (h : ∀ a, f a = g (r a) a) : Measurable f := by
  intro S hS
  have key : f ⁻¹' S = ⋃ c : γ, (r ⁻¹' {c} ∩ g c ⁻¹' S) := by
    ext a
    simp [h a]
  rw [key]
  exact MeasurableSet.iUnion fun c => (hr (measurableSet_singleton c)).inter (hg c hS)

/-- Evaluating a measurable family at a measurable countable-valued index. -/
theorem measurable_eval_var {α : Type*} [MeasurableSpace α] {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] {X : Type*} [MeasurableSpace X]
    (q : α → ι) (hq : Measurable q) (f : α → ι → X)
    (hf : ∀ i, Measurable fun a => f a i) : Measurable fun a => f a (q a) :=
  measurable_of_countable_partition q hq _ (fun i a => f a i) hf fun _ => rfl

/-- Any map out of a countable space with measurable singletons is measurable. -/
theorem measurable_from_countable' {ι X : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace X] (g : ι → X) : Measurable g := by
  intro S _
  exact (Set.to_countable (g ⁻¹' S)).measurableSet

/-- A decidable relation between two countable-valued measurable observables. -/
theorem measurable_decide_rel {α : Type*} [MeasurableSpace α] {ι κ : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (f : α → ι) (g : α → κ) (hf : Measurable f) (hg : Measurable g)
    (R : ι → κ → Prop) [DecidableRel R] : Measurable fun a => decide (R (f a) (g a)) :=
  measurable_of_countable_partition f hf _ (fun c a => decide (R c (g a)))
    (fun c => (measurable_from_countable' (fun k => decide (R c k))).comp hg) fun _ => rfl

/-- Deciding a measurable predicate is measurable. -/
theorem measurable_decide {α : Type*} [MeasurableSpace α] (Q : α → Prop) [DecidablePred Q]
    (hQ : MeasurableSet {a | Q a}) : Measurable fun a => decide (Q a) := by
  refine measurable_to_countable' fun b => ?_
  cases b with
  | false =>
      have hpre : (fun a => decide (Q a)) ⁻¹' {false} = {a | Q a}ᶜ := by
        ext a
        simp
      rw [hpre]
      exact hQ.compl
  | true =>
      have hpre : (fun a => decide (Q a)) ⁻¹' {true} = {a | Q a} := by
        ext a
        simp
      rw [hpre]
      exact hQ

end LatticeProb
