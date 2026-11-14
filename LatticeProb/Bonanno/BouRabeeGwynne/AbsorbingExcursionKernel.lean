/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.AbsorbingExcursionKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! A common measurable selector for whole excursions, with a permanent
termination flag. The state space may retain an integer clock and all vertices,
or a genuine normalized Brownian excursion. -/

open MeasureTheory ProbabilityTheory Set

namespace BouRabeeGwynne

variable {X S J : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

/-- A selected excursion starts actively when a ball is selected, and becomes
a constant terminated excursion when the selector returns `none`. -/
noncomputable def selectedExcursionKernel (κ : J → Kernel X S)
    (constantState : X → S) (hconstant : Measurable constantState) :
    Kernel (Option J × X) (Bool × S) where
  toFun p := match p.1 with
    | none => Measure.dirac (true, constantState p.2)
    | some j => (κ j p.2).map (fun s => (false, s))
  measurable' := by
    apply measurable_from_prod_countable_right
    intro j
    cases j with
    | none => exact Measure.measurable_dirac.comp (measurable_const.prodMk hconstant)
    | some j =>
      exact ((κ j).mapOfMeasurable (fun s => (false, s))
        (measurable_const.prodMk measurable_id)).measurable

@[simp] lemma selectedExcursionKernel_none (κ : J → Kernel X S)
    (constantState : X → S) (hconstant : Measurable constantState) (x : X) :
    selectedExcursionKernel κ constantState hconstant (none, x) =
      Measure.dirac (true, constantState x) := rfl

@[simp] lemma selectedExcursionKernel_some (κ : J → Kernel X S)
    (constantState : X → S) (hconstant : Measurable constantState) (j : J) (x : X) :
    selectedExcursionKernel κ constantState hconstant (some j, x) =
      (κ j x).map (fun s => (false, s)) := rfl

instance selectedExcursionKernel_isMarkov (κ : J → Kernel X S)
    [∀ j, IsMarkovKernel (κ j)] (constantState : X → S)
    (hconstant : Measurable constantState) :
    IsMarkovKernel (selectedExcursionKernel κ constantState hconstant) where
  isProbabilityMeasure p := by
    rcases p with ⟨j, x⟩
    cases j with
    | none => rw [selectedExcursionKernel_none]; infer_instance
    | some j =>
      rw [selectedExcursionKernel_some]
      exact (Measure.isProbabilityMeasure_map_iff
        (measurable_const.prodMk measurable_id).aemeasurable).mpr inferInstance

/-- A terminated history stays terminated independently of every later stage's
selector. An active history selects its next genuine whole excursion using its
own endpoint. -/
noncomputable def absorbingExcursionKernel (κ : J → Kernel X S)
    (endPoint : S → X) (hend : Measurable endPoint)
    (constantState : X → S) (hconstant : Measurable constantState)
    (selector : X → Option J) (hselector : Measurable selector) :
    Kernel (Bool × S) (Bool × S) where
  toFun p := if p.1 then Measure.dirac (true, constantState (endPoint p.2)) else
    selectedExcursionKernel κ constantState hconstant (selector (endPoint p.2), endPoint p.2)
  measurable' := by
    apply measurable_from_prod_countable_right
    intro b
    cases b with
    | false =>
      exact (selectedExcursionKernel κ constantState hconstant).measurable.comp
        ((hselector.comp hend).prodMk hend)
    | true =>
      exact Measure.measurable_dirac.comp (measurable_const.prodMk (hconstant.comp hend))

@[simp] lemma absorbingExcursionKernel_true (κ : J → Kernel X S)
    (endPoint : S → X) (hend : Measurable endPoint)
    (constantState : X → S) (hconstant : Measurable constantState)
    (selector : X → Option J) (hselector : Measurable selector) (s : S) :
    absorbingExcursionKernel κ endPoint hend constantState hconstant selector hselector
      (true, s) = Measure.dirac (true, constantState (endPoint s)) := rfl

lemma absorbingExcursionKernel_false_none (κ : J → Kernel X S)
    (endPoint : S → X) (hend : Measurable endPoint)
    (constantState : X → S) (hconstant : Measurable constantState)
    (selector : X → Option J) (hselector : Measurable selector) (s : S)
    (hs : selector (endPoint s) = none) :
    absorbingExcursionKernel κ endPoint hend constantState hconstant selector hselector
      (false, s) = Measure.dirac (true, constantState (endPoint s)) := by
  change selectedExcursionKernel κ constantState hconstant
    (selector (endPoint s), endPoint s) = _
  rw [hs, selectedExcursionKernel_none]

lemma absorbingExcursionKernel_false_some (κ : J → Kernel X S)
    (endPoint : S → X) (hend : Measurable endPoint)
    (constantState : X → S) (hconstant : Measurable constantState)
    (selector : X → Option J) (hselector : Measurable selector) (s : S) (j : J)
    (hs : selector (endPoint s) = some j) :
    absorbingExcursionKernel κ endPoint hend constantState hconstant selector hselector
      (false, s) = (κ j (endPoint s)).map (fun e => (false, e)) := by
  change selectedExcursionKernel κ constantState hconstant
    (selector (endPoint s), endPoint s) = _
  rw [hs, selectedExcursionKernel_some]

instance absorbingExcursionKernel_isMarkov (κ : J → Kernel X S)
    [∀ j, IsMarkovKernel (κ j)]
    (endPoint : S → X) (hend : Measurable endPoint)
    (constantState : X → S) (hconstant : Measurable constantState)
    (selector : X → Option J) (hselector : Measurable selector) :
    IsMarkovKernel (absorbingExcursionKernel κ endPoint hend constantState hconstant
      selector hselector) where
  isProbabilityMeasure p := by
    rcases p with ⟨b, s⟩
    cases b with
    | true => rw [absorbingExcursionKernel_true]; infer_instance
    | false =>
      change IsProbabilityMeasure (selectedExcursionKernel κ constantState hconstant
        (selector (endPoint s), endPoint s))
      infer_instance

lemma absorbingExcursionKernel_ae_start [MeasurableSingletonClass X] (κ : J → Kernel X S)
    (endPoint : S → X) (hend : Measurable endPoint)
    (constantState : X → S) (hconstant : Measurable constantState)
    (selector : X → Option J) (hselector : Measurable selector)
    (start : S → X) (hstart_m : Measurable start)
    (hstart : ∀ j x, ∀ᵐ s ∂κ j x, start s = x)
    (hconst : ∀ x, start (constantState x) = x) (p : Bool × S) :
    ∀ᵐ q ∂absorbingExcursionKernel κ endPoint hend constantState hconstant
      selector hselector p, start q.2 = endPoint p.2 := by
  rcases p with ⟨b, s⟩
  have hm : MeasurableSet {q : Bool × S | start q.2 = endPoint s} :=
    (hstart_m.comp measurable_snd) (measurableSet_singleton _)
  cases b with
  | true =>
    rw [absorbingExcursionKernel_true]
    exact (ae_dirac_iff hm).mpr (hconst _)
  | false =>
    cases hs : selector (endPoint s) with
    | none =>
      rw [absorbingExcursionKernel_false_none κ endPoint hend constantState hconstant
        selector hselector s hs]
      exact (ae_dirac_iff hm).mpr (hconst _)
    | some j =>
      rw [absorbingExcursionKernel_false_some κ endPoint hend constantState hconstant
        selector hselector s j hs]
      exact (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hm).mpr
        (hstart j (endPoint s))

end BouRabeeGwynne
