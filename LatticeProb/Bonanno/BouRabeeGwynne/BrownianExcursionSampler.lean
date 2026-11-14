/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianExcursionSampler at commit fdb5cad; local import paths and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.AbsorbingExcursionKernel
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionKernel

/-! Actual full-excursion sampling from a fresh continuous Brownian path.
The permanent termination flag is retained, and the sampled laws agree exactly
with the shared selected and absorbing excursion kernels. -/

open MeasureTheory ProbabilityTheory Set

namespace BouRabeeGwynne

set_option linter.unusedSectionVars false

variable {d : ℕ} {J : Type*}

private lemma measurable_constantBrownianExcursion :
    Measurable (fun z : Euc d => ContinuousMap.const unitInterval z) :=
  ContinuousMap.measurable_iff_eval.mpr (fun _ => measurable_id)

/-- Sample the selected genuine excursion; no selection gives a terminated
constant excursion at the supplied starting point. -/
noncomputable def selectedBrownianExcursionSampler (U : J → Set (Euc d))
    (p : Option J × Euc d) (ω : BrownianPath d) : Bool × C(unitInterval, Euc d) :=
  match p.1 with
  | none => (true, ContinuousMap.const unitInterval p.2)
  | some j => (false, stoppedBrownianRepresentative (U j) p.2 ω)

@[simp] lemma selectedBrownianExcursionSampler_none (U : J → Set (Euc d))
    (x : Euc d) (ω : BrownianPath d) :
    selectedBrownianExcursionSampler U (none, x) ω =
      (true, ContinuousMap.const unitInterval x) := rfl

@[simp] lemma selectedBrownianExcursionSampler_some (U : J → Set (Euc d))
    (j : J) (x : Euc d) (ω : BrownianPath d) :
    selectedBrownianExcursionSampler U (some j, x) ω =
      (false, stoppedBrownianRepresentative (U j) x ω) := rfl

variable [Countable J] [MeasurableSpace (Option J)]
  [MeasurableSingletonClass (Option J)]

lemma measurable_selectedBrownianExcursionSampler_joint (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) :
    Measurable (fun p : (Option J × Euc d) × BrownianPath d =>
      selectedBrownianExcursionSampler U p.1 p.2) := by
  have hm : Measurable (fun p : Option J × (Euc d × BrownianPath d) =>
      selectedBrownianExcursionSampler U (p.1, p.2.1) p.2.2) := by
    apply measurable_from_prod_countable_right
    intro j
    cases j with
    | none =>
      exact measurable_const.prodMk (measurable_constantBrownianExcursion.comp measurable_fst)
    | some j =>
      exact measurable_const.prodMk (measurable_stoppedBrownianRepresentative_joint (hU j))
  exact hm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

lemma measurable_selectedBrownianExcursionSampler (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (p : Option J × Euc d) :
    Measurable (selectedBrownianExcursionSampler U p) :=
  (measurable_selectedBrownianExcursionSampler_joint U hU).comp
    (measurable_const.prodMk measurable_id)

/-- Equality of the actual fresh-path pushforward with the selected full
excursion kernel, including the initial active excursion. -/
theorem selectedBrownianExcursionSampler_map (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (p : Option J × Euc d) :
    μ.map (selectedBrownianExcursionSampler U p) =
      selectedExcursionKernel (fun j => brownianExcursionKernel (hU j) μ)
        (ContinuousMap.const unitInterval) measurable_constantBrownianExcursion p := by
  rcases p with ⟨j, x⟩
  cases j with
  | none =>
    change μ.map (fun _ : BrownianPath d => (true, ContinuousMap.const unitInterval x)) =
      Measure.dirac (true, ContinuousMap.const unitInterval x)
    rw [Measure.map_const, measure_univ, one_smul]
  | some j =>
    have hflag : Measurable (fun s : C(unitInterval, Euc d) => (false, s)) :=
      measurable_const.prodMk measurable_id
    rw [selectedExcursionKernel_some, brownianExcursionKernel_apply,
      Measure.map_map hflag
        (measurable_stoppedBrownianRepresentative (hU j) x)]
    rfl

/-- The next sampler uses the previous endpoint and preserves termination
regardless of the later selector. -/
noncomputable def absorbingBrownianExcursionSampler (U : J → Set (Euc d))
    (selector : Euc d → Option J) (q : Bool × C(unitInterval, Euc d))
    (ω : BrownianPath d) : Bool × C(unitInterval, Euc d) :=
  selectedBrownianExcursionSampler U
    ((if q.1 then none else selector (q.2 1)), q.2 1) ω

@[simp] lemma absorbingBrownianExcursionSampler_true (U : J → Set (Euc d))
    (selector : Euc d → Option J) (c : C(unitInterval, Euc d)) (ω : BrownianPath d) :
    absorbingBrownianExcursionSampler U selector (true, c) ω =
      (true, ContinuousMap.const unitInterval (c 1)) := rfl

@[simp] lemma absorbingBrownianExcursionSampler_false (U : J → Set (Euc d))
    (selector : Euc d → Option J) (c : C(unitInterval, Euc d)) (ω : BrownianPath d) :
    absorbingBrownianExcursionSampler U selector (false, c) ω =
      selectedBrownianExcursionSampler U (selector (c 1), c 1) ω := rfl

lemma measurable_absorbingBrownianExcursionSampler_joint (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (selector : Euc d → Option J)
    (hselector : Measurable selector) :
    Measurable (fun p : (Bool × C(unitInterval, Euc d)) × BrownianPath d =>
      absorbingBrownianExcursionSampler U selector p.1 p.2) := by
  have hchoice : Measurable (fun q : Bool × C(unitInterval, Euc d) =>
      if q.1 then none else selector (q.2 1)) := by
    apply measurable_from_prod_countable_right
    intro b
    cases b with
    | false => exact hselector.comp (ContinuousMap.measurable_eval 1)
    | true => exact measurable_const
  have hend : Measurable (fun q : Bool × C(unitInterval, Euc d) => q.2 1) :=
    (ContinuousMap.measurable_eval 1).comp measurable_snd
  exact (measurable_selectedBrownianExcursionSampler_joint U hU).comp
    (((hchoice.prodMk hend).comp measurable_fst).prodMk measurable_snd)

lemma measurable_absorbingBrownianExcursionSampler (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (selector : Euc d → Option J)
    (hselector : Measurable selector) (q : Bool × C(unitInterval, Euc d)) :
    Measurable (absorbingBrownianExcursionSampler U selector q) :=
  (measurable_absorbingBrownianExcursionSampler_joint U hU selector hselector).comp
    (measurable_const.prodMk measurable_id)

/-- Pointwise equality with the shared absorbing kernel, for the actual
measurable sampler driven by one fresh Brownian path. -/
theorem absorbingBrownianExcursionSampler_map (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (selector : Euc d → Option J) (hselector : Measurable selector)
    (q : Bool × C(unitInterval, Euc d)) :
    μ.map (absorbingBrownianExcursionSampler U selector q) =
      absorbingExcursionKernel (fun j => brownianExcursionKernel (hU j) μ)
        (fun c => c 1) (ContinuousMap.measurable_eval 1)
        (ContinuousMap.const unitInterval) measurable_constantBrownianExcursion selector hselector q := by
  change μ.map (selectedBrownianExcursionSampler U
    ((if q.1 then none else selector (q.2 1)), q.2 1)) = _
  rw [selectedBrownianExcursionSampler_map U hU μ]
  rcases q with ⟨b, c⟩
  cases b <;> rfl

end BouRabeeGwynne
