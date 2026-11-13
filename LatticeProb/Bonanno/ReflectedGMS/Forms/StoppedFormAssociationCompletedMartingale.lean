/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedFormAssociationCompletedMartingale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.RightContinuousMartingaleUITransfer
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalMartingaleCombination

/-!
# Completed-filtration martingales from almost-everywhere adapted increment identities

The fast-side drift elimination of `p:lem:localharm`
(`Forms/StoppedHarmonicLimitIntegration`, `Forms/StoppedHarmonicAdaptedness`) delivers a
stopped process that is only *almost everywhere* adapted to the right continuation of the
raw natural filtration, together with set-integral increment identities on that raw
filtration.  Mathlib's `Martingale` predicate demands exact adaptedness, so no
`Martingale` structure is available on the raw filtration.  On the project's completed
natural filtration `Process/NaturalFiltration.completedNaturalFiltration` — which contains
every null event and is right continuous — the same data *is* a martingale.  This module
proves that transfer once, generically:

* `martingale_completedNaturalFiltration_of_rightCont_setIntegral` — a real process which
  is integrable, a.e. strongly measurable for the right-continuous raw natural filtration
  at each time, a.s. right continuous, and satisfies the martingale set-integral
  identities on that raw filtration, is a `Martingale` of
  `completedNaturalFiltration P X hX` under `P.completion`.

The route is that of `Forms/CompletedRightContinuousMartingaleTransfer`: adjoin the null
events (null sets make a.e. adaptedness exact, and every event of the augmented filtration
is a.e. equal to a raw event), pass to the right continuation by the uniform-integrability
transfer `Forms/RightContinuousMartingaleUITransfer`, and identify the completed natural
filtration with that right continuation.  Nothing here mentions a process law or a speed
measure.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace ReflectedGMS.StoppedFormAssociation

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ## The identity map from the completion -/

/-- The identity from the completed measure space to the original one is measure
preserving. -/
theorem completion_identity_measurePreserving (P : @Measure Ω m) :
    @MeasurePreserving (NullMeasurableSpace Ω P) Ω
      (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) m
      (fun ω => (ω : Ω)) P.completion P := by
  let e : NullMeasurableSpace Ω P → Ω := fun ω => ω
  have he : Measurable e := fun _ hs => hs.nullMeasurableSet
  refine ⟨he, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply he hs]
  change P.completion s = P s
  exact Measure.completion_apply P s

theorem integrable_completion_of_integrable
    {P : Measure Ω} {f : Ω → ℝ} (hf : Integrable f P) :
    Integrable (fun ω : NullMeasurableSpace Ω P => f ω) P.completion :=
  (completion_identity_measurePreserving P).integrable_comp_of_integrable hf

theorem setIntegral_completion_eq_setIntegral
    {P : Measure Ω} {f : Ω → ℝ} {s : Set Ω}
    (hf : Integrable f P) (hs : MeasurableSet s) :
    (∫ ω : NullMeasurableSpace Ω P in s, f ω ∂P.completion) =
      ∫ ω : Ω in s, f ω ∂P := by
  let e : NullMeasurableSpace Ω P → Ω := fun ω => ω
  have heP : MeasurePreserving e P.completion P :=
    completion_identity_measurePreserving P
  have hfi : AEStronglyMeasurable (s.indicator f) P :=
    (hf.indicator hs).aestronglyMeasurable
  calc
    (∫ ω : NullMeasurableSpace Ω P in s, f ω ∂P.completion) =
        ∫ ω : NullMeasurableSpace Ω P, s.indicator f ω ∂P.completion :=
      (integral_indicator hs.nullMeasurableSet).symm
    _ = ∫ ω : Ω, s.indicator f ω ∂P := by
      calc
        _ = ∫ ω : Ω, s.indicator f ω ∂Measure.map e P.completion :=
          (integral_map heP.measurable.aemeasurable
            (by simpa only [heP.map_eq] using hfi)).symm
        _ = _ := by rw [heP.map_eq]
    _ = ∫ ω : Ω in s, f ω ∂P := integral_indicator hs

/-- An almost-sure statement for `P` is one for its completion. -/
theorem ae_completion_of_ae {P : Measure Ω} {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ ω : NullMeasurableSpace Ω P ∂P.completion, p ω :=
  h

/-! ## A martingale for a larger filtration, adapted to a smaller one -/

theorem martingale_of_le_of_stronglyAdapted
    {Ω' : Type*} {m' : MeasurableSpace Ω'}
    {P : Measure Ω'} [IsFiniteMeasure P]
    {F E : Filtration ℝ≥0 m'} {M : ℝ≥0 → Ω' → ℝ}
    (hEF : E ≤ F) (hM : Martingale M F P) (hE : StronglyAdapted E M) :
    Martingale M E P := by
  refine ⟨hE, fun s t hst => ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq
    (E.le s) (hM.integrable t) (fun _ _ _ => (hM.integrable s).integrableOn) ?_
      (hE s).aestronglyMeasurable).symm
  intro A hA _
  exact hM.setIntegral_eq hst (hEF s A hA)

/-! ## The transfer -/

/-- **Completed-filtration martingale from raw right-continuous increment identities.**

`Y` is integrable at every time, at every time `t` almost everywhere equal to a function
measurable for the right continuation of the raw natural filtration at `t`, almost surely
right continuous, and satisfies the set-integral martingale identities for every event of
that right continuation.  Then `Y` is a martingale of the completed natural filtration under
the completed law. -/
theorem martingale_completedNaturalFiltration_of_rightCont_setIntegral
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : ℝ≥0 → Ω → ℕ} (hX : ∀ t, Measurable (X t))
    {Y : ℝ≥0 → Ω → ℝ}
    (hint : ∀ t, Integrable (Y t) P)
    (hadapt : ∀ t, AEStronglyMeasurable[(Filtration.natural X
      (fun t => (hX t).stronglyMeasurable)).rightCont t] (Y t) P)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => Y t ω))
    (hset : ∀ s t, s ≤ t → ∀ B : Set Ω,
      MeasurableSet[(Filtration.natural X (fun t => (hX t).stronglyMeasurable)).rightCont s] B →
      ∫ ω in B, Y t ω ∂P = ∫ ω in B, Y s ω ∂P) :
    Martingale (fun t (ω : NullMeasurableSpace Ω P) => Y t ω)
      (ProcessFiltration.completedNaturalFiltration P X hX) P.completion := by
  have : IsFiniteMeasure P.completion :=
    ⟨(Measure.completion_apply P (Set.univ : Set Ω)).trans_lt
      (measure_lt_top P Set.univ)⟩
  let N : Filtration ℝ≥0
      (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) :=
    Filtration.natural (Ω := NullMeasurableSpace Ω P) X
      (fun t => (hX t).nullMeasurable.measurable'.stronglyMeasurable)
  let H : Filtration ℝ≥0
      (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) := {
    seq := fun t => N t ⊔ ProcessFiltration.nullEventSigma P
    mono' := fun _ _ h => sup_le_sup (N.mono h) le_rfl
    le' := fun t => sup_le (N.le t)
      (MeasurableSpace.generateFrom_le
        (fun _ hs => NullMeasurableSet.of_null hs)) }
  let G : Filtration ℝ≥0
      (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) := {
    seq := fun t => N.rightCont t ⊔ ProcessFiltration.nullEventSigma P
    mono' := fun _ _ h => sup_le_sup (N.rightCont.mono h) le_rfl
    le' := fun t => sup_le (N.rightCont.le t)
      (MeasurableSpace.generateFrom_le
        (fun _ hs => NullMeasurableSet.of_null hs)) }
  have hNright (u : ℝ≥0) :
      N.rightCont u =
        (Filtration.natural X (fun v => (hX v).stronglyMeasurable)).rightCont u := by
    rw [Filtration.rightCont_eq, Filtration.rightCont_eq]
    rfl
  -- null events are measurable for `G`
  have hnull : ∀ (t : ℝ≥0) (A : Set (NullMeasurableSpace Ω P)),
      P.completion A = 0 → MeasurableSet[G t] A := by
    intro t A hA
    have hle : ProcessFiltration.nullEventSigma P ≤ G t :=
      le_sup_right (a := N.rightCont t) (b := ProcessFiltration.nullEventSigma P)
    refine hle _ (MeasurableSpace.GenerateMeasurable.basic A ?_)
    exact (Measure.completion_apply P A).symm.trans hA
  -- the process on the completed space
  let Y' : ℝ≥0 → NullMeasurableSpace Ω P → ℝ := fun t ω => Y t ω
  have hY'int : ∀ t, Integrable (Y' t) P.completion := fun t =>
    integrable_completion_of_integrable (hint t)
  -- exact adaptedness to `G` from a.e. adaptedness plus null events
  have hGadapt : StronglyAdapted G Y' := by
    intro t
    obtain ⟨g, hg, hgY⟩ := hadapt t
    have hg' : StronglyMeasurable[G t] (fun ω : NullMeasurableSpace Ω P => g ω) := by
      have hgN : StronglyMeasurable[N.rightCont t] (fun ω : NullMeasurableSpace Ω P => g ω) := by
        rw [hNright t]
        exact hg
      exact hgN.mono (le_sup_left (a := N.rightCont t) (b := ProcessFiltration.nullEventSigma P))
    exact LocalMartingaleCombination.stronglyMeasurable_of_ae_eq_of_null_events (G.le t)
      (hnull t) hg' (ae_completion_of_ae hgY.symm)
  -- the martingale property for `G`
  have hMG : Martingale Y' G P.completion := by
    refine ⟨hGadapt, fun s t hst => ?_⟩
    apply (ae_eq_condExp_of_forall_setIntegral_eq
      (G.le s) (hY'int t) (fun _ _ _ => (hY'int s).integrableOn) ?_
        (hGadapt s).aestronglyMeasurable).symm
    intro A hA _
    have hAev : EventuallyMeasurableSet (N.rightCont s) (ae P.completion) A := by
      apply (show G s ≤ eventuallyMeasurableSpace (N.rightCont s) (ae P.completion) from ?_) A hA
      refine sup_le le_eventuallyMeasurableSpace ?_
      apply MeasurableSpace.generateFrom_le
      intro Z hZ
      refine ⟨∅, @MeasurableSet.empty _ (N.rightCont s), ae_eq_empty.mpr ?_⟩
      exact (Measure.completion_apply P Z).trans hZ
    rcases hAev with ⟨B, hB, hAB⟩
    have hB0 := hB
    rw [hNright s] at hB0
    have hBm : @MeasurableSet Ω m B :=
      (Filtration.natural X (fun u => (hX u).stronglyMeasurable)).rightCont.le s B hB0
    calc
      ∫ ω in A, Y' s ω ∂P.completion = ∫ ω in B, Y' s ω ∂P.completion :=
        setIntegral_congr_set hAB
      _ = ∫ ω in B, Y s ω ∂P := setIntegral_completion_eq_setIntegral (hint s) hBm
      _ = ∫ ω in B, Y t ω ∂P := (hset s t hst B hB0).symm
      _ = ∫ ω in B, Y' t ω ∂P.completion :=
        (setIntegral_completion_eq_setIntegral (hint t) hBm).symm
      _ = ∫ ω in A, Y' t ω ∂P.completion := setIntegral_congr_set hAB.symm
  -- pass to the right continuation of `G`
  have hAdaptedG : StronglyAdapted G.rightCont Y' := fun t =>
    (hMG.stronglyMeasurable t).mono (G.le_rightCont t)
  have hGright : Martingale Y' G.rightCont P.completion :=
    martingale_rightCont_of_ae_eq_of_ae_rightContinuous
      (P := P.completion) (F := G) hMG hAdaptedG
      (fun _ => EventuallyEq.rfl) (ae_completion_of_ae hr)
  -- the completed natural filtration is the right continuation of `H`, and `H₊ ≤ G₊`
  have hHG : H ≤ G := fun t =>
    sup_le_sup (N.le_rightCont t) le_rfl
  have hHrightGright : H.rightCont ≤ G.rightCont := by
    intro t
    rw [Filtration.rightCont_eq, Filtration.rightCont_eq]
    refine le_iInf₂ fun u hu => ?_
    exact (iInf₂_le u hu).trans (hHG u)
  have hGH : G ≤ H.rightCont := by
    intro t
    rw [Filtration.rightCont_eq]
    refine le_iInf₂ fun u hu => ?_
    refine sup_le_sup ?_ le_rfl
    rw [Filtration.rightCont_eq]
    exact iInf₂_le u hu
  have hHadapt : StronglyAdapted H.rightCont Y' := fun t =>
    (hMG.stronglyMeasurable t).mono (hGH t)
  have hfinal : Martingale Y' H.rightCont P.completion :=
    martingale_of_le_of_stronglyAdapted hHrightGright hGright hHadapt
  exact hfinal

end ReflectedGMS.StoppedFormAssociation
