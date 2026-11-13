/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ActualThresholdArrayDescent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.WindowModulusGridTransfer

/-!
# Descending a localized martingale array from the completion to the original space

## Why this is needed

Every threshold-lane producer (`LocalizedArrayProducer.ThresholdArrayInputs`,
`LocalizedThresholdArray.LocalThresholdArrayInputs`) asks the row filtrations to contain the null
events:

`null : ∀ n t (A : Set Ω), P A = 0 → MeasurableSet[F n t] A`.

Since `F n t ≤ m`, this forces the **ambient** σ-algebra `m` to be `P`-complete.  The canonical
sample space `Existence.Sample V = (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ)` carries the product Borel
σ-algebra and the canonical law has exponential (non-atomic) real coordinates, so it is **not**
complete: stated on `areaSampleLaw` itself, the producers' hypotheses are unsatisfiable.  This is
why the walk's bracket `InvarianceMainStatement.CanonicalBracket` lives on
`NullMeasurableSpace (Existence.Sample _) P` with `P.completion` and the completed filtration.

The `harray` consumers (`CompactContainmentProducer.compactContainment_of_arrays`,
`ExactClockModulus`, `RescaledInterpolationError`, `ActualWindowModulus`), however, ask for a
`LocalizedMartingaleArray` on the **original** space `(Existence.Sample _, areaSampleLaw)`.  The
producers therefore land on the wrong space, and a descent is required.

## What is proved

* `exists_martingale_modification_of_completion` — **an almost surely right-continuous martingale
  on the completion has an indistinguishable modification which is a martingale on the original
  space**, for the *augmented trace* filtration `augFiltration P F̄` (`t ↦ {A ∈ m | A =ᵐ A' for
  some A' ∈ F̄ t}`).  The modification is `G.indicator U` for one measurable full-measure set `G`
  on which the paths are right continuous and agree with measurable versions along a countable
  dense set of times; its measurability is that of a pointwise limit along times decreasing to
  `t`.
* `nonempty_localizedMartingaleArray_of_completion` — **the descent**: a localized martingale
  array for target rows `X` on the completion yields one on the original space, with the same
  terminal constant and bracket slope.  The rows and the compensated squares are modified by the
  previous statement, the compensator is *defined* as their difference, the envelopes are
  replaced by measurable versions, and every probability, integral and almost-sure statement is
  transported through `Measure.completion_apply` / `Measure.ae_completion` (both `rfl`).

Nothing here mentions the reflected walk.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.ActualThresholdArray

open ReflectedGMS.WindowModulusGridTransfer

/-! ## The augmented trace σ-algebra -/

section AugTrace

variable {Ω : Type*}

/-- **The augmented trace** of a σ-algebra `n` on the σ-algebra `m`: the `m`-measurable sets that
agree `P`-almost everywhere with some `n`-measurable set.  With `n` a σ-algebra of the completion
this is the natural sub-σ-algebra of `m` "known to `n` up to null sets". -/
def augTrace (m : MeasurableSpace Ω) (P : @Measure Ω m) (n : MeasurableSpace Ω) :
    MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet[m] s ∧ ∃ s' : Set Ω, MeasurableSet[n] s' ∧ s =ᵐ[P] s'
  measurableSet_empty := ⟨@MeasurableSet.empty _ m, ∅, @MeasurableSet.empty _ n,
    EventuallyEqSet.rfl⟩
  measurableSet_compl := fun s hs =>
    ⟨hs.1.compl, (hs.2.choose)ᶜ, hs.2.choose_spec.1.compl, hs.2.choose_spec.2.compl⟩
  measurableSet_iUnion := fun f hf =>
    ⟨MeasurableSet.iUnion fun i => (hf i).1, ⋃ i, (hf i).2.choose,
      MeasurableSet.iUnion fun i => (hf i).2.choose_spec.1,
      EventuallyEqSet.countable_iUnion fun i => (hf i).2.choose_spec.2⟩

theorem augTrace_le (m : MeasurableSpace Ω) (P : @Measure Ω m) (n : MeasurableSpace Ω) :
    augTrace m P n ≤ m := fun _ hs => hs.1

theorem augTrace_mono (m : MeasurableSpace Ω) (P : @Measure Ω m) {n₁ n₂ : MeasurableSpace Ω}
    (h : n₁ ≤ n₂) : augTrace m P n₁ ≤ augTrace m P n₂ := fun _ hs =>
  ⟨hs.1, hs.2.choose, h _ hs.2.choose_spec.1, hs.2.choose_spec.2⟩

/-- A function measurable for `m` and almost everywhere equal to an `n`-measurable function is
measurable for the augmented trace. -/
theorem measurable_augTrace (m : MeasurableSpace Ω) (P : @Measure Ω m) {n : MeasurableSpace Ω}
    {f g : Ω → ℝ} (hf : Measurable[m] f) (hg : Measurable[n] g)
    (hfg : ∀ᵐ ω ∂P, f ω = g ω) : Measurable[augTrace m P n] f := by
  intro S hS
  refine ⟨hf hS, g ⁻¹' S, hg hS, Eventually.set_eq ?_⟩
  filter_upwards [hfg] with ω hω
  show f ω ∈ S ↔ g ω ∈ S
  rw [hω]

end AugTrace

section Completion

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **The augmented trace filtration** of a filtration of the completion. -/
def augFiltration (P : @Measure Ω m)
    (F : @Filtration (NullMeasurableSpace Ω P) ℝ≥0 _ inferInstance) :
    Filtration ℝ≥0 m where
  seq t := augTrace m P (F t)
  mono' _ _ hst := augTrace_mono m P (F.mono hst)
  le' _ := augTrace_le m P _

/-! ### The identity map from the completion -/

/-- The identity map from the completion to the original space, with its codomain named. -/
def completionId (P : @Measure Ω m) : NullMeasurableSpace Ω P → Ω := fun ω => ω

theorem measurable_completionId (P : @Measure Ω m) : Measurable (completionId P) :=
  fun _ hs => hs.nullMeasurableSet

theorem measurePreserving_completionId (P : @Measure Ω m) :
    MeasurePreserving (completionId P) P.completion P := by
  refine ⟨measurable_completionId P, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_completionId P) hs]
  change P.completion s = P s
  exact Measure.completion_apply P s

theorem ae_of_ae_completion {P : @Measure Ω m} {p : Ω → Prop}
    (h : ∀ᵐ ω ∂P.completion, p ω) : ∀ᵐ ω ∂P, p ω := h

theorem ae_completion_of_ae {P : @Measure Ω m} {p : Ω → Prop}
    (h : ∀ᵐ ω ∂P, p ω) : ∀ᵐ ω ∂P.completion, p ω := h

theorem integral_completion_eq {P : @Measure Ω m} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) :
    ∫ ω : NullMeasurableSpace Ω P, f ω ∂P.completion = ∫ ω, f ω ∂P := by
  have heP := measurePreserving_completionId P
  calc ∫ ω : NullMeasurableSpace Ω P, f ω ∂P.completion
      = ∫ ω : Ω, f ω ∂Measure.map (completionId P) P.completion :=
        (integral_map heP.measurable.aemeasurable (by simpa only [heP.map_eq] using hf)).symm
    _ = ∫ ω, f ω ∂P := by rw [heP.map_eq]

theorem setIntegral_completion_eq {P : @Measure Ω m} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ ω : NullMeasurableSpace Ω P in s, f ω ∂P.completion = ∫ ω in s, f ω ∂P := by
  calc ∫ ω : NullMeasurableSpace Ω P in s, f ω ∂P.completion
      = ∫ ω : NullMeasurableSpace Ω P, s.indicator f ω ∂P.completion :=
        (integral_indicator hs.nullMeasurableSet).symm
    _ = ∫ ω : Ω, s.indicator f ω ∂P := integral_completion_eq (hf.indicator hs)
    _ = ∫ ω in s, f ω ∂P := integral_indicator hs

theorem integrable_completion_iff {P : @Measure Ω m} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) :
    Integrable (fun ω : NullMeasurableSpace Ω P => f ω) P.completion ↔ Integrable f P := by
  have heP := measurePreserving_completionId P
  have h := integrable_map_measure (μ := P.completion) (f := completionId P) (g := f)
    (by simpa only [heP.map_eq] using hf) heP.measurable.aemeasurable
  rw [heP.map_eq] at h
  exact h.symm

theorem memLp_completion_iff {P : @Measure Ω m} {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (p : ℝ≥0∞) :
    MemLp (fun ω : NullMeasurableSpace Ω P => f ω) p P.completion ↔ MemLp f p P := by
  have heP := measurePreserving_completionId P
  have h := memLp_map_measure_iff (μ := P.completion) (p := p) (f := completionId P) (g := f)
    (by simpa only [heP.map_eq] using hf) heP.measurable.aemeasurable
  rw [heP.map_eq] at h
  exact h.symm

/-- Every function measurable for the completion has a measurable version. -/
theorem exists_measurable_version {P : @Measure Ω m} {f : NullMeasurableSpace Ω P → ℝ}
    (hf : Measurable f) : ∃ g : Ω → ℝ, Measurable g ∧ ∀ᵐ ω ∂P, f ω = g ω := by
  have h : AEMeasurable (f : Ω → ℝ) P := MeasureTheory.NullMeasurable.aemeasurable hf
  exact ⟨h.mk _, h.measurable_mk, h.ae_eq_mk⟩

/-! ### The martingale modification -/

/-- **A right-continuous martingale on the completion descends.**  An almost surely
right-continuous martingale `U` of a filtration `F` of the completion has a modification `U'`,
equal to `U` at all times on one full-probability event, which is a martingale of the original
space for the augmented trace filtration `augFiltration P F`. -/
theorem exists_martingale_modification_of_completion (P : @Measure Ω m) [IsFiniteMeasure P]
    (F : @Filtration (NullMeasurableSpace Ω P) ℝ≥0 _ inferInstance) {U : ℝ≥0 → Ω → ℝ}
    (hU : Martingale (Ω := NullMeasurableSpace Ω P) U F P.completion)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (fun t => U t ω)) :
    ∃ U' : ℝ≥0 → Ω → ℝ, Martingale U' (augFiltration P F) P ∧
      ∀ᵐ ω ∂P, ∀ t, U' t ω = U t ω := by
  classical
  have : IsFiniteMeasure P.completion :=
    ⟨(Measure.completion_apply P Set.univ).trans_lt (measure_lt_top P Set.univ)⟩
  -- measurable versions at every time
  have hver : ∀ t, ∃ g : Ω → ℝ, Measurable g ∧ ∀ᵐ ω ∂P, U t ω = g ω := fun t =>
    exists_measurable_version (P := P) ((hU.stronglyAdapted t).mono (F.le t)).measurable
  choose g hgm hgae using hver
  -- a countable dense set of times
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  -- the bad event and the good measurable event
  set Bad : Set Ω := {ω | ¬ IsRightContinuous (fun t => U t ω)} ∪
    ⋃ d ∈ D, {ω | U d ω ≠ g d ω} with hBad
  have hBad0 : P Bad = 0 := by
    refine measure_union_null (ae_iff.1 hrc) ?_
    exact (measure_biUnion_null_iff hDc).2 fun d _ => ae_iff.1 (hgae d)
  set G : Set Ω := (toMeasurable P Bad)ᶜ with hG
  have hGm : MeasurableSet G := (measurableSet_toMeasurable P Bad).compl
  have hGc : P Gᶜ = 0 := by
    rw [hG, compl_compl, measure_toMeasurable]
    exact hBad0
  have hGgood : ∀ ω ∈ G,
      IsRightContinuous (fun t => U t ω) ∧ ∀ d ∈ D, U d ω = g d ω := by
    intro ω hω
    have hω' : ω ∉ Bad := fun h => hω (subset_toMeasurable P Bad h)
    rw [hBad] at hω'
    refine ⟨?_, fun d hd => ?_⟩
    · by_contra h
      exact hω' (Or.inl h)
    · by_contra h
      exact hω' (Or.inr (Set.mem_biUnion hd h))
  have hae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    exact measure_mono_null (fun ω hω => hω) hGc
  have hmod : ∀ᵐ ω ∂P, ∀ t, G.indicator (U t) ω = U t ω := by
    filter_upwards [hae] with ω hω t
    exact Set.indicator_of_mem hω _
  -- measurability of the modification on the original space
  have hU'm : ∀ t, Measurable (G.indicator (U t)) := by
    intro t
    obtain ⟨u, -, hu, hlim⟩ := hDd.exists_seq_strictAnti_tendsto t
    refine measurable_of_tendsto_metrizable (f := fun n => G.indicator (g (u n)))
      (fun n => (hgm (u n)).indicator hGm) ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ G
    · simp only [Set.indicator_of_mem hω]
      have hgood := hGgood ω hω
      have hwithin : Tendsto u atTop (𝓝[>] t) :=
        tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => (hu n).1⟩
      have h1 : Tendsto (fun n => U (u n) ω) atTop (𝓝 (U t ω)) :=
        (hgood.1 t).tendsto.comp hwithin
      exact h1.congr fun n => hgood.2 (u n) (hu n).2
    · simp only [Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  -- adaptedness to the augmented trace filtration
  have hU'aug : ∀ t, Measurable[augFiltration P F t] (G.indicator (U t)) := fun t =>
    measurable_augTrace m P (hU'm t) ((hU.stronglyAdapted t).measurable)
      (hmod.mono fun ω h => h t)
  -- integrability on the original space
  have hint : ∀ t, Integrable (G.indicator (U t)) P := by
    intro t
    refine (integrable_completion_iff (hU'm t).aestronglyMeasurable).1 ?_
    exact (hU.integrable t).congr (ae_completion_of_ae (hmod.mono fun ω h => (h t).symm))
  refine ⟨fun t => G.indicator (U t), ⟨fun t => (hU'aug t).stronglyMeasurable, ?_⟩, hmod⟩
  intro s t hst
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((augFiltration P F).le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (hU'aug s).stronglyMeasurable.aestronglyMeasurable).symm
  obtain ⟨hAm, A', hA', hAA'⟩ := hA
  have hAA'c : A =ᵐ[P.completion] A' := hAA'
  calc ∫ x in A, G.indicator (U s) x ∂P
      = ∫ x : NullMeasurableSpace Ω P in A, G.indicator (U s) x ∂P.completion :=
        (setIntegral_completion_eq (hU'm s).aestronglyMeasurable hAm).symm
    _ = ∫ x : NullMeasurableSpace Ω P in A', G.indicator (U s) x ∂P.completion :=
        setIntegral_congr_set hAA'c
    _ = ∫ x : NullMeasurableSpace Ω P in A', U s x ∂P.completion :=
        integral_congr_ae (ae_restrict_of_ae (ae_completion_of_ae (hmod.mono fun ω h => h s)))
    _ = ∫ x : NullMeasurableSpace Ω P in A', U t x ∂P.completion := hU.setIntegral_eq hst hA'
    _ = ∫ x : NullMeasurableSpace Ω P in A', G.indicator (U t) x ∂P.completion :=
        (integral_congr_ae
          (ae_restrict_of_ae (ae_completion_of_ae (hmod.mono fun ω h => h t)))).symm
    _ = ∫ x : NullMeasurableSpace Ω P in A, G.indicator (U t) x ∂P.completion :=
        (setIntegral_congr_set hAA'c).symm
    _ = ∫ x in A, G.indicator (U t) x ∂P :=
        setIntegral_completion_eq (hU'm t).aestronglyMeasurable hAm

/-! ### The descent of an array -/

/-- **A localized martingale array on the completion descends to the original space.**  Same
target rows, same horizon; the terminal constant and the bracket slope are unchanged. -/
theorem nonempty_localizedMartingaleArray_of_completion (P : @Measure Ω m)
    [IsProbabilityMeasure P]
    {X : ℕ → ℝ≥0 → Ω → ℝ} {H : ℝ≥0}
    (hA : Nonempty (LocalizedMartingaleArray (Ω := NullMeasurableSpace Ω P) P.completion X H)) :
    Nonempty (LocalizedMartingaleArray P X H) := by
  classical
  obtain ⟨A⟩ := hA
  -- the rows and the compensated squares descend
  have hrow : ∀ n, ∃ Y' : ℝ≥0 → Ω → ℝ, Martingale Y' (augFiltration P (A.F n)) P ∧
      ∀ᵐ ω ∂P, ∀ t, Y' t ω = A.Y n t ω := fun n =>
    exists_martingale_modification_of_completion P (A.F n) (A.martingale n)
      (ae_of_ae_completion ((A.cadlag n).mono fun _ h => h.isRightContinuous))
  have hcomp : ∀ n, ∃ Z' : ℝ≥0 → Ω → ℝ, Martingale Z' (augFiltration P (A.F n)) P ∧
      ∀ᵐ ω ∂P, ∀ t, Z' t ω = A.Y n t ω * A.Y n t ω - A.B n t ω := fun n =>
    exists_martingale_modification_of_completion P (A.F n) (A.compensated n)
      (ae_of_ae_completion (A.rightContinuous_compensated n))
  have hRver : ∀ n, ∃ R' : Ω → ℝ, Measurable R' ∧ ∀ᵐ ω ∂P, R' ω = A.R n ω := by
    intro n
    obtain ⟨g', hg'm, hg'ae⟩ := (A.integrable_error n).aestronglyMeasurable
    obtain ⟨g, hg, hgae⟩ := exists_measurable_version (P := P) hg'm.measurable
    refine ⟨g, hg, ?_⟩
    have h1 : ∀ᵐ ω ∂P, A.R n ω = g' ω := hg'ae
    filter_upwards [h1, hgae] with ω h1ω h2ω
    rw [h1ω, h2ω]
  choose Y' hY'mart hY'eq using hrow
  choose Z' hZ'mart hZ'eq using hcomp
  choose R' hR'm hR'eq using hRver
  have hY'meas : ∀ n t, AEStronglyMeasurable (Y' n t) P := fun n t =>
    (((hY'mart n).stronglyAdapted t).mono ((augFiltration P (A.F n)).le t)).aestronglyMeasurable
  refine ⟨{
    F := fun n => augFiltration P (A.F n)
    Y := Y'
    B := fun n t ω => Y' n t ω * Y' n t ω - Z' n t ω
    R := R'
    C := A.C
    v := A.v
    martingale := hY'mart
    compensated := ?_
    cadlag := ?_
    rightContinuous_compensated := ?_
    memLp := ?_
    terminal := ?_
    v_nonneg := A.v_nonneg
    integrable_error := ?_
    error := ?_
    error_mean := ?_
    agree := ?_ }⟩
  · intro n
    simp only [sub_sub_cancel]
    exact hZ'mart n
  · intro n
    filter_upwards [hY'eq n, ae_of_ae_completion (A.cadlag n)] with ω h1 h2
    have heq : (fun t => Y' n t ω) = fun t => A.Y n t ω := funext h1
    rw [heq]
    exact h2
  · intro n
    filter_upwards [hZ'eq n, ae_of_ae_completion (A.rightContinuous_compensated n)]
      with ω h1 h2
    simp only [sub_sub_cancel]
    have heq : (fun t => Z' n t ω) = fun t => A.Y n t ω * A.Y n t ω - A.B n t ω := funext h1
    rw [heq]
    exact h2
  · intro n t
    have hae : ∀ᵐ ω ∂P, A.Y n t ω = Y' n t ω := (hY'eq n).mono fun ω h => (h t).symm
    exact (memLp_completion_iff (hY'meas n t) 2).1
      (MemLp.ae_eq (ae_completion_of_ae hae) (A.memLp n t))
  · intro n
    have hae : ∀ᵐ ω ∂P, Y' n H ω ^ 2 = A.Y n H ω ^ 2 := (hY'eq n).mono fun ω h => by rw [h H]
    calc ∫ ω, Y' n H ω ^ 2 ∂P
        = ∫ ω : NullMeasurableSpace Ω P, Y' n H ω ^ 2 ∂P.completion :=
          (integral_completion_eq ((hY'meas n H).pow 2)).symm
      _ = ∫ ω : NullMeasurableSpace Ω P, A.Y n H ω ^ 2 ∂P.completion :=
          integral_congr_ae (ae_completion_of_ae hae)
      _ ≤ A.C := A.terminal n
  · intro n
    refine (integrable_completion_iff (hR'm n).aestronglyMeasurable).1 ?_
    exact (A.integrable_error n).congr
      (ae_completion_of_ae ((hR'eq n).mono fun ω h => h.symm))
  · intro n
    filter_upwards [hY'eq n, hZ'eq n, hR'eq n, ae_of_ae_completion (A.error n)]
      with ω h1 h2 h3 h4
    intro t ht
    show |Y' n t ω * Y' n t ω - Z' n t ω - A.v * (t : ℝ)| ≤ R' n ω
    rw [h1 t, h2 t, h3, sub_sub_cancel]
    exact h4 t ht
  · have heq : ∀ n, ∫ ω : NullMeasurableSpace Ω P, A.R n ω ∂P.completion = ∫ ω, R' n ω ∂P := by
      intro n
      rw [← integral_completion_eq (hR'm n).aestronglyMeasurable]
      exact integral_congr_ae (ae_completion_of_ae ((hR'eq n).mono fun ω h => h.symm))
    exact A.error_mean.congr heq
  · have hset : ∀ n, P.completion {ω | ∃ t ≤ H, A.Y n t ω ≠ X n t ω} =
        P {ω | ∃ t ≤ H, Y' n t ω ≠ X n t ω} := by
      intro n
      refine (Measure.completion_apply P _).trans (measure_congr (Eventually.set_eq ?_))
      filter_upwards [hY'eq n] with ω h
      show (∃ t ≤ H, A.Y n t ω ≠ X n t ω) ↔ (∃ t ≤ H, Y' n t ω ≠ X n t ω)
      simp only [h]
    exact A.agree.congr hset

end Completion

end ReflectedGMS.ActualThresholdArray
