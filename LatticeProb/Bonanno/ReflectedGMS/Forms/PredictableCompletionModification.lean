/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.PredictableCompletionModification at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergySquareCompensation
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyMartingaleLinearity
import LatticeProb.Bonanno.ReflectedGMS.Forms.PolarizedJumpOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.SquareCovariationPolarization
import LatticeProb.Bonanno.ReflectedGMS.Forms.BracketJointMeasurability
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedAdaptedness
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Predictability across an almost-sure modification on a completed filtration

`MeasureTheory.IsStronglyPredictable F A` is the *strict* statement
`StronglyMeasurable[F.predictable] (Function.uncurry A)`, so an almost-sure
identity `∀ᵐ ω, ∀ t, A t ω = B t ω` does not by itself move predictability from
`A` to `B`.  On the *completed* filtration used by
`InvarianceMainStatement.CanonicalBracket` — the one produced by
`ProcessFiltration.completedNaturalFiltration`, which contains every null event
of the sample law at every time — the transfer does hold, provided the
modification `B` is jointly measurable in `(t, ω)`.

That joint-measurability side condition is *necessary*, not a convenience: the
trace of `F.predictable` on `ℝ≥0 × N`, for a null event `N`, is
`Borel(ℝ≥0) ⊗ (all subsets of N)`, so a modification which is wild in time on a
single null outcome is never predictable, no matter how complete the filtration
is.  The content of this module is that this is the *only* obstruction:

* `measurableSet_predictable_prod_of_null` — a Borel time set crossed with a
  null event is predictable;
* `measurableSet_predictable_inter_null_prod` — a *product-measurable* set
  intersected with `univ ×ˢ (null event)` is predictable;
* `isStronglyPredictable_of_ae_eq` — the a.e.-modification lemma for any
  filtration containing all null events;
* `isStronglyPredictable_completedNaturalFiltration_of_ae_eq` and
  `stronglyAdapted_completedNaturalFiltration_of_ae_eq` — the same statements in
  exactly the shape `CanonicalBracket` consumes, i.e. for
  `ProcessFiltration.completedNaturalFiltration P X hX`;
* `isStronglyPredictable_ordinaryEdgeBracket_completedNaturalFiltration` — the
  instantiation on the pair of `ActualHarmonicBracketIdentification`, carrying
  predictability from the checked predictable representative
  `polarizedJumpOccupation` to the manuscript's `ordinaryEdgeBracket`.

The last statement carried two side hypotheses, `hdom` (the completed
filtration dominates the right-continuous natural filtration of the path) and
`hjoint` (joint measurability of the bracket integral).  Both are discharged
here:

* `rightCont_le_rightCont`, `comap_le_comap_encode`,
  `pastSigma_le_iSup_comap_encode` and
  `naturalFiltration_rightCont_le_completedNaturalFiltration` — `hdom` holds
  whenever the ℕ-valued code is an *injective* encoding of the path, which is
  exactly the shape `InvarianceMainStatement.areaFiltration` uses
  (`observedState = Encodable.encode`).  An injective encoding into a discrete
  measurable space loses no information, so the coded natural filtration is the
  path's own natural filtration, and right continuation is monotone.
* `BracketJointMeasurability.measurable_uncurry_ordinaryEdgeBracket_processFamily`
  supplies `hjoint` for the constructed reflected family of Theorem 1.6.

Hence `isStronglyPredictable_ordinaryEdgeBracket_processFamily` and its
area-clock form `isStronglyPredictable_ordinaryEdgeBracket_exponentialAreaPath`
carry **no** measurability or filtration side hypothesis at all: only the
manuscript's own data (a reflected walk, a connected graph, positive summable
cell areas, finite-energy coordinates) and the injectivity of the code.

Consumer: the third clause of `MartingaleIngredients.HasOrdinaryEdgeBracket`,
i.e. `p:eq:fastPhibracket` of `p:lem:localharm`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal

namespace ReflectedGMS.PredictableCompletionModification

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The whole time axis crossed with a null event is predictable, as soon as the
filtration contains every null event of the law. -/
theorem measurableSet_predictable_univ_prod_of_null
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    (hnull : ∀ (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[F t] S)
    {N : Set Ω} (hN : P N = 0) :
    MeasurableSet[F.predictable] ((univ : Set ℝ≥0) ×ˢ N) := by
  have hsplit : (univ : Set ℝ≥0) = {(⊥ : ℝ≥0)} ∪ Ioi (⊥ : ℝ≥0) := by
    ext t
    simp only [mem_univ, mem_union, mem_singleton_iff, mem_Ioi, true_iff]
    exact eq_bot_or_bot_lt t
  rw [hsplit, Set.union_prod]
  exact (measurableSet_predictable_singleton_bot_prod (hnull ⊥ N hN)).union
    (measurableSet_predictable_Ioi_prod (hnull ⊥ N hN))

/-- Every Borel time set crossed with a null event is predictable: the sets
`Set.Ioi i` generate the Borel structure of `ℝ≥0`, and the null event lies in
every level of the filtration. -/
theorem measurableSet_predictable_prod_of_null
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    (hnull : ∀ (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[F t] S)
    {N : Set Ω} (hN : P N = 0) {I : Set ℝ≥0} (hI : MeasurableSet I) :
    MeasurableSet[F.predictable] (I ×ˢ N) := by
  -- Transport `hI` to the `Ioi`-generated σ-algebra *before* any local
  -- `MeasurableSpace ℝ≥0` enters the context: a `let`-bound σ-algebra is a local
  -- instance and would shadow `NNReal.measurableSpace` in instance search.
  have hI' : MeasurableSet[MeasurableSpace.generateFrom
      (Set.range (Set.Ioi : ℝ≥0 → Set ℝ≥0))] I := by
    rw [← borel_eq_generateFrom_Ioi ℝ≥0, ← NNReal.borelSpace.measurable_eq]
    exact hI
  let 𝒞 : MeasurableSpace ℝ≥0 :=
    { MeasurableSet' := fun J => MeasurableSet[F.predictable] (J ×ˢ N)
      measurableSet_empty := by
        show MeasurableSet[F.predictable] ((∅ : Set ℝ≥0) ×ˢ N)
        rw [Set.empty_prod]
        exact @MeasurableSet.empty (ℝ≥0 × Ω) F.predictable
      measurableSet_compl := fun J hJ => by
        show MeasurableSet[F.predictable] (Jᶜ ×ˢ N)
        have hcompl : Jᶜ ×ˢ N = (univ : Set ℝ≥0) ×ˢ N \ J ×ˢ N := by
          ext p
          simp only [mem_prod, mem_compl_iff, mem_univ, true_and, mem_diff, not_and]
          tauto
        rw [hcompl]
        exact (measurableSet_predictable_univ_prod_of_null hnull hN).diff hJ
      measurableSet_iUnion := fun f hf => by
        show MeasurableSet[F.predictable] ((⋃ i, f i) ×ˢ N)
        rw [Set.iUnion_prod_const]
        exact MeasurableSet.iUnion hf }
  have hle : MeasurableSpace.generateFrom (Set.range (Set.Ioi : ℝ≥0 → Set ℝ≥0)) ≤ 𝒞 := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨i, rfl⟩
    show MeasurableSet[F.predictable] (Ioi i ×ˢ N)
    exact measurableSet_predictable_Ioi_prod (hnull i N hN)
  exact hle I hI'

/-- A set which is measurable for *some* product structure on `ℝ≥0 × Ω` becomes
predictable once it is cut down to a null event: on `ℝ≥0 × N` the predictable
σ-algebra already contains every Borel time set crossed with an arbitrary
subset of `N`. -/
theorem measurableSet_predictable_inter_null_prod
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {m₂ : MeasurableSpace Ω}
    (hnull : ∀ (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[F t] S)
    {N : Set Ω} (hN : P N = 0) {S : Set (ℝ≥0 × Ω)}
    (hS : MeasurableSet[@Prod.instMeasurableSpace ℝ≥0 Ω inferInstance m₂] S) :
    MeasurableSet[F.predictable] (S ∩ (univ : Set ℝ≥0) ×ˢ N) := by
  have hK : MeasurableSet[F.predictable] ((univ : Set ℝ≥0) ×ˢ N) :=
    measurableSet_predictable_univ_prod_of_null hnull hN
  let 𝒟 : MeasurableSpace (ℝ≥0 × Ω) :=
    { MeasurableSet' := fun T =>
        MeasurableSet[F.predictable] (T ∩ (univ : Set ℝ≥0) ×ˢ N)
      measurableSet_empty := by
        show MeasurableSet[F.predictable] (∅ ∩ (univ : Set ℝ≥0) ×ˢ N)
        rw [Set.empty_inter]
        exact @MeasurableSet.empty (ℝ≥0 × Ω) F.predictable
      measurableSet_compl := fun T hT => by
        show MeasurableSet[F.predictable] (Tᶜ ∩ (univ : Set ℝ≥0) ×ˢ N)
        have hcompl : Tᶜ ∩ (univ : Set ℝ≥0) ×ˢ N =
            (univ : Set ℝ≥0) ×ˢ N \ (T ∩ (univ : Set ℝ≥0) ×ˢ N) := by
          ext p
          simp only [mem_inter_iff, mem_compl_iff, mem_diff, not_and]
          tauto
        rw [hcompl]
        exact hK.diff hT
      measurableSet_iUnion := fun f hf => by
        show MeasurableSet[F.predictable] ((⋃ i, f i) ∩ (univ : Set ℝ≥0) ×ˢ N)
        rw [Set.iUnion_inter]
        exact MeasurableSet.iUnion hf }
  have hfst : MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace ℝ≥0) ≤ 𝒟 := by
    rintro T ⟨I, hI, rfl⟩
    show MeasurableSet[F.predictable] (Prod.fst ⁻¹' I ∩ (univ : Set ℝ≥0) ×ˢ N)
    have hrw : Prod.fst ⁻¹' I ∩ (univ : Set ℝ≥0) ×ˢ N = I ×ˢ N := by
      ext p
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and] <;> tauto
    rw [hrw]
    exact measurableSet_predictable_prod_of_null hnull hN hI
  have hsnd : MeasurableSpace.comap Prod.snd m₂ ≤ 𝒟 := by
    rintro T ⟨D, _, rfl⟩
    show MeasurableSet[F.predictable] (Prod.snd ⁻¹' D ∩ (univ : Set ℝ≥0) ×ˢ N)
    have hDN : P (D ∩ N) = 0 := measure_mono_null inter_subset_right hN
    have hrw : Prod.snd ⁻¹' D ∩ (univ : Set ℝ≥0) ×ˢ N = (univ : Set ℝ≥0) ×ˢ (D ∩ N) := by
      ext p
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and] <;> tauto
    rw [hrw]
    exact measurableSet_predictable_univ_prod_of_null hnull hDN
  exact (sup_le hfst hsnd) S hS

/-- **Predictability across an almost-sure modification.**  If the filtration
contains every null event of the law, if `A` is strongly predictable and if the
modification `B` agrees with `A` on one full-probability event simultaneously at
all times and is jointly measurable in `(t, ω)`, then `B` itself is strongly
predictable.  Joint measurability is only asked for *some* σ-algebra `m₂` on the
outcome space, so it may be verified in the uncompleted structure. -/
theorem isStronglyPredictable_of_ae_eq
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {m₂ : MeasurableSpace Ω}
    (hnull : ∀ (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[F t] S)
    {A B : ℝ≥0 → Ω → ℝ}
    (hA : IsStronglyPredictable F A)
    (hB : @Measurable (ℝ≥0 × Ω) ℝ (@Prod.instMeasurableSpace ℝ≥0 Ω inferInstance m₂)
      inferInstance (uncurry B))
    (hAB : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, A t ω = B t ω) :
    IsStronglyPredictable F B := by
  have hN : P {ω : Ω | ¬ ∀ t : ℝ≥0, A t ω = B t ω} = 0 := ae_iff.mp hAB
  unfold IsStronglyPredictable
  refine Measurable.stronglyMeasurable (f := uncurry B) ?_
  intro s hs
  have key : uncurry B ⁻¹' s =
      (uncurry B ⁻¹' s ∩ (univ : Set ℝ≥0) ×ˢ {ω : Ω | ¬ ∀ t : ℝ≥0, A t ω = B t ω}) ∪
        (uncurry A ⁻¹' s \ (univ : Set ℝ≥0) ×ˢ {ω : Ω | ¬ ∀ t : ℝ≥0, A t ω = B t ω}) := by
    ext p
    obtain ⟨r, ω⟩ := p
    by_cases hp : ¬ ∀ t : ℝ≥0, A t ω = B t ω
    · simp only [mem_preimage, mem_union, mem_inter_iff, mem_diff, mem_prod, mem_univ,
        mem_setOf_eq, true_and, hp, uncurry_apply_pair] <;> tauto
    · have heq : A r ω = B r ω := not_not.mp hp r
      simp only [mem_preimage, mem_union, mem_inter_iff, mem_diff, mem_prod, mem_univ,
        mem_setOf_eq, true_and, hp, uncurry_apply_pair, heq] <;> tauto
  rw [key]
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_predictable_inter_null_prod (m₂ := m₂) hnull hN (hB hs)
  · exact (hA.measurable hs).diff (measurableSet_predictable_univ_prod_of_null hnull hN)

/-- Predictability only depends on the levels of the filtration, and it is
monotone in them. -/
theorem isStronglyPredictable_mono {m₁ m₂ : MeasurableSpace Ω}
    {F : Filtration ℝ≥0 m₁} {H : Filtration ℝ≥0 m₂} (hFH : ∀ t : ℝ≥0, F t ≤ H t)
    {A : ℝ≥0 → Ω → ℝ} (hA : IsStronglyPredictable F A) :
    IsStronglyPredictable H A := by
  unfold IsStronglyPredictable at hA ⊢
  refine hA.mono (measurableSpace_le_predictable_of_measurableSet ?_ ?_)
  · exact fun S hS => measurableSet_predictable_singleton_bot_prod (hFH ⊥ S hS)
  · exact fun i S hS => measurableSet_predictable_Ioi_prod (hFH i S hS)

/-- **Right continuation is monotone in the filtration**, also across two
different ambient σ-algebras on the same outcome space.  Mathlib has no
monotonicity lemma for `MeasureTheory.Filtration.rightCont`; the project used
this argument only inside one proof
(`Forms/CompletedRightContinuousMartingaleTransfer.lean`).  On `ℝ≥0` no point is
isolated on the right, so `𝓕₊ t = ⨅ u > t, 𝓕 u` on both sides. -/
theorem rightCont_le_rightCont {m₁ m₂ : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 m₁) (H : Filtration ℝ≥0 m₂)
    (hFH : ∀ u : ℝ≥0, F u ≤ H u) (t : ℝ≥0) :
    F.rightCont t ≤ H.rightCont t := by
  rw [Filtration.rightCont_eq, Filtration.rightCont_eq]
  exact le_iInf₂ fun u hu => (iInf₂_le u hu).trans (hFH u)

/-- **An injective encoding into a discrete measurable space loses no
information.**  The σ-algebra generated by `f` is contained in the σ-algebra
generated by `enc ∘ f`, for *any* σ-algebra on the intermediate space: the
witness for a set `S` is its image `enc '' S`, which is measurable because the
target is discrete, and `enc ⁻¹' (enc '' S) = S` by injectivity. -/
theorem comap_le_comap_encode {α β γ : Type*} (mβ : MeasurableSpace β)
    {mγ : MeasurableSpace γ} [DiscreteMeasurableSpace γ] (f : α → β)
    {enc : β → γ} (henc : Function.Injective enc) :
    MeasurableSpace.comap f mβ ≤ MeasurableSpace.comap (fun a => enc (f a)) mγ := by
  rintro _ ⟨S, -, rfl⟩
  refine ⟨enc '' S, MeasurableSet.of_discrete, ?_⟩
  show (fun a => enc (f a)) ⁻¹' (enc '' S) = f ⁻¹' S
  rw [show (fun a => enc (f a)) ⁻¹' (enc '' S) = f ⁻¹' (enc ⁻¹' (enc '' S)) from rfl,
    Set.preimage_image_eq S henc]

end General

section Completed

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The a.e.-modification lemma in the shape `CanonicalBracket` consumes.**  On
the project's completed natural filtration, a jointly measurable process which
agrees almost surely, at all times, with a strongly predictable process is
itself strongly predictable.  The almost-sure hypothesis is stated for the
original law; the completed law has the same null sets. -/
theorem isStronglyPredictable_completedNaturalFiltration_of_ae_eq
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℕ) (hX : ∀ t, Measurable (X t))
    {A B : ℝ≥0 → Ω → ℝ}
    (hA : IsStronglyPredictable (ProcessFiltration.completedNaturalFiltration P X hX) A)
    (hB : Measurable (uncurry B))
    (hAB : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, A t ω = B t ω) :
    IsStronglyPredictable (ProcessFiltration.completedNaturalFiltration P X hX) B := by
  refine isStronglyPredictable_of_ae_eq (P := P.completion)
    (m₂ := (inferInstance : MeasurableSpace Ω))
    (fun t S hS =>
      ProcessFiltration.measurableSet_completedNaturalFiltration_of_null P X hX t S hS)
    hA hB ?_
  have h0 : P.completion {ω : NullMeasurableSpace Ω P | ¬ ∀ t : ℝ≥0, A t ω = B t ω} = 0 :=
    (Measure.completion_apply P _).trans (ae_iff.mp hAB)
  exact ae_iff.mpr h0

end Completed

section CodedFiltration

open ReflectedWalk ReflectedWalk.Theorem16

universe v

/-- **The natural filtration of a path is the natural filtration of any injective
code of it.**  `σ(X_s : s ≤ t)` — mathlib-free, as the pullback `pastSigma` of
the cylinder σ-algebra — is contained in `⨆ s ≤ t, σ(enc ∘ X_s)`, the sequence
underlying `MeasureTheory.Filtration.natural` for the ℕ-valued code.  The state
space `Option V` is discrete and `ℕ` is discrete, so injectivity of `enc` is the
only thing needed. -/
theorem pastSigma_le_iSup_comap_encode {V : Type v} {Ω : Type v}
    (X : ℝ≥0 → Ω → Option V) {enc : Option V → ℕ} (henc : Function.Injective enc)
    (t : ℝ≥0) :
    pastSigma X t ≤ ⨆ s : ℝ≥0, ⨆ _ : s ≤ t,
      MeasurableSpace.comap (fun ω => enc (X s ω)) (inferInstance : MeasurableSpace ℕ) := by
  -- Install the coded σ-algebra as *the* measurable structure of `Ω`, so that the
  -- pointwise criterion `measurable_pi_iff` reads it off instance search: `Ω`
  -- carries no other `MeasurableSpace` here, so nothing is shadowed.
  letI 𝒢 : MeasurableSpace Ω := ⨆ s : ℝ≥0, ⨆ _ : s ≤ t,
    MeasurableSpace.comap (fun ω => enc (X s ω)) (inferInstance : MeasurableSpace ℕ)
  have key : ∀ s : ℝ≥0, s ≤ t →
      MeasurableSpace.comap (X s) (inferInstance : MeasurableSpace (Option V)) ≤ 𝒢 := by
    intro s hs
    refine (comap_le_comap_encode (inferInstance : MeasurableSpace (Option V)) (X s) henc).trans ?_
    exact le_iSup₂ (f := fun (r : ℝ≥0) (_ : r ≤ t) =>
      MeasurableSpace.comap (fun ω => enc (X r ω))
        (inferInstance : MeasurableSpace ℕ)) s hs
  have hmeas : Measurable (pastPath X t) :=
    measurable_pi_iff.mpr fun s => measurable_iff_comap_le.mpr (key s.1 s.2)
  unfold pastSigma
  exact measurable_iff_comap_le.mp hmeas

/-- **The hypothesis `hdom`, discharged.**  The right continuation of the
natural filtration of the path is dominated by the project's completed natural
filtration of any *injective* ℕ-valued code of the same path.  This is exactly
the shape `InvarianceMainStatement.areaFiltration` produces, where the code is
`observedState = Encodable.encode`.  No regularity of the path is used. -/
theorem naturalFiltration_rightCont_le_completedNaturalFiltration {V : Type v}
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Option V) (hX : ∀ t : ℝ≥0, Measurable (X t))
    {enc : Option V → ℕ} (henc : Function.Injective enc)
    (hcode : ∀ t : ℝ≥0, Measurable fun ω => enc (X t ω)) (t : ℝ≥0) :
    (Theorem16.naturalFiltration X hX).rightCont t ≤
      ProcessFiltration.completedNaturalFiltration P (fun s ω => enc (X s ω)) hcode t := by
  unfold ProcessFiltration.completedNaturalFiltration
  dsimp only
  refine rightCont_le_rightCont _ _ (fun u => ?_) t
  refine le_trans ?_ (le_sup_left)
  exact pastSigma_le_iSup_comap_encode (Ω := NullMeasurableSpace Ω P) X henc u

end CodedFiltration

section OrdinaryEdgeBracket

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open MartingaleIngredients StatementIngredients

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

end OrdinaryEdgeBracket

end ReflectedGMS.PredictableCompletionModification
