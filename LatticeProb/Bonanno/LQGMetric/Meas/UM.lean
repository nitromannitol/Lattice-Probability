/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Meas.UM at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Prob.CondIndepAEDet
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.G4CMeasLusin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Universally measurable events and "determined by" (decision D30 = D-C1, nodes F.MEAS-UM, F.MEAS-DET)

`decisions/DEC-C.md`, OD-1, items 2, 4, 5; signatures verbatim from its last section.

* `UMeasurableSet s`: `s` is null-measurable for every finite measure (universally measurable).
  API: measurable sets, complements, countable unions/intersections, s-finite measures,
  preimages under measurable and a.e.-measurable maps, the σ-algebra `umMeasurableSpace`.
* **Lusin**: images of Borel sets under measurable maps between standard Borel spaces
  (`UMeasurableSet.image`, `UMeasurableSet.image_fst`: "∃"), and their complements
  (`UMeasurableSet.forall_snd`: "∀ over a standard Borel parameter") are universally measurable.
  Source: Kechris, *Classical Descriptive Set Theory* (1995), Thm 21.10 (Lusin: analytic sets are
  universally measurable) and §14.A (Borel images are analytic; mathlib
  `MeasurableSet.analyticSet_image`). Lean: QuantumZipper
  `QuantumZipper.Thm18Asm.G4Core.analyticSet_nullMeasurableSet` (QZ/Proofs/Thm18/G4CMeasLusin.lean).
* `AEEventDeterminedBy E X P` ("`E` is a.s. an event of `σ(X)`", GM_B M2) with the bridge
  `AEEventDeterminedBy.iff_indicator` to FOUNDATIONS' `AEDeterminedBy`, `AEDeterminedBy.preimage`,
  its converse for standard Borel targets (`aeDeterminedBy_of_forall_preimage`, via the existing
  `LQGMetric.aeDeterminedBy_of_aeDeterminedSigma`), closure under complements and countable
  unions, monotonicity in `X`.
* `AESigmaLE m₁ m₂ P` (σ-algebra inclusion modulo null sets) = `AEDeterminedSigma`.
-/

open MeasureTheory MeasurableSpace Set Filter

namespace LQGMetric

/-- universally measurable: null-measurable for every finite measure -/
def UMeasurableSet {α : Type*} [MeasurableSpace α] (s : Set α) : Prop :=
  ∀ μ : Measure α, IsFiniteMeasure μ → NullMeasurableSet s μ

/-- an event is a.s. determined by `X`: a.s. equal to an event of `σ(X)` -/
def AEEventDeterminedBy {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (E : Set Ω) (X : Ω → α) (P : Measure Ω) : Prop :=
  ∃ S : Set α, MeasurableSet S ∧ E =ᵐ[P] X ⁻¹' S

/-- `m₁ ⊆ m₂` modulo `P`-null sets. (`P` is a measure for the ambient σ-algebra `mΩ`; in the
DEC-C text `(P : Measure Ω)` after the binders `m₁ m₂` would elaborate as a measure for `m₂`, the
last local instance, so the ambient instance is named here.) -/
def AESigmaLE {Ω : Type*} [mΩ : MeasurableSpace Ω] (m₁ m₂ : MeasurableSpace Ω)
    (P : Measure[mΩ] Ω) : Prop :=
  ∀ s, MeasurableSet[m₁] s → ∃ t, MeasurableSet[m₂] t ∧ s =ᵐ[P] t

namespace UMeasurableSet

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {s t : Set α}

theorem of_measurableSet (hs : MeasurableSet s) : UMeasurableSet s :=
  fun _ _ => hs.nullMeasurableSet
theorem empty : UMeasurableSet (∅ : Set α) := of_measurableSet MeasurableSet.empty

theorem compl (hs : UMeasurableSet s) : UMeasurableSet sᶜ := fun μ hμ => (hs μ hμ).compl

theorem iUnion {ι : Sort*} [Countable ι] {s : ι → Set α} (hs : ∀ i, UMeasurableSet (s i)) :
    UMeasurableSet (⋃ i, s i) := fun μ hμ => NullMeasurableSet.iUnion fun i => hs i μ hμ

theorem iInter {ι : Sort*} [Countable ι] {s : ι → Set α} (hs : ∀ i, UMeasurableSet (s i)) :
    UMeasurableSet (⋂ i, s i) := fun μ hμ => NullMeasurableSet.iInter fun i => hs i μ hμ
theorem union (hs : UMeasurableSet s) (ht : UMeasurableSet t) : UMeasurableSet (s ∪ t) :=
  fun μ hμ => (hs μ hμ).union (ht μ hμ)

theorem inter (hs : UMeasurableSet s) (ht : UMeasurableSet t) : UMeasurableSet (s ∩ t) :=
  fun μ hμ => (hs μ hμ).inter (ht μ hμ)

theorem diff (hs : UMeasurableSet s) (ht : UMeasurableSet t) : UMeasurableSet (s \ t) :=
  hs.inter ht.compl

/-- universally measurable sets are null-measurable for every s-finite measure -/
theorem nullMeasurableSet (hs : UMeasurableSet s) (μ : Measure α) [SFinite μ] :
    NullMeasurableSet s μ :=
  (hs μ.toFinite inferInstance).mono_ac (absolutelyContinuous_toFinite μ)

/-- preimages of universally measurable sets under measurable maps -/
theorem preimage {f : α → β} {u : Set β} (hu : UMeasurableSet u) (hf : Measurable f) :
    UMeasurableSet (f ⁻¹' u) :=
  fun μ _ => (hu (μ.map f) inferInstance).preimage (hf.quasiMeasurePreserving μ)

/-- the preimage of a universally measurable set under an a.e.-measurable random variable is a
null-measurable event (law = finite measure) -/
theorem nullMeasurableSet_preimage {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → β} {u : Set β} (hu : UMeasurableSet u) (hf : AEMeasurable f P) :
    NullMeasurableSet (f ⁻¹' u) P := by
  have h1 : NullMeasurableSet (hf.mk f ⁻¹' u) P :=
    (hu (P.map (hf.mk f)) inferInstance).preimage (hf.measurable_mk.quasiMeasurePreserving P)
  refine h1.congr ?_
  filter_upwards [hf.ae_eq_mk] with ω hω
  simp [hω]

/-- **Lusin** (Kechris Thm 21.10; QZ `analyticSet_nullMeasurableSet`): the image of a Borel set
under a measurable map between standard Borel spaces is universally measurable. -/
theorem image [StandardBorelSpace α] [StandardBorelSpace β] {f : α → β} (hf : Measurable f)
    (hs : MeasurableSet s) : UMeasurableSet (f '' s) := by
  intro μ _
  let := upgradeStandardBorel β
  exact QuantumZipper.Thm18Asm.G4Core.analyticSet_nullMeasurableSet
    (hs.analyticSet_image hf) μ

/-- "∃": the projection of a Borel relation between standard Borel spaces is universally
measurable. -/
theorem image_fst [StandardBorelSpace α] [StandardBorelSpace β] {S : Set (α × β)}
    (hS : MeasurableSet S) : UMeasurableSet (Prod.fst '' S) :=
  image measurable_fst hS

/-- "∃" in set-builder form. -/
theorem setOf_exists [StandardBorelSpace α] [StandardBorelSpace β] {S : Set (α × β)}
    (hS : MeasurableSet S) : UMeasurableSet {a | ∃ b, (a, b) ∈ S} := by
  convert image_fst hS using 1
  ext a; simp

/-- "∀ over a standard Borel parameter": coanalytic, hence universally measurable. -/
theorem setOf_forall [StandardBorelSpace α] [StandardBorelSpace β] {S : Set (α × β)}
    (hS : MeasurableSet S) : UMeasurableSet {a | ∀ b, (a, b) ∈ S} := by
  have h := (setOf_exists hS.compl).compl
  convert h using 1
  ext a; simp

end UMeasurableSet

/-! ### "Determined by" -/

namespace AEEventDeterminedBy

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {P : Measure Ω} {X : Ω → α} {E F : Set Ω}

theorem of_measurableSet {S : Set α} (hS : MeasurableSet S) :
    AEEventDeterminedBy (X ⁻¹' S) X P := ⟨S, hS, ae_eq_refl _⟩

theorem congr (h : AEEventDeterminedBy E X P) (hEF : E =ᵐ[P] F) : AEEventDeterminedBy F X P := by
  obtain ⟨S, hS, hE⟩ := h
  exact ⟨S, hS, hEF.symm.trans hE⟩

theorem union (hE : AEEventDeterminedBy E X P) (hF : AEEventDeterminedBy F X P) :
    AEEventDeterminedBy (E ∪ F) X P := by
  obtain ⟨S, hS, h1⟩ := hE
  obtain ⟨T, hT, h2⟩ := hF
  exact ⟨S ∪ T, hS.union hT, h1.union h2⟩

end AEEventDeterminedBy

section Det

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {P : Measure Ω} {X : Ω → α}

end Det

section SigmaLE

variable {Ω α : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω}

theorem AESigmaLE.trans {m₁ m₂ m₃ : MeasurableSpace Ω} (h₁ : @AESigmaLE Ω mΩ m₁ m₂ P)
    (h₂ : @AESigmaLE Ω mΩ m₂ m₃ P) : @AESigmaLE Ω mΩ m₁ m₃ P := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := h₁ s hs
  obtain ⟨u, hu, htu⟩ := h₂ t ht
  exact ⟨u, hu, hst.trans htu⟩

end SigmaLE

end LQGMetric
