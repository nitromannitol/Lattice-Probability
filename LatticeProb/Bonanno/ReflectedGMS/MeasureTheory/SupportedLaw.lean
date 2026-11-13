/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.MeasureTheory.SupportedLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.MeasureTheory.AENullSet
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option autoImplicit false

open MeasureTheory

namespace ReflectedGMS

variable {α : Type*} [MeasurableSpace α]

/-- A measurable core allows a map into a trace-measurable subtype even when the
subtype predicate itself is not measurable. -/
noncomputable def conullCoreMap (S C : Set α) (hCS : C ⊆ S) (d : S) : α → S := by
  classical
  exact fun x => ⟨if x ∈ C then x else d.1, by
    split_ifs with hx
    · exact hCS hx
    · exact d.2⟩

theorem measurable_conullCoreMap (S C : Set α) (hCS : C ⊆ S) (d : S)
    (hC : MeasurableSet C) : Measurable (conullCoreMap S C hCS d) := by
  classical
  unfold conullCoreMap
  apply Measurable.subtype_mk
  exact Measurable.ite hC measurable_id measurable_const

/-- The law on the valid subtype induced by a measurable conull core. -/
noncomputable def conullCoreLaw (μ : Measure α) (S C : Set α)
    (hCS : C ⊆ S) (d : S) : Measure S :=
  μ.map (conullCoreMap S C hCS d)

theorem map_conullCoreLaw (μ : Measure α) (S C : Set α)
    (hCS : C ⊆ S) (d : S) (hC : MeasurableSet C)
    (hCae : ∀ᵐ x ∂μ, x ∈ C) :
    (conullCoreLaw μ S C hCS d).map Subtype.val = μ := by
  classical
  rw [conullCoreLaw, Measure.map_map measurable_subtype_coe
    (measurable_conullCoreMap S C hCS d hC)]
  have h : (Subtype.val ∘ conullCoreMap S C hCS d) =ᵐ[μ] id := by
    filter_upwards [hCae] with x hx
    simp [conullCoreMap, hx]
  rw [Measure.map_congr h, Measure.map_id]

/-- Every almost-sure support predicate for a probability law supplies the core
and subtype inhabitant needed by the construction, without measurable validity. -/
theorem exists_supportedLaw_data (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Set α) (hS : ∀ᵐ x ∂μ, x ∈ S) :
    ∃ C : Set α, MeasurableSet C ∧ C ⊆ S ∧
      (∀ᵐ x ∂μ, x ∈ C) ∧ Nonempty S := by
  obtain ⟨N, hNm, hN0, hN⟩ :=
    (ae_iff_exists_measurable_null_set μ (fun x => x ∈ S)).mp hS
  refine ⟨Nᶜ, hNm.compl, hN, ?_, ?_⟩
  · exact measure_eq_zero_iff_ae_notMem.mp hN0
  · obtain ⟨x, hx⟩ := hS.exists
    exact ⟨⟨x, hx⟩⟩

/-- Auxiliary choices used to lift a supported law. They are proved to exist;
they are not extra assumptions in the eventual environment theorem. -/
structure SupportedLawData (μ : Measure α) (S : Set α) where
  core : Set α
  measurable_core : MeasurableSet core
  core_subset : core ⊆ S
  core_ae : ∀ᵐ x ∂μ, x ∈ core
  default : S

noncomputable def chosenSupportedLawData (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Set α) (hS : ∀ᵐ x ∂μ, x ∈ S) : SupportedLawData μ S :=
  let h := exists_supportedLaw_data μ S hS
  { core := Classical.choose h
    measurable_core := (Classical.choose_spec h).1
    core_subset := (Classical.choose_spec h).2.1
    core_ae := (Classical.choose_spec h).2.2.1
    default := Classical.choice (Classical.choose_spec h).2.2.2 }

/-- The actual probability law on an almost-surely valid subtype, with its trace
sigma algebra. No measurability of the validity predicate is required. -/
noncomputable def supportedLaw (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Set α) (hS : ∀ᵐ x ∂μ, x ∈ S) : Measure S :=
  let d := chosenSupportedLawData μ S hS
  conullCoreLaw μ S d.core d.core_subset d.default

instance supportedLaw_isProbability (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Set α) (hS : ∀ᵐ x ∂μ, x ∈ S) :
    IsProbabilityMeasure (supportedLaw μ S hS) := by
  unfold supportedLaw conullCoreLaw
  infer_instance

theorem map_supportedLaw (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Set α) (hS : ∀ᵐ x ∂μ, x ∈ S) :
    (supportedLaw μ S hS).map Subtype.val = μ := by
  let d := chosenSupportedLawData μ S hS
  exact map_conullCoreLaw μ S d.core d.core_subset d.default
    d.measurable_core d.core_ae

/-- Ambient inclusion determines every trace-measurable set, even for a
nonmeasurable subtype predicate. This avoids any measurable-embedding claim. -/
theorem subtype_measure_eq_of_map_eq (S : Set α) (ν ρ : Measure S)
    (h : ν.map Subtype.val = ρ.map Subtype.val) : ν = ρ := by
  ext t ht
  rcases ht with ⟨u, hu, rfl⟩
  simpa only [Measure.map_apply measurable_subtype_coe hu] using
    congrArg (fun m : Measure α => m u) h

theorem supportedLaw_unique (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Set α) (hS : ∀ᵐ x ∂μ, x ∈ S) (ν : Measure S)
    (hν : ν.map Subtype.val = μ) : ν = supportedLaw μ S hS := by
  apply subtype_measure_eq_of_map_eq S
  exact hν.trans (map_supportedLaw μ S hS).symm

end ReflectedGMS
