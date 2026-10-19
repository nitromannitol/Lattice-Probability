/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedGMS/MeasureTheory/AENullSet.lean and ReflectedGMS/MeasureTheory/SupportedLaw.lean.
-/
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Laws supported on almost-sure sets

For a probability measure `μ` and a set `S` that contains `μ`-almost every point, this file
constructs the law of `μ` viewed as a measure on the subtype `S`. The subtype need not be
measurable: the construction goes through a measurable conull core `C ⊆ S`, on which `μ` gives
full mass, and a default point of `S` that fills the values outside `C`.

The main results are `supportedLaw`, which is a probability measure on `S` whose pushforward
along `Subtype.val` is `μ` (`map_supportedLaw`), and `supportedLaw_unique`, which says that
any measure on `S` with this pushforward equals `supportedLaw`. The file also contains a
nonvacuity example: a Dirac measure on a three-point type whose subset `{a, c}` is conull
but not measurable.
-/

open MeasureTheory

namespace LatticeProb

/-- An almost-everywhere predicate holds off one measurable null set.

No measurability assumption on the predicate is needed: in the forward direction,
`toMeasurable` supplies a measurable hull of its bad set without changing its measure. -/
theorem ae_iff_exists_measurable_null_set {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → Prop) :
    (∀ᵐ x ∂μ, p x) ↔
      ∃ N : Set α, MeasurableSet N ∧ μ N = 0 ∧ ∀ x, x ∉ N → p x := by
  constructor
  · intro hp
    let bad : Set α := {x | ¬p x}
    refine ⟨toMeasurable μ bad, measurableSet_toMeasurable μ bad, ?_, ?_⟩
    · rw [measure_toMeasurable]
      exact ae_iff.mp hp
    · intro x hxN
      by_contra hpx
      exact hxN (subset_toMeasurable μ bad hpx)
  · rintro ⟨N, _hNmeas, hNnull, hp⟩
    exact (measure_eq_zero_iff_ae_notMem.mp hNnull).mono hp

variable {α : Type*} [MeasurableSpace α]

/-- A measurable core allows a map into a trace-measurable subtype even when the
subtype predicate itself is not measurable. -/
noncomputable def conullCoreMap (S C : Set α) (hCS : C ⊆ S) (d : S) : α → S := by
  classical
  exact fun x => ⟨if x ∈ C then x else d.1, by
    split_ifs with hx
    · exact hCS hx
    · exact d.2⟩

/-- The map `conullCoreMap S C hCS d` is measurable when the core `C` is measurable. -/
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

/-- Pushing the conull core law forward along the subtype inclusion recovers `μ`, provided
the core is measurable and contains `μ`-almost every point. -/
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

/-- Auxiliary choices used to lift a supported law: a measurable core inside `S` that
carries full `μ`-mass, and a default point of `S`. They are proved to exist, so they add no
hypotheses to the statements that use them. -/
structure SupportedLawData (μ : Measure α) (S : Set α) where
  /-- A measurable subset of `S` on which `μ` gives full mass. -/
  core : Set α
  /-- The core is measurable. -/
  measurable_core : MeasurableSet core
  /-- The core lies inside `S`. -/
  core_subset : core ⊆ S
  /-- Almost every point of `μ` lies in the core. -/
  core_ae : ∀ᵐ x ∂μ, x ∈ core
  /-- A point of `S` used as the value outside the core. -/
  default : S

/-- Chosen supported-law data, obtained from `exists_supportedLaw_data`. -/
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

/-- The supported law is a probability measure. -/
instance supportedLaw_isProbability (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Set α) (hS : ∀ᵐ x ∂μ, x ∈ S) :
    IsProbabilityMeasure (supportedLaw μ S hS) := by
  let d := chosenSupportedLawData μ S hS
  unfold supportedLaw conullCoreLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_conullCoreMap S d.core d.core_subset d.default d.measurable_core).aemeasurable

/-- The pushforward of the supported law along the subtype inclusion is `μ`. -/
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

/-- Any measure on the subtype `S` whose pushforward to `α` is `μ` equals the supported law. -/
theorem supportedLaw_unique (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Set α) (hS : ∀ᵐ x ∂μ, x ∈ S) (ν : Measure S)
    (hν : ν.map Subtype.val = μ) : ν = supportedLaw μ S hS := by
  apply subtype_measure_eq_of_map_eq S
  exact hν.trans (map_supportedLaw μ S hS).symm

/-! ## Nonvacuity

The three-point type `Three` carries the σ-algebra that sees only `Three.c` against
`{Three.a, Three.b}`. Its Dirac measure at `Three.c` gives the set `{Three.a, Three.c}` full
mass without that set being measurable, so the theorems above apply to a genuinely
nonmeasurable support. -/

namespace SupportedLawExample

/-- Three points, of which only the last is separated from the first two. -/
inductive Three where
  | a
  | b
  | c

/-- The two-valued flag that determines the measurable structure on `Three`. -/
def threeFlag : Three → Bool
  | .a => false
  | .b => false
  | .c => true

/-- The σ-algebra on `Three` generated by the flag, so that its measurable sets are the
preimages of Boolean sets. -/
instance threeMeasurableSpace : MeasurableSpace Three :=
  MeasurableSpace.comap threeFlag ⊤

/-- The set `{a, b}` is measurable: it is the preimage of `{false}`. -/
theorem measurableSet_ab : MeasurableSet ({Three.a, Three.b} : Set Three) := by
  refine MeasurableSpace.measurableSet_comap.2 ⟨{false}, MeasurableSpace.measurableSet_top, ?_⟩
  ext x
  cases x <;> simp [threeFlag]

/-- The set `{a, c}` is not measurable. -/
theorem not_measurableSet_ac : ¬ MeasurableSet ({Three.a, Three.c} : Set Three) := by
  intro h
  obtain ⟨s, -, hs⟩ := MeasurableSpace.measurableSet_comap.1 h
  have h1 : Three.a ∈ threeFlag ⁻¹' s := by rw [hs]; simp
  have h2 : Three.b ∉ threeFlag ⁻¹' s := by rw [hs]; simp
  exact h2 (by simpa [threeFlag] using h1)

/-- The Dirac mass at `c` gives `{a, b}` zero mass. -/
theorem dirac_c_ab_eq_zero : Measure.dirac Three.c ({Three.a, Three.b} : Set Three) = 0 := by
  rw [Measure.dirac_apply' _ measurableSet_ab, Set.indicator_of_notMem (by simp)]

/-- The set `{a, c}` is conull for the Dirac mass at `c`, though it is not measurable. -/
theorem ae_mem_ac :
    ∀ᵐ x ∂(Measure.dirac Three.c), x ∈ ({Three.a, Three.c} : Set Three) := by
  refine (ae_iff_exists_measurable_null_set _ _).2
    ⟨{Three.a, Three.b}, measurableSet_ab, dirac_c_ab_eq_zero, ?_⟩
  intro x hx
  cases x <;> simp_all

/-- The supported law on the nonmeasurable set `{a, c}` exists and has the required
pushforward. -/
example :
    (supportedLaw (Measure.dirac Three.c) {Three.a, Three.c} ae_mem_ac).map Subtype.val =
      Measure.dirac Three.c :=
  map_supportedLaw _ _ _

/-- The subtype data for the nonmeasurable set `{a, c}` exist. -/
example : ∃ C : Set Three, MeasurableSet C ∧ C ⊆ {Three.a, Three.c} ∧
    (∀ᵐ x ∂(Measure.dirac Three.c), x ∈ C) ∧ Nonempty ({Three.a, Three.c} : Set Three) :=
  exists_supportedLaw_data _ _ ae_mem_ac

/-- The uniqueness theorem applies: any measure on `{a, c}` pushing forward to the Dirac mass
at `c` equals the supported law. -/
example (ν : Measure ({Three.a, Three.c} : Set Three))
    (hν : ν.map Subtype.val = Measure.dirac Three.c) :
    ν = supportedLaw (Measure.dirac Three.c) {Three.a, Three.c} ae_mem_ac :=
  supportedLaw_unique _ _ _ ν hν

end SupportedLawExample

end LatticeProb
