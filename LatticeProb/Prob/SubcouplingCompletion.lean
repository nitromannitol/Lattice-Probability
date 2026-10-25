module

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/SubcouplingCompletion.lean
-/
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Sub

@[expose] public section

/-!
# Completing a finite matched coupling by an actual product measure

A partial coupling with dominated marginals is completed using the product of
its two residual marginals, normalized by their common mass. This includes the
zero-residual case.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- The product measure `α.prod β` rescaled by the inverse of the total mass of `α`.
When `α` and `β` are finite with equal total mass, the marginals of this measure are
`α` and `β` (`balancedProduct_fst` and `balancedProduct_snd`). If `α` is zero, the
result is zero. -/
noncomputable def balancedProduct {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (α : Measure X) (β : Measure Y) : Measure (X × Y) :=
  (α univ)⁻¹ • α.prod β

/-- The first marginal of `balancedProduct α β` is `α`, when `α` and `β` are finite
with equal total mass. -/
lemma balancedProduct_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (α : Measure X) (β : Measure Y) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (hmass : β univ = α univ) : (balancedProduct α β).fst = α := by
  by_cases hzero : α univ = 0
  · have hα : α = 0 := Measure.measure_univ_eq_zero.mp hzero
    simp [balancedProduct, hα]
  · rw [balancedProduct, Measure.fst, Measure.map_smul, Measure.map_fst_prod,
      hmass, smul_smul, ENNReal.inv_mul_cancel hzero (measure_ne_top α univ), one_smul]

/-- The second marginal of `balancedProduct α β` is `β`, when `α` and `β` are finite
with equal total mass. -/
lemma balancedProduct_snd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (α : Measure X) (β : Measure Y) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (hmass : β univ = α univ) : (balancedProduct α β).snd = β := by
  by_cases hzero : α univ = 0
  · have hα : α = 0 := Measure.measure_univ_eq_zero.mp hzero
    have hβ : β = 0 := Measure.measure_univ_eq_zero.mp (hmass.trans hzero)
    simp [balancedProduct, hα, hβ]
  · rw [balancedProduct, Measure.snd, Measure.map_smul, Measure.map_snd_prod,
      smul_smul, ENNReal.inv_mul_cancel hzero (measure_ne_top α univ), one_smul]

/-- Completion of the partial coupling `ρ` of `μ` and `ν`: `ρ` plus the balanced
product of the residual marginals `μ - ρ.fst` and `ν - ρ.snd`. -/
noncomputable def completeSubcoupling {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y)) : Measure (X × Y) :=
  ρ + balancedProduct (μ - ρ.fst) (ν - ρ.snd)

/-- The two residual marginals of a partial coupling dominated by `μ` and `ν` have
equal total mass. -/
private lemma residual_masses_eq {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (hfst : ρ.fst ≤ μ) (hsnd : ρ.snd ≤ ν) :
    (ν - ρ.snd) univ = (μ - ρ.fst) univ := by
  rw [Measure.sub_apply MeasurableSet.univ hsnd,
    Measure.sub_apply MeasurableSet.univ hfst, measure_univ (μ := μ), measure_univ (μ := ν),
    Measure.fst_univ, Measure.snd_univ]

/-- The completion of a partial coupling has first marginal `μ`, when its marginals
are dominated by `μ` and `ν`. -/
lemma completeSubcoupling_fst {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (hfst : ρ.fst ≤ μ) (hsnd : ρ.snd ≤ ν) :
    (completeSubcoupling μ ν ρ).fst = μ := by
  rw [completeSubcoupling, Measure.fst_add,
    balancedProduct_fst _ _ (residual_masses_eq μ ν ρ hfst hsnd),
    add_comm, Measure.sub_add_cancel_of_le hfst]

/-- The completion of a partial coupling has second marginal `ν`, when its marginals
are dominated by `μ` and `ν`. -/
lemma completeSubcoupling_snd {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (hfst : ρ.fst ≤ μ) (hsnd : ρ.snd ≤ ν) :
    (completeSubcoupling μ ν ρ).snd = ν := by
  rw [completeSubcoupling, Measure.snd_add,
    balancedProduct_snd _ _ (residual_masses_eq μ ν ρ hfst hsnd),
    add_comm, Measure.sub_add_cancel_of_le hsnd]

/-- The completion of a partial coupling is a probability measure, when its marginals
are dominated by `μ` and `ν`. -/
lemma completeSubcoupling_isProbabilityMeasure {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (hfst : ρ.fst ≤ μ) (hsnd : ρ.snd ≤ ν) :
    IsProbabilityMeasure (completeSubcoupling μ ν ρ) where
  measure_univ := by
    rw [← Measure.fst_univ, completeSubcoupling_fst μ ν ρ hfst hsnd, measure_univ]

/-- Any event `B` that the partial coupling `ρ` does not charge has probability at most
the unmatched mass `1 - ρ univ` in the completed coupling. No existence of a coupling
of `μ` and `ν` is assumed. -/
theorem completeSubcoupling_bad_event_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (hfst : ρ.fst ≤ μ) (hsnd : ρ.snd ≤ ν)
    {B : Set (X × Y)} (hB : ρ B = 0) :
    completeSubcoupling μ ν ρ B ≤ 1 - ρ univ := by
  rw [completeSubcoupling, Measure.add_apply, hB, zero_add]
  calc
    balancedProduct (μ - ρ.fst) (ν - ρ.snd) B ≤
        balancedProduct (μ - ρ.fst) (ν - ρ.snd) univ := measure_mono (subset_univ B)
    _ = (μ - ρ.fst) univ := by
      rw [← Measure.fst_univ,
        balancedProduct_fst _ _ (residual_masses_eq μ ν ρ hfst hsnd)]
    _ = 1 - ρ univ := by
      rw [Measure.sub_apply MeasurableSet.univ hfst, measure_univ, Measure.fst_univ]

/-! ### Nonvacuity examples on `Bool`

Two different probability measures on `Bool`, a nonzero subcoupling below both of
their marginals, and the completion evaluated for these data. -/

namespace SubcouplingCompletionExample

/-- The uniform probability measure on `Bool`. -/
noncomputable def exampleLeft : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac true + (2⁻¹ : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure exampleLeft :=
  ⟨by
    simp only [exampleLeft, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ true), Measure.dirac_apply_of_mem (mem_univ false),
      smul_eq_mul, mul_one, ENNReal.inv_two_add_inv_two]⟩

/-- The point mass at `true`, a probability measure on `Bool` different from
`exampleLeft`. -/
noncomputable def exampleRight : Measure Bool := Measure.dirac true

instance : IsProbabilityMeasure exampleRight :=
  inferInstanceAs (IsProbabilityMeasure (Measure.dirac true))

/-- The two example measures on `Bool` are different: they give `{true}` the masses
`2⁻¹` and `1`. -/
theorem exampleLeft_ne_exampleRight : exampleLeft ≠ exampleRight := by
  intro h
  have h1 : exampleLeft {true} = 2⁻¹ := by
    have hnot : false ∉ ({true} : Set Bool) := by simp
    simp only [exampleLeft, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_singleton true),
      (dirac_eq_zero_iff_not_mem (measurableSet_singleton true)).2 hnot,
      smul_eq_mul, mul_one, mul_zero, add_zero]
  have h2 : exampleRight {true} = 1 := Measure.dirac_apply_of_mem (mem_singleton true)
  rw [h, h2] at h1
  exact ne_of_lt (ENNReal.inv_lt_one.2 ENNReal.one_lt_two) h1.symm

/-- The nonzero subcoupling `2⁻¹ • δ_(true, true)` on `Bool × Bool`. -/
noncomputable def exampleCoupling : Measure (Bool × Bool) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac (true, true)

/-- The total mass of `exampleCoupling` is `2⁻¹`. -/
theorem exampleCoupling_univ : exampleCoupling univ = 2⁻¹ := by
  rw [exampleCoupling, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _),
    smul_eq_mul, mul_one]

instance : IsFiniteMeasure exampleCoupling :=
  ⟨by rw [exampleCoupling_univ]; exact ENNReal.inv_lt_top.2 zero_lt_two⟩

/-- The first marginal of `exampleCoupling` is `2⁻¹ • δ_true`. -/
theorem exampleCoupling_fst : exampleCoupling.fst = (2⁻¹ : ℝ≥0∞) • Measure.dirac true := by
  rw [exampleCoupling, Measure.fst, Measure.map_smul, Measure.map_dirac' measurable_fst]

/-- The second marginal of `exampleCoupling` is `2⁻¹ • δ_true`. -/
theorem exampleCoupling_snd : exampleCoupling.snd = (2⁻¹ : ℝ≥0∞) • Measure.dirac true := by
  rw [exampleCoupling, Measure.snd, Measure.map_smul, Measure.map_dirac' measurable_snd]

/-- The first marginal of `exampleCoupling` is below `exampleLeft`. -/
theorem exampleCoupling_fst_le : exampleCoupling.fst ≤ exampleLeft := by
  rw [exampleCoupling_fst, exampleLeft]
  refine Measure.le_iff'.2 fun s => ?_
  simp

/-- The second marginal of `exampleCoupling` is below `exampleRight`. -/
theorem exampleCoupling_snd_le : exampleCoupling.snd ≤ exampleRight := by
  rw [exampleCoupling_snd]
  refine Measure.le_iff'.2 fun s => ?_
  rw [exampleRight, Measure.smul_apply, smul_eq_mul]
  exact mul_le_of_le_one_left zero_le (by norm_num)

/-- `exampleCoupling` gives no mass to the event `{p | p.1 = false}`. -/
theorem exampleCoupling_bad : exampleCoupling {p : Bool × Bool | p.1 = false} = 0 := by
  have hmeas : MeasurableSet {p : Bool × Bool | p.1 = false} := (Set.toFinite _).measurableSet
  have hnot : (true, true) ∉ {p : Bool × Bool | p.1 = false} := by simp
  rw [exampleCoupling, Measure.smul_apply, (dirac_eq_zero_iff_not_mem hmeas).2 hnot, smul_zero]

/-- Nonvacuity: the completion of `exampleCoupling` is a probability measure. -/
theorem exampleCompletion_isProbabilityMeasure :
    IsProbabilityMeasure (completeSubcoupling exampleLeft exampleRight exampleCoupling) :=
  completeSubcoupling_isProbabilityMeasure _ _ _ exampleCoupling_fst_le exampleCoupling_snd_le

/-- Nonvacuity: the completion of `exampleCoupling` has first marginal `exampleLeft`. -/
theorem exampleCompletion_fst :
    (completeSubcoupling exampleLeft exampleRight exampleCoupling).fst = exampleLeft :=
  completeSubcoupling_fst _ _ _ exampleCoupling_fst_le exampleCoupling_snd_le

/-- Nonvacuity: the completion of `exampleCoupling` has second marginal `exampleRight`. -/
theorem exampleCompletion_snd :
    (completeSubcoupling exampleLeft exampleRight exampleCoupling).snd = exampleRight :=
  completeSubcoupling_snd _ _ _ exampleCoupling_fst_le exampleCoupling_snd_le

/-- Nonvacuity: the completion of `exampleCoupling` gives `{p | p.1 = false}` mass at
most `2⁻¹`, the bound `1 - exampleCoupling univ` evaluated. -/
theorem exampleCompletion_bad_event :
    completeSubcoupling exampleLeft exampleRight exampleCoupling {p : Bool × Bool | p.1 = false}
      ≤ 2⁻¹ := by
  have h := completeSubcoupling_bad_event_le exampleLeft exampleRight exampleCoupling
    exampleCoupling_fst_le exampleCoupling_snd_le exampleCoupling_bad
  rwa [exampleCoupling_univ, ENNReal.one_sub_inv_two] at h

end SubcouplingCompletionExample

end LatticeProb
