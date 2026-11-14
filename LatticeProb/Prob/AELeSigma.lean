/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.CondIndepEvChain

/-!
# Containment of sigma-algebras up to null sets

`AELeSigma A A' μ` says that every event of `A` agrees almost surely with an event of `A'`.  The
events almost surely equal to an event of `A'` form a σ-algebra `aeClosure A' μ`, so that
`AELeSigma A A' μ` is the order relation `A ≤ aeClosure A' μ`.  Consequently the relation is
stable under suprema (`AELeSigma.sup`, `AELeSigma.iSup`), and it holds for `comap f` as soon as `f`
agrees almost surely with an `A'`-measurable function (`AELeSigma.comap_of_ae_eq`).
-/

open MeasureTheory MeasurableSpace Filter Set

namespace LatticeProb

variable {Ω : Type*} {A A₁ A₂ A' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The σ-algebra of events that agree almost surely with an event of `A'`. -/
@[instance_reducible]
def aeClosure (A' : MeasurableSpace Ω) (μ : Measure[mΩ] Ω) : MeasurableSpace Ω where
  MeasurableSet' a := ∃ a', MeasurableSet[A'] a' ∧ a =ᵐ[μ] a'
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ A', Filter.EventuallyEq.rfl⟩
  measurableSet_compl := by
    rintro a ⟨a', h, hae⟩
    exact ⟨a'ᶜ, h.compl, hae.compl⟩
  measurableSet_iUnion := by
    intro f hf
    choose g hg hae using hf
    exact ⟨⋃ n, g n, MeasurableSet.iUnion hg, EventuallyEqSet.countable_iUnion hae⟩

theorem aeLeSigma_iff_le : AELeSigma A A' μ ↔ A ≤ aeClosure A' μ := Iff.rfl

theorem AELeSigma.of_le (h : A ≤ A') : AELeSigma A A' μ :=
  fun a ha => ⟨a, h _ ha, Filter.EventuallyEq.rfl⟩

theorem AELeSigma.sup (h₁ : AELeSigma A₁ A' μ) (h₂ : AELeSigma A₂ A' μ) :
    AELeSigma (A₁ ⊔ A₂) A' μ :=
  aeLeSigma_iff_le.2 (sup_le (aeLeSigma_iff_le.1 h₁) (aeLeSigma_iff_le.1 h₂))

theorem AELeSigma.iSup {ι : Sort*} {B : ι → MeasurableSpace Ω} (h : ∀ i, AELeSigma (B i) A' μ) :
    AELeSigma (⨆ i, B i) A' μ :=
  aeLeSigma_iff_le.2 (iSup_le fun i => aeLeSigma_iff_le.1 (h i))

theorem AELeSigma.iSup_prop {p : Prop} (h : p → AELeSigma A A' μ) :
    AELeSigma (⨆ _ : p, A) A' μ := by
  by_cases hp : p
  · rw [iSup_pos hp]
    exact h hp
  · rw [iSup_neg hp]
    exact AELeSigma.of_le bot_le

/-- `comap f` is contained in `A'` up to null sets when `f` agrees almost surely with an
`A'`-measurable function. -/
theorem AELeSigma.comap_of_ae_eq {β : Type*} [MeasurableSpace β] {f g : Ω → β}
    (hg : Measurable[A'] g) (h : f =ᵐ[μ] g) :
    AELeSigma (MeasurableSpace.comap f inferInstance) A' μ := by
  rintro a ⟨s, hs, rfl⟩
  refine ⟨g ⁻¹' s, hg hs, ?_⟩
  filter_upwards [h] with x hx
  show (f x ∈ s) = (g x ∈ s)
  rw [hx]

end LatticeProb
