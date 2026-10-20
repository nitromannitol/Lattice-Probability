/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Statement/Metric.lean.
Source: LQGMetric/Prob/CondIndepAEDet.lean.
-/

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import LatticeProb.Prob.CondIndepDetermined

/-!
# Almost-sure determination of one random variable by another

`AEDeterminedBy Y X P` says that `Y` is almost surely a measurable function of `X` under `P`: there
is a measurable `F` with `Y = F ∘ X` `P`-almost surely.

The σ-algebra notion `AEDeterminedSigma` from `LatticeProb.Prob.CondIndepDetermined` gives this
random-variable notion when the target `β` is standard Borel: if `σ(Y)` is almost surely determined
by `σ(X)`, then `Y` is almost surely a measurable function of `X`.

Main results:
* `LatticeProb.exists_ae_eq_measurable_of_aeDeterminedSigma`: if `σ(Y)` is almost surely determined
  by a σ-algebra `G`, then `Y` agrees almost surely with a `G`-measurable random variable.
* `LatticeProb.aeDeterminedBy_of_aeDeterminedSigma`: if `σ(Y)` is almost surely determined by
  `σ(X)`, then `AEDeterminedBy Y X` holds.
* `LatticeProb.aeDeterminedBy_of_condIndepEv_of_ae_eq`: the two-copies criterion in
  `AEDeterminedBy` form: if `D` and `D'` are conditionally independent given `σ(X)` and `D = D'`
  almost surely, then `AEDeterminedBy D X` holds.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LatticeProb

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `AEDeterminedBy Y X P` says that `Y` is almost surely a measurable function of `X` under `P`:
there is a measurable `F` such that `Y = F ∘ X` holds `P`-almost surely. -/
def AEDeterminedBy {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Y : Ω → β) (X : Ω → α) (P : Measure Ω) : Prop :=
  ∃ F : α → β, Measurable F ∧ Y =ᵐ[P] F ∘ X

end

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If `σ(Y)` is almost surely determined by the σ-algebra `G` and `β` is standard Borel, then `Y`
agrees almost surely with a `G`-measurable random variable `Y'`. -/
theorem exists_ae_eq_measurable_of_aeDeterminedSigma {β : Type*} [mβ : MeasurableSpace β]
    [StandardBorelSpace β] [Nonempty β] {G : MeasurableSpace Ω} {Y : Ω → β}
    (h : AEDeterminedSigma (mβ.comap Y) G μ) :
    ∃ Y' : Ω → β, Measurable[G] Y' ∧ Y =ᵐ[μ] Y' := by
  classical
  obtain ⟨ψ, hψm, hψi⟩ := measurable_injection_nat_bool_of_countablySeparated β
  have hψe : MeasurableEmbedding ψ := hψm.measurableEmbedding hψi
  obtain ⟨g, hgm, hg⟩ := hψe.exists_measurable_extend measurable_id fun _ => inferInstance
  have hB : ∀ n, MeasurableSet[mβ] {b | ψ b n = true} := fun n =>
    ((measurable_pi_apply n).comp hψm) (measurableSet_singleton true)
  choose C hC hYC using fun n => h (Y ⁻¹' {b | ψ b n = true}) ⟨_, hB n, rfl⟩
  let Φ : Ω → ℕ → Bool := fun ω n => decide (ω ∈ C n)
  have hΦ : Measurable[G] Φ := by
    refine measurable_pi_iff.2 fun n => measurable_to_countable' fun x => ?_
    cases x
    · convert (hC n).compl using 1
      ext ω; simp [Φ]
    · convert hC n using 1
      ext ω; simp [Φ]
  have hae : ∀ᵐ ω ∂μ, ψ (Y ω) = Φ ω := by
    have hall : ∀ᵐ ω ∂μ, ∀ n, (ω ∈ Y ⁻¹' {b | ψ b n = true} ↔ ω ∈ C n) :=
      ae_all_iff.2 fun n => eventuallyEq_set.1 (hYC n)
    filter_upwards [hall] with ω hω
    funext n
    have := hω n
    simp only [mem_preimage, mem_setOf_eq] at this
    by_cases hc : ω ∈ C n
    · simpa [Φ, this.2 hc] using hc
    · have : ψ (Y ω) n ≠ true := fun h' => hc (this.1 h')
      simp [Φ, hc] at this ⊢
      exact this
  refine ⟨g ∘ Φ, hgm.comp hΦ, ?_⟩
  filter_upwards [hae] with ω hω
  simp only [Function.comp_apply, ← hω]
  exact (congrFun hg (Y ω)).symm

/-- If `σ(Y)` is almost surely determined by `σ(X)` and `β` is standard Borel, then `Y` is almost
surely a measurable function of `X`, that is `AEDeterminedBy Y X μ`. -/
theorem aeDeterminedBy_of_aeDeterminedSigma {α β : Type*} [mα : MeasurableSpace α]
    [mβ : MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] {X : Ω → α} {Y : Ω → β}
    (h : AEDeterminedSigma (mβ.comap Y) (mα.comap X) μ) : AEDeterminedBy Y X μ := by
  obtain ⟨Y', hY'm, hYY'⟩ := exists_ae_eq_measurable_of_aeDeterminedSigma h
  obtain ⟨F, hF, rfl⟩ := hY'm.exists_eq_measurable_comp
  exact ⟨F, hF, hYY'⟩

/-- Two-copies criterion in `AEDeterminedBy` form. Let `X` and `D` be measurable, `D'` arbitrary,
and the target `β` standard Borel and nonempty. If `D` and `D'` are conditionally independent given
`σ(X)` (in event form, `CondIndepEv`) and `D = D'` almost surely, then `D` is almost surely a
measurable function of `X`. -/
theorem aeDeterminedBy_of_condIndepEv_of_ae_eq [IsProbabilityMeasure μ] {α β : Type*}
    [mα : MeasurableSpace α] [mβ : MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    {X : Ω → α} (hX : Measurable[mΩ] X) {D D' : Ω → β} (hD : Measurable[mΩ] D)
    (hDD' : CondIndepEv (mα.comap X) (mβ.comap D) (mβ.comap D') μ) (heq : D =ᵐ[μ] D') :
    AEDeterminedBy D X μ :=
  aeDeterminedBy_of_aeDeterminedSigma
    (aeDeterminedSigma_of_condIndepEv_of_ae_eq hX.comap_le hD hDD' heq)

namespace AEDeterminedByExample

/-- The hypotheses of `aeDeterminedBy_of_condIndepEv_of_ae_eq` hold on the two-point space
`(Bool, coin)` with `X = D = D' = id`. The conditioning σ-algebra `σ(X)` is the full σ-algebra of
`Bool`, so the conditional independence is the trivial one, and `D = D'` holds trivially. -/
example : AEDeterminedBy (id : Bool → Bool) (id : Bool → Bool) AEDeterminedSigmaExample.coin := by
  refine aeDeterminedBy_of_condIndepEv_of_ae_eq measurable_id measurable_id ?_
    (EventuallyEq.refl _ _)
  rw [MeasurableSpace.comap_id]
  exact condIndepEv_top le_rfl le_rfl

end AEDeterminedByExample

end LatticeProb
