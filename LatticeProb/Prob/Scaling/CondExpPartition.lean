/-
A conditional expectation determined by matching a candidate on every piece of a countable
partition of the sub-σ-algebra. `Ω` is an arbitrary measurable space, `m ≤ m₀` an arbitrary
sub-σ-algebra, `μ` an arbitrary probability measure, and `sel : Ω → K` an arbitrary
`m`-measurable, countable-valued observable that decides which piece of the partition a point
falls in.

Useful for upgrading a conditional mean known on each piece of a countable partition to the
conditional expectation of the whole sub-σ-algebra, for instance a martingale increment whose
range of summation is itself random but determined by the smaller σ-algebra.

Moved from Parking-Sharpness.
-/
import Mathlib

open MeasureTheory

noncomputable section

namespace LatticeProb.Scaling.CondExpPartition

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **A conditional expectation determined on a countable partition is the conditional
expectation.**  If a candidate `g`, `m`-measurable, matches `Φ`'s integral on every
`m`-measurable set confined to one piece of a countable partition `sel⁻¹{κ}` (`κ : K`), then
`g` is (a version of) the conditional expectation of `Φ` with respect to `m`.  General
countable-additivity assembly; no probabilistic content beyond `Countable K`. -/
theorem condExp_of_countable_partition [IsProbabilityMeasure μ] (hm : m ≤ m₀)
    {K : Type*} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (sel : Ω → K) (hsel : Measurable[m] sel)
    (Φ g : Ω → ℝ) (hΦ : Integrable Φ μ)
    (hgmeas : Measurable[m] g) (hgint : Integrable g μ)
    (heq : ∀ κ : K, ∀ S : Set Ω, MeasurableSet[m] S →
        S ⊆ {ω | sel ω = κ} →
        ∫ ω, S.indicator Φ ω ∂μ = ∫ ω, S.indicator g ω ∂μ) :
    μ[Φ | m] =ᵐ[μ] g := by
  classical
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hΦ
    (fun S _ _ => hgint.integrableOn) ?_ hgmeas.aestronglyMeasurable).symm
  intro S hS _
  have hpart : S = ⋃ κ : K, S ∩ sel ⁻¹' {κ} := by
    ext ω; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨sel ω, h, rfl⟩, fun ⟨κ, h, _⟩ => h⟩
  have hmeasS : ∀ κ : K, MeasurableSet[m] (S ∩ sel ⁻¹' {κ}) :=
    fun κ => hS.inter (hsel (measurableSet_singleton κ))
  have hmeasSamb : ∀ κ : K, MeasurableSet (S ∩ sel ⁻¹' {κ}) := fun κ => hm _ (hmeasS κ)
  have hdisj : Pairwise (Function.onFun Disjoint fun κ : K => S ∩ sel ⁻¹' {κ}) := by
    intro κ κ' hκκ'
    refine Set.disjoint_left.mpr fun ω hωκ hωκ' => hκκ' ?_
    rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hωκ hωκ'
    rw [← hωκ.2, ← hωκ'.2]
  have hEq : ∀ κ : K, ∫ ω in S ∩ sel ⁻¹' {κ}, g ω ∂μ
      = ∫ ω in S ∩ sel ⁻¹' {κ}, Φ ω ∂μ := by
    intro κ
    have := heq κ (S ∩ sel ⁻¹' {κ}) (hmeasS κ) (fun ω hω => hω.2)
    rw [integral_indicator (hmeasSamb κ), integral_indicator (hmeasSamb κ)] at this
    exact this.symm
  have hΦS : IntegrableOn Φ S μ := hΦ.integrableOn
  have hgS : IntegrableOn g S μ := hgint.integrableOn
  rw [show (∫ ω in S, g ω ∂μ) = ∫ ω in ⋃ κ : K, S ∩ sel ⁻¹' {κ}, g ω ∂μ
      from by rw [← hpart],
    show (∫ ω in S, Φ ω ∂μ) = ∫ ω in ⋃ κ : K, S ∩ sel ⁻¹' {κ}, Φ ω ∂μ
      from by rw [← hpart],
    integral_iUnion hmeasSamb hdisj (hpart ▸ hgS),
    integral_iUnion hmeasSamb hdisj (hpart ▸ hΦS)]
  exact tsum_congr hEq

end LatticeProb.Scaling.CondExpPartition

end
