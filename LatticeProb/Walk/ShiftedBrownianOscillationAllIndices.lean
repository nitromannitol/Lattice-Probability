import LatticeProb.Bonanno.BouRabeeGwynne.BrownianUniformFiniteProbability
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianCoupling

/-! # Uniform oscillation for a shifted Brownian skeleton -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric BouRabeeGwynne
open scoped unitInterval NNReal ENNReal

universe u

namespace LatticeProb

/-- The finite-skeleton clock and pasted-curve oscillation estimates hold
uniformly for shifted selectors satisfying the same margin and coverage
conditions. The cutoff is chosen before the label type; the stage count is
chosen after the label type and before the domains and selector. -/
theorem uniform_shiftedBrownianSkeleton_probability_all_indices
    {d : ℕ}
    (hd : 1 ≤ d) {U : Set (Euc d)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ a > 0, ∀ (J : Type u) [Countable J]
      [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)],
      ∀ ε : ℝ, 0 < ε → ε ≤ a → ∀ δ : ℝ, 0 < δ → δ ≤ a →
      ∀ W : Set (Euc d), Bornology.IsBounded W → U ⊆ W →
      ∀ r : ℝ, 0 < r → ∃ K : ℕ,
      ∀ (G : J → Set (Euc d)), (∀ j, IsOpen (G j)) → (∀ j, G j ⊆ W) →
      ∀ z ∈ U, ∀ j₀ : J,
      ∀ (select : ℕ → Euc d → Option J), (∀ k, Measurable (select k)) →
      (∀ k x j, select k x = some j → ball x (r / 2) ⊆ G j) →
      (∀ k x, select k x = none → x ∉ thickening δ U) →
      ∀ P : TimePartition K,
        μ {ω | (brownianSkeletonClock G z j₀ (brownianSelectorForWalk select) K ω).1 =
          false} ≤ ENNReal.ofReal τ ∧
        μ {ω | pastedBrownianCurve P (fun k => brownianSkeletonExcursion G z j₀
          (brownianSelectorForWalk select) k ω) ∈
            unitCurveExitOscillationBad (innerDomain U ε) (thickening δ U) η} ≤
          ENNReal.ofReal τ + ENNReal.ofReal τ := by
  obtain ⟨a, ha, h⟩ := hL.uniform_brownian_finiteSkeleton_probability_all_indices
    hd hU hUb hμ hη hτ
  refine ⟨a, ha, ?_⟩
  intro J _ _ _ ε hε hεa δ hδ hδa W hW hUW r hr
  obtain ⟨K, hK⟩ := h J ε hε hεa δ hδ hδa W hW hUW r hr
  refine ⟨K, ?_⟩
  intro G hG hGW z hz j₀ select hs hmargin hnone P
  have hshift : ∀ k, Measurable (brownianSelectorForWalk select k) :=
    fun k => hs (k - 1)
  have hresult := hK G hG hGW z hz j₀ (brownianSelectorForWalk select) hshift
    (fun k x j hj => hmargin (k - 1) x j hj)
    (fun k x hx => hnone (k - 1) x hx) P
  refine ⟨hresult.1, ?_⟩
  have hΓ : Measurable (fun ω k => brownianSkeletonExcursion G z j₀
      (brownianSelectorForWalk select) k ω) :=
    Measurable.of_eval (fun k => measurable_brownianSkeletonExcursion G hG z j₀ hshift k)
  have hset : MeasurableSet {γ : ℕ → Bool × C(unitInterval, Euc d) |
      pastedBrownianCurve P γ ∈
        unitCurveExitOscillationBad (innerDomain U ε) (thickening δ U) η} :=
    (measurableSet_unitCurveExitOscillationBad (isOpen_innerDomain U ε)
      isOpen_thickening η).preimage (measurable_pastedBrownianCurve P)
  rw [Measure.map_apply hΓ hset] at hresult
  exact hresult.2

end LatticeProb
end
