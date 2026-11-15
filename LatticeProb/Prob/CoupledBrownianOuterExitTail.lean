import LatticeProb.Prob.BrownianSkeletonOuterExitTail

/-! # Brownian first-exit tails on coupled spaces -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped ENNReal

namespace LatticeProb

/-- The same finite skeleton reaches the first outer exit uniformly on every
coupled space with the prescribed Brownian marginal. An additional failure
event is charged separately, without any independence assumption. -/
theorem brownian_finiteDomain_coupled_outerExit_tail
    {d : ℕ} {J : Type*} [Finite J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j))
    {Z : Set (Euc d)} (hZ : Bornology.IsBounded Z)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ z ∈ Z, ∀ j₀ : J,
      ∀ (selector : ℕ → Euc d → Option J),
        (∀ n, Measurable (selector n)) →
        (∀ n x j, selector n x = some j → Metric.ball x ε ⊆ U j) →
        ∀ outer : Set (Euc d),
        (∀ n x, x ∈ outer → selector n x ≠ none) →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (ν : Measure Ω)
          (X : Ω → BrownianPath d), Measurable X → ν.map X = μ →
        ∀ (B : Set Ω) (b : ℝ≥0∞), ν B ≤ b →
          ν {ω | ω ∈ B ∨ (brownianSkeletonClock U z j₀ selector K (X ω)).2 <
            continuousExitTime outer z (X ω)} ≤ b + ENNReal.ofReal η := by
  obtain ⟨K, hK⟩ := brownian_finiteDomain_outerExit_skeleton_tail
    hd hμ U hU hUb hZ hε hη
  refine ⟨K, ?_⟩
  intro z hz j₀ selector hselector hmargin outer hactive Ω _ ν X hX hlaw B b hB
  let A : Set (BrownianPath d) := {ω |
    (brownianSkeletonClock U z j₀ selector K ω).2 < continuousExitTime outer z ω}
  have hpre : ν (X ⁻¹' A) ≤ ENNReal.ofReal η := by
    calc
      ν (X ⁻¹' A) ≤ ν.map X A := Measure.le_map_apply hX.aemeasurable A
      _ = μ A := by rw [hlaw]
      _ ≤ ENNReal.ofReal η := hK z hz j₀ selector hselector hmargin outer hactive
  change ν (B ∪ X ⁻¹' A) ≤ _
  exact (measure_union_le B (X ⁻¹' A)).trans (add_le_add hB hpre)

end LatticeProb
