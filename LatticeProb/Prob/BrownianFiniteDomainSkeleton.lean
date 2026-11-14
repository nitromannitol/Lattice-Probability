import LatticeProb.Bonanno.BouRabeeGwynne.BrownianActiveSkeletonTail

/-!
# Brownian skeletons with finitely many exit domains

A finite family of bounded exit domains has a bounded common ambient set. This yields a uniform
bound on the probability that a Brownian excursion skeleton remains active after many steps.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- For finitely many bounded open domains, the active-skeleton tail is uniform over all starts
in a bounded set and all measurable selectors with a fixed positive geometric margin. -/
theorem brownian_finiteDomain_activeSkeleton_tail
    {d : ℕ} {J : Type*} [Finite J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BouRabeeGwynne.BrownianPath d)}
    (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ)
    (U : J → Set (BouRabeeGwynne.Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j))
    {Z : Set (BouRabeeGwynne.Euc d)} (hZ : Bornology.IsBounded Z)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ z ∈ Z, ∀ j₀ : J,
      ∀ (selector : ℕ → BouRabeeGwynne.Euc d → Option J),
        (∀ n, Measurable (selector n)) →
        (∀ n x j, selector n x = some j → Metric.ball x ε ⊆ U j) →
        μ {ω | (BouRabeeGwynne.brownianSkeletonClock U z j₀ selector K ω).1 = false} ≤
          ENNReal.ofReal η := by
  let V := Z ∪ ⋃ j, U j
  have hV : Bornology.IsBounded V := hZ.union (Bornology.isBounded_iUnion.mpr hUb)
  obtain ⟨K, hK⟩ := BouRabeeGwynne.standardBrownianLaw_uniform_activeSkeletonTail
    (J := J) hd hμ hV hε hη
  refine ⟨K, ?_⟩
  intro z hz j₀ selector hselector hmargin
  apply hK U hU (fun j x hx => Or.inr (mem_iUnion.mpr ⟨j, hx⟩))
    z (Or.inl hz) j₀ selector hselector hmargin

end LatticeProb
