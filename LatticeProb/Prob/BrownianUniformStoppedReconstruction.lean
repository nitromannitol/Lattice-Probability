import LatticeProb.Prob.BrownianFiniteDomainSkeleton
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedSkeleton

/-! # Uniform approximation of stopped Brownian curve laws -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- A uniform finite excursion prefix approximates the stopped Brownian curve
law, provided the selector is active throughout the open stopping domain. -/
theorem brownian_finiteDomain_uniform_stopped_reconstruction
    {d : ℕ} {J : Type*} [Finite J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (W : J → Set (Euc d)) (hW : ∀ j, IsOpen (W j))
    (hWb : ∀ j, Bornology.IsBounded (W j))
    {Z : Set (Euc d)} (hZ : Bornology.IsBounded Z)
    {ε : ℝ} (hε : 0 < ε) (r : ℝ≥0) (hr : 0 < r) :
    ∃ K : ℕ, ∀ z ∈ Z, ∀ j₀ : J,
      ∀ (selector : ℕ → Euc d → Option J),
        (∀ n, Measurable (selector n)) →
        (∀ n x j, selector n x = some j → ball x ε ⊆ W j) →
        ∀ {U : Set (Euc d)}, IsOpen U →
        (∀ n x, x ∈ U → selector n x ≠ none) →
        ∀ P : TimePartition K,
          levyProkhorovEDist (stoppedBrownianLaw U z μ)
            ((μ.map (fun ω k => brownianSkeletonExcursion W z j₀ selector k ω)).map
              (reconstructedBrownianStoppedCurve U P)) ≤ r := by
  obtain ⟨K, hK⟩ := brownian_finiteDomain_activeSkeleton_tail hd hμ W hW hWb hZ hε
    (show (0 : ℝ) < r by exact_mod_cast hr)
  refine ⟨K, ?_⟩
  intro z hz j₀ selector hselector hmargin U hU hactive P
  have hnone : ∀ n x, selector n x = none → x ∉ U := by
    intro n x hn hx
    exact hactive n x hx hn
  apply levyProkhorov_stoppedBrownian_reconstruction_le hd hμ W hW hWb z j₀
    selector hselector hU hnone K P r hr
  simpa only [ENNReal.ofReal_coe_nnreal] using hK z hz j₀ selector hselector hmargin

end LatticeProb
