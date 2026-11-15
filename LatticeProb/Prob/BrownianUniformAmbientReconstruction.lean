import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedSkeleton

/-! # Uniform stopped Brownian reconstruction in a bounded ambient set -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- A single finite prefix length approximates the stopped Brownian curve law
uniformly over all excursion domains contained in a bounded ambient set. -/
theorem brownian_uniform_ambient_stopped_reconstruction
    {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {V : Set (Euc d)} (hV : Bornology.IsBounded V)
    {ε : ℝ} (hε : 0 < ε) (r : ℝ≥0) (hr : 0 < r) :
    ∃ K : ℕ, ∀ (W : J → Set (Euc d)), (∀ j, IsOpen (W j)) →
      (∀ j, W j ⊆ V) → ∀ z ∈ V, ∀ j₀ : J,
      ∀ (selector : ℕ → Euc d → Option J),
        (∀ n, Measurable (selector n)) →
        (∀ n x j, selector n x = some j → ball x ε ⊆ W j) →
        ∀ {U : Set (Euc d)}, IsOpen U →
        (∀ n x, x ∈ U → selector n x ≠ none) →
        ∀ P : TimePartition K,
          levyProkhorovEDist (stoppedBrownianLaw U z μ)
            ((μ.map (fun ω k => brownianSkeletonExcursion W z j₀ selector k ω)).map
              (reconstructedBrownianStoppedCurve U P)) ≤ r := by
  obtain ⟨K, hK⟩ := standardBrownianLaw_uniform_activeSkeletonTail (J := J)
    hd hμ hV hε (show (0 : ℝ) < r by exact_mod_cast hr)
  refine ⟨K, ?_⟩
  intro W hW hWV z hz j₀ selector hselector hmargin U hU hactive P
  have hnone : ∀ n x, selector n x = none → x ∉ U := by
    intro n x hn hx
    exact hactive n x hx hn
  apply levyProkhorov_stoppedBrownian_reconstruction_le hd hμ W hW
    (fun j => hV.subset (hWV j)) z j₀ selector hselector hU hnone K P r hr
  simpa only [ENNReal.ofReal_coe_nnreal] using
    hK W hW hWV z hz j₀ selector hselector hmargin

end LatticeProb
