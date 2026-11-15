/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianFiniteProbability at commit fdb5cad; local import paths and proof notation are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianBoundaryOscillation
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonOscillation

/-! The uniform Brownian probability input for the finite coupling argument.
The boundary cutoff precedes the fixed margin and stage count, and the stage
count precedes every fine selector and excursion-domain family. -/

open MeasureTheory Set Metric
open scoped unitInterval NNReal ENNReal

namespace BouRabeeGwynne

noncomputable def pastedBrownianCurve {d n : ℕ} (P : TimePartition n)
    (γ : ℕ → Bool × C(unitInterval, Euc d)) : C(unitInterval, Euc d) :=
  P.concatenate (ExcursionTrajectory.prefixChain n d (fun k ↦ (γ k).2))

lemma measurable_pastedBrownianCurve {d n : ℕ} (P : TimePartition n) :
    Measurable (pastedBrownianCurve (d := d) P) := by
  have hm : Measurable (fun γ : ℕ → Bool × C(unitInterval, Euc d) ↦ fun k ↦ (γ k).2) := by
    apply Measurable.of_eval
    intro k
    exact measurable_snd.comp (measurable_pi_apply k)
  exact P.measurable_concatenate.comp ((ExcursionTrajectory.measurable_prefixChain n d).comp hm)

theorem HasLipschitzBoundary.uniform_brownian_finiteSkeleton_probability
    {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {U : Set (Euc d)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ a > 0, ∀ ε : ℝ, 0 < ε → ε ≤ a → ∀ δ : ℝ, 0 < δ → δ ≤ a →
      ∀ W : Set (Euc d), Bornology.IsBounded W → U ⊆ W →
      ∀ r : ℝ, 0 < r → ∃ K : ℕ,
      ∀ (G : J → Set (Euc d)) (_hG : ∀ j, IsOpen (G j)), (∀ j, G j ⊆ W) →
      ∀ z ∈ U, ∀ j₀ : J,
      ∀ (selector : ℕ → Euc d → Option J) (_hselector : ∀ k, Measurable (selector k)),
      (∀ k x j, selector k x = some j → ball x (r / 2) ⊆ G j) →
      (∀ k x, selector k x = none → x ∉ thickening δ U) →
      ∀ P : TimePartition K,
        μ {ω | (brownianSkeletonClock G z j₀ selector K ω).1 = false} ≤ ENNReal.ofReal τ ∧
        (μ.map (fun ω k ↦ brownianSkeletonExcursion G z j₀ selector k ω))
          {γ | pastedBrownianCurve P γ ∈
            unitCurveExitOscillationBad (innerDomain U ε) (thickening δ U) η} ≤
          ENNReal.ofReal τ + ENNReal.ofReal τ := by
  let : IsProbabilityMeasure μ := hμ.1
  obtain ⟨a, ha, hboundary⟩ :=
    hL.uniform_brownian_boundary_oscillation hd hU hUb μ hμ hη hτ
  refine ⟨a, ha, ?_⟩
  intro ε hε hεa δ hδ hδa W hW hUW r hr
  obtain ⟨K, hK⟩ := standardBrownianLaw_uniform_activeSkeletonTail (J := J)
    hd hμ hW (half_pos hr) hτ
  refine ⟨K, ?_⟩
  intro G hG hGW z hz j₀ selector hselector hmargin hnone P
  have hactive := hK G hG hGW z (hUW hz) j₀ selector hselector hmargin
  refine ⟨hactive, ?_⟩
  have hΓ : Measurable (fun ω k ↦ brownianSkeletonExcursion G z j₀ selector k ω) := by
    apply Measurable.of_eval
    intro k
    exact measurable_brownianSkeletonExcursion G hG z j₀ hselector k
  have hset : MeasurableSet {γ : ℕ → Bool × C(unitInterval, Euc d) |
      pastedBrownianCurve P γ ∈
        unitCurveExitOscillationBad (innerDomain U ε) (thickening δ U) η} :=
    (measurableSet_unitCurveExitOscillationBad (isOpen_innerDomain U ε)
      isOpen_thickening η).preimage (measurable_pastedBrownianCurve P)
  rw [Measure.map_apply hΓ hset]
  have hinner : innerDomain U ε ⊆ thickening δ U :=
    (subset_closure.trans (closure_innerDomain_subset U hε)).trans (self_subset_thickening hδ U)
  exact brownianSkeleton_oscillationBad_measure_le hd hμ G hG (fun j ↦ hW.subset (hGW j))
    z j₀ selector hselector (isOpen_innerDomain U ε) isOpen_thickening hinner hnone
    K P η (ENNReal.ofReal τ) (ENNReal.ofReal τ)
    (hboundary ε hε hεa δ hδ hδa z hz) hactive

end BouRabeeGwynne
