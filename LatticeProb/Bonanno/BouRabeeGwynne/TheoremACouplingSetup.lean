/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.TheoremACouplingSetup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianUniformFiniteProbability
import LatticeProb.Bonanno.BouRabeeGwynne.CouplingNeighborhoods

/-! Fix the geometric and Brownian probability data for Theorem A before
the finite backward partitions and the approximation index are chosen. -/

open MeasureTheory Set Metric
open scoped unitInterval NNReal ENNReal

namespace BouRabeeGwynne

local instance setupOptionMeasurableSpace {X : Type*} : MeasurableSpace (Option X) := ⊤

theorem exists_theoremA_coupling_setup {d : ℕ} (hd : 1 ≤ d)
    {U D : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : HasLipschitzBoundary U) (hUD : HasAmbientCollar U D)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {η : ℝ} (hη : 0 < η) :
    ∃ (δ r : ℝ) (W Q : Set (Euc d)) (centers : Finset (Euc d)) (K : ℕ),
      0 < δ ∧ 0 < r ∧ r ≤ δ / 100 ∧ r ≤ η / 100 ∧
      IsOpen W ∧ Bornology.IsBounded W ∧ U ⊆ W ∧ HasAmbientCollar W D ∧
      IsCompact Q ∧ cthickening δ U ⊆ Q ∧
      (∀ c ∈ centers, c ∈ cthickening δ U) ∧
      (∀ z ∈ cthickening δ U, ∃ c ∈ centers, z ∈ ball c (r / 4)) ∧
      (∀ c ∈ centers, closedBall c r ⊆ W) ∧
      (∀ c ∈ centers, closure (ball c r) ⊆ Q) ∧
      ∀ z ∈ U, ∀ j₀ : ↥centers,
      ∀ (selector : ℕ → Euc d → Option ↥centers) (_hselector : ∀ k, Measurable (selector k)),
      (∀ k x j, selector k x = some j → ball x (r / 2) ⊆ ball (j : Euc d) r) →
      (∀ k x, selector k x = none → x ∉ thickening δ U) →
      ∀ P : TimePartition K,
        μ {ω | (brownianSkeletonClock (fun c : ↥centers ↦ ball (c : Euc d) r)
          z j₀ selector K ω).1 = false} ≤ ENNReal.ofReal (η / 100) ∧
        (μ.map (fun ω k ↦ brownianSkeletonExcursion
          (fun c : ↥centers ↦ ball (c : Euc d) r) z j₀ selector k ω))
          {γ | pastedBrownianCurve P γ ∈
            unitCurveExitOscillationBad (innerDomain U (6 * r)) (thickening δ U) (η / 10)} ≤
          2 * ENNReal.ofReal (η / 100) := by
  classical
  have hη10 : 0 < η / 10 := by positivity
  have hη100 : 0 < η / 100 := by positivity
  obtain ⟨a, ha, hprob⟩ :=
    hL.uniform_brownian_finiteSkeleton_probability_all_indices hd hU hUb hμ hη10 hη100
  obtain ⟨δ, r, W, Q, centers, hδ, hδa, hr, hrη, hrδ,
      hW, hWb, hWD, hQ, hCQ, hcenters, hcover, hballs, hballsQ⟩ :=
    exists_coupling_neighborhoods hUb hUD ha hη100
  have hUW : U ⊆ W := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hcover z (self_subset_cthickening U hz)
    apply hballs c hc
    have hzdist : dist z c < r / 4 := hzc
    change dist z c ≤ r
    linarith
  have h6r : 0 < 6 * r := by positivity
  have h6ra : 6 * r ≤ a := by linarith
  obtain ⟨K, hK⟩ := hprob ↥centers (6 * r) h6r h6ra δ hδ hδa W hWb hUW r hr
  refine ⟨δ, r, W, Q, centers, K, hδ, hr, hrδ, hrη, hW, hWb, hUW, hWD,
    hQ, hCQ, hcenters, hcover, hballs, hballsQ, ?_⟩
  intro z hz j₀ selector hselector hmargin hnone P
  have hfixed : ∀ c : ↥centers, ball (c : Euc d) r ⊆ W :=
    fun c ↦ ball_subset_closedBall.trans (hballs c c.property)
  have h := hK (fun c : ↥centers ↦ ball (c : Euc d) r) (fun _ ↦ isOpen_ball)
    hfixed z hz j₀ selector hselector hmargin hnone P
  exact ⟨h.1, by simpa only [two_mul] using h.2⟩

end BouRabeeGwynne
