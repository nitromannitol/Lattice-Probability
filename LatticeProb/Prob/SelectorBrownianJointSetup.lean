import LatticeProb.Prob.ActualSelectorBrownianSetup
import LatticeProb.Prob.NetworkBallSelectorDiameter

/-! # Joint selector and Brownian estimates -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open MeasureTheory Filter Set Metric BouRabeeGwynne
open scoped Topology unitInterval ENNReal

namespace LatticeProb

local instance {X : Type*} : MeasurableSpace (Option X) := ⊤

/-- A single family of selectors satisfies the finite-network first-failure
estimate and the Brownian clock and oscillation estimates. The endpoint-law
convergence is assumed uniformly over the network vertices. -/
theorem exists_selector_brownian_joint_setup {d : ℕ} (hd : 1 ≤ d)
    {U D : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : HasLipschitzBoundary U) (hUD : HasAmbientCollar U D)
    {ρ : Measure (BrownianPath d)} [IsProbabilityMeasure ρ]
    (hρ : IsStandardBrownianLaw ρ) {η : ℝ} (hη : 0 < η) :
    ∃ (δ r : ℝ) (W Q : Set (Euc d)) (centers : Finset (Euc d)) (K : ℕ),
      0 < δ ∧ 0 < r ∧ r ≤ δ / 100 ∧ r ≤ η / 100 ∧
      IsOpen W ∧ Bornology.IsBounded W ∧ U ⊆ W ∧ HasAmbientCollar W D ∧
      IsCompact Q ∧ cthickening δ U ⊆ Q ∧
      (∀ c ∈ centers, c ∈ cthickening δ U) ∧
      (∀ z ∈ cthickening δ U, ∃ c ∈ centers, z ∈ ball c (r / 4)) ∧
      (∀ c ∈ centers, closedBall c r ⊆ W) ∧
      (∀ c ∈ centers, closure (ball c r) ⊆ Q) ∧
      ∀ (V : ℕ → Type*) [∀ n, Fintype (V n)] [∀ n, MeasurableSpace (V n)]
        [∀ n, MeasurableSingletonClass (V n)]
        (N : ∀ n, FiniteConductanceNetwork (V n)) (pos : ∀ n, V n → Euc d)
        (_hpos : ∀ n, Measurable (pos n)) (hinj : ∀ n, Function.Injective (pos n))
        (B : ∀ n, centers → Set (V n))
        (hB : ∀ n j v, v ∈ B n j → 0 < (N n).totalConductance v)
        (ν : ∀ j : centers, closedBall j.val (r / 2) → ProbabilityMeasure (Euc d)),
      (∀ j z, (ν j z : Measure (Euc d)) =
        (stoppedBrownianLaw (ball j.val r) z.1 ρ).map BouRabeeGwynne.CurveSpace.endPoint) →
      (∀ j, Continuous (ν j)) →
      (∀ j : centers, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
        ∀ hv : pos n v ∈ closedBall j.val (r / 2),
        levyProkhorovDist (((N n).discreteHarmonicMeasure (B n j) (hB n j) v).map (pos n))
          (ν j ⟨pos n v, hv⟩ : Measure (Euc d)) < ε) →
      ∀ (a b : ℝ), 0 < a → 0 < b →
      ∃ (m : Fin (K + 1) → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
        (ε : Fin (K + 1) → ℝ)
        (hdisj : ∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l)))
        (hmeas : ∀ i k, MeasurableSet (E i k))
        (choice : ∀ i, Fin (m i) → Option ↥centers),
        (∀ i, 0 < ε i) ∧
        (∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ min a (r / 4)) ∧
        (∀ i, Q ⊆ ⋃ k, E i k) ∧
        let ix : ℕ → Fin (K + 1) := fun q => ⟨min q K, Nat.lt_succ_of_le (min_le_right _ _)⟩
        let m' : ℕ → ℕ := fun q => m (ix q)
        let E' : ∀ q, Fin (m' q) → Set (Euc d) := fun q => E (ix q)
        let select := fun q => cellSelector (E' q) (choice (ix q))
        let hs : ∀ q, Measurable (select q) := fun q =>
          measurable_cellSelector (E' q) (choice (ix q)) (hdisj (ix q)) (hmeas (ix q))
        (∀ q x, x ∈ cthickening δ U → select q x ≠ none) ∧
        (∀ q x j, select q x = some j → ball x (r / 2) ⊆ ball j.val r) ∧
        (∀ z ∈ U, ∀ initial : centers, ∀ P : TimePartition K,
          ρ {ω | (brownianSkeletonExcursion (fun c : centers => ball c.val r)
            z initial (brownianSelectorForWalk select) K ω).1 = false} ≤ ENNReal.ofReal (η / 100) ∧
          ρ {ω | pastedBrownianCurve P (fun k => brownianSkeletonExcursion
            (fun c : centers => ball c.val r) z initial (brownianSelectorForWalk select) k ω) ∈
            unitCurveExitOscillationBad (innerDomain U (6 * r)) (thickening δ U) (η / 10)} ≤
              2 * ENNReal.ofReal (η / 100)) ∧
        ∀ᶠ n in atTop, ∀ (initial : centers) (v₀ : V n) (z : Euc d),
          pos n v₀ ∈ closedBall initial.val (r / 2) →
          z ∈ closedBall initial.val (r / 2) →
          dist (pos n v₀) z ≤ ε ⟨0, Nat.zero_lt_succ K⟩ →
          (N n).walkBrownianJointLaw (pos n) (hinj n) (B n) (hB n)
            (fun j : centers => ball j.val r) (fun _ => isOpen_ball) ρ select hs
            m' E' (fun q => hmeas (ix q)) (fun q => hdisj (ix q)) initial v₀ z
            {p | ∃ i ≤ K, (p.1 i, p.2 i) ∉ goodExcursionPair (pos n) (E' i) (min a (r / 4))} ≤
              (K + 1 : ℝ≥0∞) * ENNReal.ofReal b := by
  obtain ⟨δ, r, W, Q, centers, K, hδ, hr, hrδ, hrη, hW, hWb, hUW, hWD,
    hQ, hCQ, hc, hcover, hballs, hballsQ, hprob⟩ :=
    exists_actual_selector_brownian_setup hd hU hUb hL hUD hρ hη
  refine ⟨δ, r, W, Q, centers, K, hδ, hr, hrδ, hrη, hW, hWb, hUW, hWD,
    hQ, hCQ, hc, hcover, hballs, hballsQ, ?_⟩
  intro V _ _ _ N pos hpos hinj B hB ν hνlaw hν hLP a b ha hb
  obtain ⟨m, E, ε, hdisj, hmeas, choice, hε, hdiam, hcoverQ, hactive, hmargin, hfail⟩ :=
    exists_network_ball_selectors_diameter_first_failure hd centers hr (cthickening δ U) Q
      hQ hCQ hcover (fun j => hballsQ j j.property) ρ hρ V N pos hpos hinj B hB ν
      hνlaw hν hLP a b ha hb K
  refine ⟨m, E, ε, hdisj, hmeas, choice, hε, hdiam, hcoverQ, ?_, ?_, ?_, hfail⟩
  · exact fun q => hactive _
  · exact fun q => hmargin _
  · intro z hz initial P
    apply hprob z hz initial _
    · exact fun q => measurable_cellSelector _ _ (hdisj _) (hmeas _)
    · exact fun q => hmargin _
    · exact fun q => hactive _

end LatticeProb
