import LatticeProb.Prob.UniformReferenceStartPerturbation
import LatticeProb.Prob.NetworkBackwardCellComparison
import LatticeProb.Walk.UniformPerturbedBallEndpoint

/-! # Endpoint laws from compact-collar reference estimates -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter BouRabeeGwynne
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped ENNReal NNReal

namespace LatticeProb

/-- Reference endpoint laws on a compact collar transfer to nearby embedded
ball-exit laws, subject to a neighboring-exit oscillation estimate. -/
theorem uniform_ball_exit_law_of_collar_reference
    {d : ℕ} {J : Type*} (I K : J → Set (Euc d))
    (hK : ∀ j, IsCompact (K j)) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (hcollar : ∀ j x, x ∈ I j → ∀ y, dist y x < r j → y ∈ K j)
    (z : J → Euc d) (R : J → ℝ)
    (V : ℕ → Type*) [∀ n, Fintype (V n)] [∀ n, MeasurableSpace (V n)]
    [∀ n, MeasurableSingletonClass (V n)]
    (N : ∀ n, FiniteConductanceNetwork (V n)) (p q : ∀ n, V n → Euc d)
    (hp : ∀ n, Measurable (p n))
    (A : ∀ n, Set (V n)) (hA : ∀ n v, v ∈ A n → 0 < (N n).totalConductance v)
    (hpA : ∀ n j, p n ⁻¹' ball (z j) (R j) ⊆ A n)
    (hqA : ∀ n j, q n ⁻¹' ball (z j) (R j) ⊆ A n)
    (ν : ∀ j, K j → ProbabilityMeasure (Euc d)) (hν : ∀ j, Continuous (ν j))
    (hclose : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v, dist (p n v) (q n v) < δ)
    (href : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      ∀ hv : p n v ∈ K j,
      levyProkhorovDist
        (((N n).discreteHarmonicMeasure (p n ⁻¹' ball (z j) (R j))
          (fun w hw => hA n w (hpA n j hw)) v).map (p n))
        (ν j ⟨p n v, hv⟩ : Measure (Euc d)) < ε)
    (hosc : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      q n v ∈ I j → ∃ (δ η : ℝ) (E : Set (ℕ → V n)),
        (∀ w, dist (p n w) (q n w) ≤ δ) ∧ η + δ < ε / 4 ∧
        (N n).trajectoryLaw (A n) (hA n) v E ≤ (ENNReal.ofReal (ε / 4)) ∧
        (∀ᵐ ω ∂(N n).trajectoryLaw (A n) (hA n) v, ω ∉ E →
          exitTime (p n ⁻¹' ball (z j) (R j + δ)) ω ≠ ⊤ ∧
          ∀ i ∈ Icc ((exitTime (p n ⁻¹' ball (z j) (R j - δ)) ω).untopD 0)
              ((exitTime (p n ⁻¹' ball (z j) (R j + δ)) ω).untopD 0),
            ∀ k ∈ Icc ((exitTime (p n ⁻¹' ball (z j) (R j - δ)) ω).untopD 0)
                ((exitTime (p n ⁻¹' ball (z j) (R j + δ)) ω).untopD 0),
              dist (p n (ω i)) (p n (ω k)) ≤ η)) :
    ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      ∀ hv : q n v ∈ I j,
      levyProkhorovDist
        (((N n).discreteHarmonicMeasure (q n ⁻¹' ball (z j) (R j))
          (fun w hw => hA n w (hqA n j hw)) v).map (q n))
        (ν j ⟨q n v, hcollar j _ hv _ (by simpa using hr j)⟩ : Measure (Euc d)) < ε := by
  let νI : ∀ j, I j → ProbabilityMeasure (Euc d) := fun j x =>
    ν j ⟨x.1, hcollar j _ x.2 _ (by simpa using hr j)⟩
  have hreference : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      ∀ hv : q n v ∈ I j,
      levyProkhorovDist
        (((N n).discreteHarmonicMeasure (p n ⁻¹' ball (z j) (R j))
          (fun w hw => hA n w (hpA n j hw)) v).map (p n))
        (νI j ⟨q n v, hv⟩ : Measure (Euc d)) < ε := by
    intro j
    let μ : ∀ n, V n → ProbabilityMeasure (Euc d) := fun n v =>
      networkEndpointProbability (N n) (p n) (hp n)
        (p n ⁻¹' ball (z j) (R j)) (fun w hw => hA n w (hpA n j hw)) v
    have h := uniform_reference_law_at_nearby_starts (I j) (K j) (hK j)
      (r j) (hr j) (hcollar j) V p q μ (ν j) (hν j) hclose (href j)
    exact h
  exact uniform_ball_exit_law_of_oscillation I z R V N p q A hA hpA hqA νI hreference hosc

end LatticeProb
end
