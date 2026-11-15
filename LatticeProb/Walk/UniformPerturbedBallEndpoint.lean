import LatticeProb.Walk.DiscreteBallExitLawPerturbation

/-! # Uniform endpoint laws for perturbed embedded balls -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter BouRabeeGwynne
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped ENNReal NNReal

namespace LatticeProb

/-- Uniform convergence of reference ball-exit laws transfers to nearby embeddings
when neighboring-radius oscillations have uniformly small exceptional mass. The
reference law is compared at the starting point of the perturbed embedding. -/
theorem uniform_ball_exit_law_of_oscillation
    {d : ℕ} {J : Type*} (I : J → Set (Euc d)) (z : J → Euc d) (R : J → ℝ)
    (V : ℕ → Type*) [∀ n, Fintype (V n)] [∀ n, MeasurableSpace (V n)]
    [∀ n, MeasurableSingletonClass (V n)]
    (N : ∀ n, FiniteConductanceNetwork (V n)) (p q : ∀ n, V n → Euc d)
    (A : ∀ n, Set (V n)) (hA : ∀ n v, v ∈ A n → 0 < (N n).totalConductance v)
    (hpA : ∀ n j, p n ⁻¹' ball (z j) (R j) ⊆ A n)
    (hqA : ∀ n j, q n ⁻¹' ball (z j) (R j) ⊆ A n)
    (ν : ∀ j, I j → ProbabilityMeasure (Euc d))
    (href : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      ∀ hv : q n v ∈ I j,
      levyProkhorovDist
        (((N n).discreteHarmonicMeasure (p n ⁻¹' ball (z j) (R j))
          (fun w hw => hA n w (hpA n j hw)) v).map (p n))
        (ν j ⟨q n v, hv⟩ : Measure (Euc d)) < ε)
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
        (ν j ⟨q n v, hv⟩ : Measure (Euc d)) < ε := by
  intro j ε hε
  filter_upwards [href j (ε / 2) (by positivity), hosc j ε hε] with n hnref hnosc
  intro v hv
  obtain ⟨δ, η, E, hclose, hr, hbad, hgood⟩ := hnosc v hv
  let r : ℝ≥0 := ⟨ε / 4, by positivity⟩
  have hr' : η + δ < (r : ℝ) := hr
  have hbad' : (N n).trajectoryLaw (A n) (hA n) v E ≤ (r : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact hbad
  have hpert := levyProkhorovEDist_discrete_ball_exit_of_oscillation
    (N n) (p n) (q n) (z j) (R j) δ η hclose (hpA n j) (hqA n j)
    (hA n) v E r hr' hbad' hgood
  have hdist : levyProkhorovDist
      (((N n).discreteHarmonicMeasure (p n ⁻¹' ball (z j) (R j))
        (fun w hw => hA n w (hpA n j hw)) v).map (p n))
      (((N n).discreteHarmonicMeasure (q n ⁻¹' ball (z j) (R j))
        (fun w hw => hA n w (hqA n j hw)) v).map (q n)) ≤ ε / 4 := by
    change (levyProkhorovEDist _ _).toReal ≤ ε / 4
    have h := ENNReal.toReal_mono (by simp) hpert
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.toReal_ofReal r.coe_nonneg] at h
    exact h
  have htriangle := levyProkhorovDist_triangle
    (((N n).discreteHarmonicMeasure (q n ⁻¹' ball (z j) (R j))
      (fun w hw => hA n w (hqA n j hw)) v).map (q n))
    (((N n).discreteHarmonicMeasure (p n ⁻¹' ball (z j) (R j))
      (fun w hw => hA n w (hpA n j hw)) v).map (p n))
    (ν j ⟨q n v, hv⟩ : Measure (Euc d))
  rw [levyProkhorovDist_comm _ (((N n).discreteHarmonicMeasure
    (p n ⁻¹' ball (z j) (R j)) (fun w hw => hA n w (hpA n j hw)) v).map (p n))] at htriangle
  have hreference := hnref v hv
  linarith

end LatticeProb
end
