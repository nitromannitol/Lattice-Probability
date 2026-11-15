import LatticeProb.Walk.RepresentativeCollarBudget

/-! # Path conditions under a walk coupling -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory BouRabeeGwynne
open scoped unitInterval

namespace LatticeProb

/-- Ambient accessibility and a walk-marginal edge bound supply the finite
clock and prefix edge conditions under any coupling with that marginal. -/
theorem representativeCoupling_goodPath_of_exit
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (N : FiniteConductanceNetwork V) (p q : V → Euc d)
    {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (select : ℕ → Euc d → Option J) (v : V) (n : ℕ)
    (ρ : Measure ((ℕ → V) × C(unitInterval, Euc d)))
    (hρ : ρ.fst = N.trajectoryLaw A hA v)
    (U Q : Set (Euc d)) {mesh : ℝ}
    (hsteps : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ j : ℕ,
      (j : WithTop ℕ) < FiniteConductanceNetwork.exitTime (p ⁻¹' U) ω →
      dist (p (ω (j + 1))) (p (ω j)) ≤ mesh)
    (E : Set ((ℕ → V) × C(unitInterval, Euc d)))
    (hpath : ∀ᵐ x ∂ρ, x ∉ E →
      ∃ k : ℕ, k ≤ (FiniteConductanceNetwork.actualWalkStage q B initial
        (fun i w => select i (q w)) n x.1).1.untopD 0 ∧
        FiniteConductanceNetwork.exitTime (p ⁻¹' U) x.1 = (k : WithTop ℕ) ∧
        ∃ t, x.2 t ∉ Q) :
    ∀ᵐ x ∂ρ, x ∉ E →
      (FiniteConductanceNetwork.actualWalkStage q B initial
        (fun i w => select i (q w)) n x.1).1 ≠ ⊤ ∧
      ∃ k : ℕ, k ≤ (FiniteConductanceNetwork.actualWalkStage q B initial
        (fun i w => select i (q w)) n x.1).1.untopD 0 ∧
        FiniteConductanceNetwork.exitTime (p ⁻¹' U) x.1 = (k : WithTop ℕ) ∧
        (∀ j < k, dist (p (x.1 (j + 1))) (p (x.1 j)) ≤ mesh) ∧
        ∃ t, x.2 t ∉ Q := by
  have hclock : ∀ᵐ x ∂ρ, ∀ i,
      (FiniteConductanceNetwork.actualWalkStage q B initial
        (fun i w => select i (q w)) i x.1).1 ≠ ⊤ := by
    have h : ∀ᵐ ω ∂ρ.map Prod.fst, ∀ i,
        (FiniteConductanceNetwork.actualWalkStage q B initial
          (fun i w => select i (q w)) i ω).1 ≠ ⊤ := by
      rw [show ρ.map Prod.fst = N.trajectoryLaw A hA v from hρ]
      exact N.actualWalkStage_ae_all_clocks_finite q B hBA hA haccess initial
        (fun i w => select i (q w)) v
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hedge : ∀ᵐ x ∂ρ, ∀ j : ℕ,
      (j : WithTop ℕ) < FiniteConductanceNetwork.exitTime (p ⁻¹' U) x.1 →
      dist (p (x.1 (j + 1))) (p (x.1 j)) ≤ mesh := by
    have h : ∀ᵐ ω ∂ρ.map Prod.fst, ∀ j : ℕ,
        (j : WithTop ℕ) < FiniteConductanceNetwork.exitTime (p ⁻¹' U) ω →
        dist (p (ω (j + 1))) (p (ω j)) ≤ mesh := by
      rw [show ρ.map Prod.fst = N.trajectoryLaw A hA v from hρ]
      exact hsteps
    exact ae_of_ae_map measurable_fst.aemeasurable h
  filter_upwards [hclock, hedge, hpath] with x hc he hp
  intro hx
  obtain ⟨k, hk, hτ, t, ht⟩ := hp hx
  refine ⟨hc n, k, hk, hτ, ?_, t, ht⟩
  intro j hj
  apply he j
  rw [hτ]
  exact WithTop.coe_lt_coe.mpr hj

end LatticeProb
end
