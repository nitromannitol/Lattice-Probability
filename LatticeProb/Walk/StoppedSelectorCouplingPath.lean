import LatticeProb.Walk.StoppedSelectorExitIndex
import LatticeProb.Walk.RepresentativeCouplingPath

/-! # Coupled path conditions at a stopped selector stage -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory BouRabeeGwynne
open scoped unitInterval

namespace LatticeProb

/-- On a coupling event, a stopped selector stage and a paired curve's outer
visit supply the discrete exit index and pre-exit edge bounds. Both the
stopping and the outer visit remain assumptions on that event. -/
theorem representativeCoupling_goodPath_of_stopped_stage
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (N : FiniteConductanceNetwork V) (p q : V → Euc d)
    {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (select : ℕ → Euc d → Option J) (v : V) (n : ℕ)
    (ρ : Measure ((ℕ → V) × C(unitInterval, Euc d)))
    (hρ : ρ.fst = N.trajectoryLaw A hA v)
    (U : Set (Euc d)) {a δ mesh : ℝ} (haδ : a < δ)
    (hpq : ∀ w, dist (p w) (q w) ≤ a)
    (hnone : ∀ i x, select i x = none → x ∉ thickening δ U)
    (hsteps : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ j : ℕ,
      (j : WithTop ℕ) < FiniteConductanceNetwork.exitTime (p ⁻¹' U) ω →
      dist (p (ω (j + 1))) (p (ω j)) ≤ mesh)
    (E : Set ((ℕ → V) × C(unitInterval, Euc d)))
    (hstop : ∀ᵐ x ∂ρ, x ∉ E →
      (FiniteConductanceNetwork.actualWalkStage q B initial
        (fun i w => select i (q w)) n x.1).2.1 = true ∧
      ∃ t, x.2 t ∉ thickening δ U) :
    ∀ᵐ x ∂ρ, x ∉ E →
      (FiniteConductanceNetwork.actualWalkStage q B initial
        (fun i w => select i (q w)) n x.1).1 ≠ ⊤ ∧
      ∃ k : ℕ, k ≤ (FiniteConductanceNetwork.actualWalkStage q B initial
        (fun i w => select i (q w)) n x.1).1.untopD 0 ∧
        FiniteConductanceNetwork.exitTime (p ⁻¹' U) x.1 = (k : WithTop ℕ) ∧
        (∀ j < k, dist (p (x.1 (j + 1))) (p (x.1 j)) ≤ mesh) ∧
        ∃ t, x.2 t ∉ thickening δ U := by
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
  apply representativeCoupling_goodPath_of_exit N p q B hBA hA haccess
    initial select v n ρ hρ U (thickening δ U) hsteps E
  filter_upwards [hclock, hstop] with x hc hs
  intro hx
  obtain ⟨hstopped, t, ht⟩ := hs hx
  obtain ⟨k, hk, hexit⟩ := exists_exit_index_le_stopped_stage_of_close
    p q B initial select U haδ hpq hnone x.1 n (hc n) hstopped
  exact ⟨k, hk, hexit, t, ht⟩

end LatticeProb
end
