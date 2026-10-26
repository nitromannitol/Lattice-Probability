import LatticeProb.Network.FiniteEnergyVoltage
import LatticeProb.Network.BarrierMaximumConsumer

/-!
# Finite-energy voltage on the infinite ray

The connected locally finite ray on the natural numbers has a bounded finite-energy unit
voltage between zero and one. Its nonzero Laplacian at zero proves it is nonconstant.
-/

namespace LatticeProb.Network.Ray

open LatticeProb.Graph
open scoped Classical

/-- The actual infinite ray admits a nonconstant bounded finite-energy unit voltage,
normalized at vertex one and with source at zero. -/
theorem exists_finite_energy_voltage :
    ∃ f : ℕ → ℝ, ∃ M : ℝ, 0 < M ∧ f 1 = 0 ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ M) ∧
      (∀ x, laplacian graph f x =
        (if x = 1 then (1 : ℝ) else 0) - (if x = 0 then 1 else 0)) ∧
      (∃ K : ℝ, ∀ F : Finset (ℕ × ℕ), (∀ e ∈ F, graph.Adj e.1 e.2) →
        ∑ e ∈ F, (f e.1 - f e.2) ^ 2 ≤ K) ∧
      ¬ ∃ c : ℝ, ∀ x, f x = c := by
  obtain ⟨f, M, hM, hb, hbox, hlap, henergy⟩ :=
    exists_finite_energy_voltage_of_connected graph_connected (by decide : (0 : ℕ) ≠ 1)
  refine ⟨f, M, hM, hb, hbox, ?_, henergy, ?_⟩
  · intro x
    by_cases h1 : x = 1 <;> by_cases h0 : x = 0 <;>
      simpa only [h1, h0, if_true, if_false] using hlap x
  · rintro ⟨c, hc⟩
    have hzero : laplacian graph f 0 = 0 := by
      unfold laplacian
      apply Finset.sum_eq_zero
      intro y _
      rw [hc y, hc 0, sub_self]
    have hsource := hlap 0
    norm_num at hsource
    linarith

end LatticeProb.Network.Ray
