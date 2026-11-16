import LatticeProb.Prob.CollarTransferExactParameters
import LatticeProb.Topology.FiniteDomainCompactEnvelope

/-! # Ordered parameters and compact envelopes -/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace LatticeProb

/-- The compact envelope can be fixed after the collar width and before the
finite horizon, while preserving the finite-horizon error budget. -/
theorem exists_collar_transfer_compact_parameters
    {X : Type*} [MetricSpace X] [ProperSpace X] {J : Type*} [Finite J]
    {U : Set X} (hU : Bornology.IsBounded U)
    (W : J → Set X) (hW : ∀ j, Bornology.IsBounded (W j))
    {r : ℝ≥0} (hr : 0 < r) :
    ∃ η τ : ℝ, 0 < η ∧ 0 < τ ∧
      ∀ c : ℝ, 0 < c →
        ∃ (a e δ mesh : ℝ) (C : Set X),
          0 < a ∧ 0 < e ∧ 0 < δ ∧ 0 < mesh ∧
          a + e ≤ c ∧ δ ≤ c ∧ a + e + mesh < δ ∧
          ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞) ∧
          IsCompact C ∧ thickening δ U ⊆ C ∧ (∀ j, closure (W j) ⊆ C) ∧
          ∀ L : ℕ, ∃ b : ℝ, 0 < b ∧
            ((L + 1 : ℝ≥0∞) * ENNReal.ofReal b +
              (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
              (ENNReal.ofReal τ + (L + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤
                (r : ℝ≥0∞) := by
  obtain ⟨η, τ, hη, hτ, hparams⟩ := exists_collar_transfer_exact_parameters hr
  refine ⟨η, τ, hη, hτ, ?_⟩
  intro c hc
  obtain ⟨a, e, δ, mesh, ha, he, hδ, hmesh, hae, hδc, hbuffer, hsmall, hbudget⟩ :=
    hparams c hc
  obtain ⟨C, hC, hUC, hWC⟩ :=
    exists_compact_envelope_thickening_of_finite_domains hU δ W hW
  exact ⟨a, e, δ, mesh, C, ha, he, hδ, hmesh, hae, hδc, hbuffer, hsmall,
    hC, hUC, hWC, hbudget⟩

end LatticeProb
