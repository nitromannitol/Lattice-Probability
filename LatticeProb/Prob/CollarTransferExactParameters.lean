import LatticeProb.Prob.CollarTransferParameters
import LatticeProb.Prob.CollarTransferENNReal

/-! # Ordered parameters for finite-horizon estimates -/

set_option autoImplicit false

open scoped NNReal ENNReal

namespace LatticeProb

/-- Choose positive tolerances before the horizon and a per-step error after it,
with the resulting bounds expressed in extended nonnegative reals. -/
theorem exists_collar_transfer_exact_parameters {r : ℝ≥0} (hr : 0 < r) :
    ∃ η τ : ℝ, 0 < η ∧ 0 < τ ∧
      ∀ c : ℝ, 0 < c →
        ∃ a e δ mesh : ℝ,
          0 < a ∧ 0 < e ∧ 0 < δ ∧ 0 < mesh ∧
          a + e ≤ c ∧ δ ≤ c ∧ a + e + mesh < δ ∧
          ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞) ∧
          ∀ L : ℕ, ∃ b : ℝ, 0 < b ∧
            ((L + 1 : ℝ≥0∞) * ENNReal.ofReal b +
              (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
              (ENNReal.ofReal τ + (L + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤
                (r : ℝ≥0∞) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨η, τ, hη, hτ, hparameters⟩ := exists_collar_transfer_parameters hr'
  refine ⟨η, τ, hη, hτ, ?_⟩
  intro c hc
  obtain ⟨a, e, δ, mesh, ha, he, hδ, hmesh, hae, hδc, hbuffer, hsmall, hbudget⟩ :=
    hparameters c hc
  refine ⟨a, e, δ, mesh, ha, he, hδ, hmesh, hae, hδc, hbuffer,
    ennreal_lt_coe_of_lt hr hsmall, ?_⟩
  intro L
  obtain ⟨b, hb, hbgt⟩ := hbudget L
  exact ⟨b, hb, ennreal_finite_horizon_budget hb.le hτ.le hbgt⟩

end LatticeProb
