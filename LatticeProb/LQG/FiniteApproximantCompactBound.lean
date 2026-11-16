import LatticeProb.LQG.LQGMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Compact density bounds for finitely many LQG approximants -/

open MeasureTheory Set

namespace LatticeProb.LQG

/-- Finitely many continuous approximant densities have a common bound on a
compact set. The same bound applies to every measurable subset of that set. -/
theorem exists_finite_lqgApprox_le_volume
    (γ : ℝ) (h : ℝ → ℂ → ℝ) (ε : ℕ → ℝ) (N : ℕ)
    (hc : ∀ k < N, Continuous (h (ε k))) (K : Set ℂ) (hK : IsCompact K) :
    ∃ A : ℝ, 0 < A ∧ ∀ k < N, ∀ S : Set ℂ, MeasurableSet S → S ⊆ K →
      lqgApprox γ h (ε k) S ≤ ENNReal.ofReal A * volume S := by
  have hb : ∀ k : Fin N, ∃ B : ℝ, ∀ z ∈ K,
      (ε k) ^ (γ ^ 2 / 2) * Real.exp (γ * h (ε k) z) ≤ B := by
    intro k
    have hcont : Continuous (fun z =>
        (ε k) ^ (γ ^ 2 / 2) * Real.exp (γ * h (ε k) z)) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hc k k.isLt)))
    obtain ⟨B, hB⟩ := hK.bddAbove_image hcont.continuousOn
    exact ⟨B, fun z hz => hB ⟨z, hz, rfl⟩⟩
  choose B hB using hb
  obtain ⟨C, hC⟩ := (Set.finite_range B).bddAbove
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro k hk S hS hSK
  rw [lqgApprox, withDensity_apply _ hS]
  calc
    (∫⁻ z in S, ENNReal.ofReal ((ε k) ^ (γ ^ 2 / 2) * Real.exp (γ * h (ε k) z))) ≤
        ∫⁻ _z in S, ENNReal.ofReal (max 1 C) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hS] with z hz
      apply ENNReal.ofReal_le_ofReal
      exact (hB ⟨k, hk⟩ z (hSK hz)).trans ((hC ⟨⟨k, hk⟩, rfl⟩).trans (le_max_right _ _))
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

end LatticeProb.LQG
