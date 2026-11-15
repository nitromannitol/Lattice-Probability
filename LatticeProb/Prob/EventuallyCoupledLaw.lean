import Mathlib

/-!
# Stationary laws under an eventual coupling

Two sequences of random variables with fixed respective laws have the same law if their values
are eventually equal almost surely on a common finite measure space.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- An almost surely eventually equal coupling identifies the stationary laws. -/
theorem map_eq_of_ae_eventually_eq {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (X Y : ℕ → Ω → E) (μ ν : Measure E)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hμ : ∀ n, P.map (X n) = μ) (hν : ∀ n, P.map (Y n) = ν)
    (heq : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, X n ω = Y n ω) : μ = ν := by
  have one_side : ∀ (X Y : ℕ → Ω → E) (μ ν : Measure E),
      (∀ n, Measurable (X n)) → (∀ n, Measurable (Y n)) →
      (∀ n, P.map (X n) = μ) → (∀ n, P.map (Y n) = ν) →
      (∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, X n ω = Y n ω) → μ ≤ ν := by
    intro X Y μ ν hX hY hμ hν heq
    refine Measure.le_iff.2 ?_
    intro s hs
    let D : ℕ → Set Ω := fun n => X n ⁻¹' s \ Y n ⁻¹' s
    have hD : ∀ n, MeasurableSet (D n) := fun n => (hX n hs).diff (hY n hs)
    have hlim : Tendsto (fun n => P (D n)) atTop (𝓝 0) := by
      have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        (μ := P) (A := ∅) (As := D) MeasurableSet.empty hD (by
          filter_upwards [heq] with ω hω
          filter_upwards [hω] with n hn
          simp [D, hn])
      simpa using h
    have hbound : ∀ n, μ s ≤ ν s + P (D n) := by
      intro n
      rw [← hμ n, ← hν n, Measure.map_apply (hX n) hs, Measure.map_apply (hY n) hs]
      calc
        P (X n ⁻¹' s) ≤ P ((Y n ⁻¹' s) ∪ D n) := measure_mono (by intro x hx; by_cases hy : Y n x ∈ s <;> simp [D, hx, hy])
        _ ≤ P (Y n ⁻¹' s) + P (D n) := measure_union_le _ _
    have ht : Tendsto (fun n => ν s + P (D n)) atTop (𝓝 (ν s)) := by
      simpa using tendsto_const_nhds.add hlim
    exact ge_of_tendsto ht (Eventually.of_forall hbound)
  exact le_antisymm (one_side X Y μ ν hX hY hμ hν heq)
    (one_side Y X ν μ hY hX hν hμ (heq.mono fun _ h => h.mono fun _ he => he.symm))

end LatticeProb
