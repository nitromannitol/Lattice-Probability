import Mathlib
import LatticeProb.Prob.Kingman

/-!
# Solution: Kingman

The challenge module `LatticeProbAudit/Kingman/Challenge.lean` imports only
Mathlib and states the theorem with one intentional `sorry`.  This solution
proves the byte-identical statement from `LatticeProb.ae_tendsto_div` and
`LatticeProb.tendsto_integral_div`.  The only work is the lower bound on the
means that the second of these asks for, which follows from the linear lower
bound on `g n`, and unfolding Mathlib's `Subadditive.lim` to the infimum.
-/

namespace LatticeProbAudit

open MeasureTheory Filter Topology

universe u

/-- Kingman's subadditive ergodic theorem, for a family bounded below linearly. -/
theorem kingman {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : ∀ (m n : ℕ) (x : Ω), g (m + n) x ≤ g m x + g n (T^[m] x))
    (hgm : ∀ n, Measurable (g n)) (hint : ∀ n, Integrable (g n) μ)
    {c : ℝ} (hlow : ∀ (n : ℕ) (x : Ω), 1 ≤ n → c * n ≤ g n x) :
    (∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / n) atTop (𝓝 L)) ∧
      Tendsto (fun n : ℕ => (∫ x, g n x ∂μ) / n) atTop
        (𝓝 (sInf ((fun n : ℕ => (∫ x, g n x ∂μ) / n) '' Set.Ici 1))) := by
  refine ⟨LatticeProb.ae_tendsto_div hT hsub hgm (hint 1) hlow, ?_⟩
  have hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g n x ∂μ) / n) := by
    refine ⟨min 0 (c * μ.real Set.univ), ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : ∫ _x, c * (n : ℝ) ∂μ ≤ ∫ x, g n x ∂μ :=
        integral_mono (integrable_const _) (hint n) fun x => hlow n x hn
      rw [integral_const, smul_eq_mul] at h1
      rw [le_div_iff₀ hn']
      calc min 0 (c * μ.real Set.univ) * n ≤ c * μ.real Set.univ * n :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hn'.le
        _ = μ.real Set.univ * (c * n) := by ring
        _ ≤ ∫ x, g n x ∂μ := h1
  have h := LatticeProb.tendsto_integral_div hT hsub hint hbdd
  rw [Subadditive.lim] at h
  exact h

end LatticeProbAudit
