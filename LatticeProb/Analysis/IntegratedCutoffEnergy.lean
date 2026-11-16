import LatticeProb.Analysis.QuenchedCutoffEnergy

/-!
# Integrated critical cutoff energy

The pointwise critical cutoff-energy estimate summed over a Euclidean lattice ball.
-/

noncomputable section

open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Shell
open LatticeProb.Analysis.QuenchedCutoffEnergy LatticeProb.Analysis.AnnealedCutoffEnergy

namespace LatticeProb.Analysis.IntegratedCutoffEnergy

/-- A Euclidean ball in the integer lattice is finite. -/
theorem finite_ball {d : ℕ} (x₀ : Site d) (R : ℝ) :
    {x : Site d | radius (physical 1 (x - x₀)) < R}.Finite := by
  have hfinite : {z : Site d | radius (physical 1 z) ≤ R}.Finite := by
    apply (Set.Finite.pi' (fun _ : Fin d => Set.finite_Icc (-(⌈R⌉ : ℤ)) ⌈R⌉)).subset
    intro z hz i
    have h := (abs_coord_le_radius (physical 1 z) i).trans hz
    simp only [physical, one_mul] at h
    have h' : |(z i : ℝ)| ≤ (⌈R⌉ : ℤ) := h.trans (Int.le_ceil R)
    have hi : |z i| ≤ (⌈R⌉ : ℤ) := by exact_mod_cast h'
    exact abs_le.mp hi
  apply (hfinite.image (fun z => x₀ + z)).subset
  intro x hx
  change radius (physical 1 (x - x₀)) < R at hx
  exact ⟨x - x₀, hx.le, by simp⟩

/-- The points in an open Euclidean lattice ball. -/
def ball {d : ℕ} (x₀ : Site d) (R : ℝ) : Finset (Site d) :=
  (finite_ball x₀ R).toFinset

@[simp] theorem mem_ball {d : ℕ} (x₀ x : Site d) (R : ℝ) :
    x ∈ ball x₀ R ↔ radius (physical 1 (x - x₀)) < R := by
  simp [ball]

/-- The cutoff energy integrated over the enlarged ball, uniformly in the field and function.
The inequality holds for every real-valued function, including each form-domain function. -/
theorem exists_integrated_cutoff_energy_bound {d : ℕ} (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Edge d → ℝ),
      (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      ∀ (x₀ : Site d) (r₁ r₂ : ℝ), r₂ ≤ r₁ → 0 < r₂ →
      ∀ (c₀ : ℝ) (f : Site d → ℝ),
        (∑ x ∈ ball x₀ (r₁ + (1 + c₀) * r₂),
          f x ^ 2 * ∑' y : {y : Site d // y ≠ x},
            a (neighborEdge x y) * (radius (physical 1 (x - y.val)) ^ (d + 2))⁻¹ *
              (cutoff x₀ r₁ r₂ x - cutoff x₀ r₁ r₂ y.val) ^ 2) ≤
        C / scale r₂ * ∑ x ∈ ball x₀ (r₁ + (1 + c₀) * r₂), f x ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_cutoff_energy_bound_sites hd hlam hlam1
  refine ⟨C, hC, ?_⟩
  intro a ha x₀ r₁ r₂ hr₁ hr₂ c₀ f
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound a ha x₀ x r₁ r₂ hr₁ hr₂).2.2 (sq_nonneg _)

end LatticeProb.Analysis.IntegratedCutoffEnergy
