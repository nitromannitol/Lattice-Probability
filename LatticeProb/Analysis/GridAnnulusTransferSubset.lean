import LatticeProb.Analysis.GridAnnulusTransfer

/-!
# Grid annuli to all annuli, with test functions only on thick grid annuli inside a region

A variant of `exists_grid_admissible_energy_le`: test functions are needed only on the grid annuli
`B_{q^a}(z_i) \ B̄_{q^b}(z_i)` with `q^b ≤ q^a / 2` whose outer disc lies in a given region `W`, and the annulus
`B_r(z) \ B̄_s(z)` to be covered has its outer disc in `W`. The comparable grid annulus selected in the proof
(`exists_grid_annulus_comparable_mem`) satisfies both conditions, since its outer disc lies in `B_r(z)`.

This is the form used when the test functions come from a probabilistic estimate that holds only for annuli in a
fixed ball and with inner radius at most half of the outer radius (Berestycki–Gwynne, *Random walks on mated-CRT
planar maps and Liouville Brownian motion* (2020), Lemma 4.3, Step 2).
-/

namespace LatticeProb

open Metric

/-- **Grid annuli inside a region give test functions for all annuli in that region.** If every grid annulus of
`gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂` with `q^b ≤ q^a / 2` and `B_{q^a}(z_i) ⊆ W` carries a function `f i` equal to
`1` on the vertices meeting its closed inner disc, vanishing off the vertices meeting its outer disc, with
nonnegative energy and `log (q^a / q^b) E (f i) ≤ C`, then every annulus `B_r(z) \ B̄_s(z)` with `B_r(z) ⊆ W`,
`|z| ≤ ρ`, `η ≤ s / 100`, `3 s ≤ r`, `x₁ ≤ r / 2`, `r ≤ y₁`, `x₂ ≤ s`, `2 s ≤ y₂` carries one of them:
`f i = 1` on `V (B̄_s(z))`, `f i = 0` off `V (B_r(z))`, and `log (r / s) E (f i) ≤ 2 C`. -/
theorem exists_grid_admissible_energy_le_of_subset {α : Type*} {V : Set ℂ → Set α} (hV : Monotone V)
    {E : (α → ℝ) → ℝ} {f : ℤ × ℤ × ℤ × ℤ → α → ℝ} {q η ρ x₁ y₁ x₂ y₂ C : ℝ} {W : Set ℂ} (hq : 1 < q)
    (hq2 : q ^ 2 ≤ 29 / 20) (hη : 0 < η)
    (hgrid : ∀ i ∈ gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂, q ^ i.2.2.2 ≤ q ^ i.2.2.1 / 2 →
      ball ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) ⊆ W →
      (∀ a ∈ V (closedBall ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2)), f i a = 1) ∧
      (∀ a, a ∉ V (ball ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1)) → f i a = 0) ∧
      0 ≤ E (f i) ∧ Real.log (q ^ i.2.2.1 / q ^ i.2.2.2) * E (f i) ≤ C)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) {s r : ℝ} (hW : ball z r ⊆ W) (hηs : η ≤ s / 100) (hrs : 3 * s ≤ r)
    (hx₁ : 0 < x₁) (hx₁r : x₁ ≤ r / 2) (hy₁ : r ≤ y₁) (hx₂ : 0 < x₂) (hx₂s : x₂ ≤ s)
    (hy₂ : 2 * s ≤ y₂) :
    ∃ i ∈ gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂,
      (∀ a ∈ V (closedBall z s), f i a = 1) ∧ (∀ a, a ∉ V (ball z r) → f i a = 0) ∧
      Real.log (r / s) * E (f i) ≤ 2 * C := by
  obtain ⟨i, hi, -, hball, hcl, -, hba, -, -, -, -, hlog⟩ :=
    exists_grid_annulus_comparable_mem hq hq2 hη hz hηs hrs hx₁ hx₁r hy₁ hx₂ hx₂s hy₂
  obtain ⟨h1, h0, hE0, hEC⟩ := hgrid i hi hba (hball.trans hW)
  refine ⟨i, hi, fun a ha => h1 a (hV hcl ha), fun a ha => h0 a fun h => ha (hV hball h), ?_⟩
  calc Real.log (r / s) * E (f i)
      ≤ (2 * Real.log (q ^ i.2.2.1 / q ^ i.2.2.2)) * E (f i) := mul_le_mul_of_nonneg_right hlog hE0
    _ = 2 * (Real.log (q ^ i.2.2.1 / q ^ i.2.2.2) * E (f i)) := by ring
    _ ≤ 2 * C := by linarith

end LatticeProb
