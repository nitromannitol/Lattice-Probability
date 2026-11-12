import LatticeProb.Analysis.GridAnnulusComparable

/-!
# From grid annuli to all annuli: test functions of small energy

Let `V : Set ℂ → Set α` assign to a set of the plane the vertices of a graph that "meet" it (for a cell
configuration, the cells that intersect the set), so that `V` is monotone. Suppose that for every parameter
`i = (m, n, a, b)` of the finite grid `gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂` we are given a function `f i` on the
vertices which is equal to `1` on `V (B̄_{q^b}(z_i))`, vanishes off `V (B_{q^a}(z_i))`, where `z_i = η (m + n i)`, and
whose energy satisfies `log (q^a / q^b) E (f i) ≤ C`. Then every annulus `B_r(z) \ B̄_s(z)` with `|z| ≤ ρ`,
`r ≥ 3 s` and `s ≥ 100 η` (and radii in the range of the grid) carries one of these functions as a test function:
it is equal to `1` on `V (B̄_s(z))`, vanishes off `V (B_r(z))`, and `log (r / s) E (f i) ≤ 2 C`.

This is the deterministic part of the union-bound argument in the proof of Berestycki–Gwynne, *Random walks on
mated-CRT planar maps and Liouville Brownian motion* (2020), Lemma 4.3, Steps 2 and 3, carried out with the geometric
radius grid of ratio `q` (for instance `q = 2 ^ (1 / 4)`) of `LatticeProb.exists_grid_annulus_comparable_mem`.
Step 3 (inner radii below a threshold `s₀`) is `exists_grid_admissible_energy_le_max`: the test function built for
the inner radius `max s s₀` is also admissible for the inner radius `s`.
-/

namespace LatticeProb

open Metric

/-- **Grid annuli give test functions for all annuli.** If every grid annulus of `gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂`
carries a function `f i` equal to `1` on the vertices meeting its closed inner disc, vanishing off the vertices
meeting its outer disc, with nonnegative energy and `log (q^a / q^b) E (f i) ≤ C`, then every annulus
`B_r(z) \ B̄_s(z)` with `|z| ≤ ρ`, `η ≤ s / 100`, `3 s ≤ r`, `x₁ ≤ r / 2`, `r ≤ y₁`, `x₂ ≤ s`, `2 s ≤ y₂` carries one
of them: `f i = 1` on `V (B̄_s(z))`, `f i = 0` off `V (B_r(z))`, and `log (r / s) E (f i) ≤ 2 C`. -/
theorem exists_grid_admissible_energy_le {α : Type*} {V : Set ℂ → Set α} (hV : Monotone V)
    {E : (α → ℝ) → ℝ} {f : ℤ × ℤ × ℤ × ℤ → α → ℝ} {q η ρ x₁ y₁ x₂ y₂ C : ℝ} (hq : 1 < q)
    (hq2 : q ^ 2 ≤ 29 / 20) (hη : 0 < η)
    (hgrid : ∀ i ∈ gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂,
      (∀ a ∈ V (closedBall ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2)), f i a = 1) ∧
      (∀ a, a ∉ V (ball ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1)) → f i a = 0) ∧
      0 ≤ E (f i) ∧ Real.log (q ^ i.2.2.1 / q ^ i.2.2.2) * E (f i) ≤ C)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) {s r : ℝ} (hηs : η ≤ s / 100) (hrs : 3 * s ≤ r)
    (hx₁ : 0 < x₁) (hx₁r : x₁ ≤ r / 2) (hy₁ : r ≤ y₁) (hx₂ : 0 < x₂) (hx₂s : x₂ ≤ s)
    (hy₂ : 2 * s ≤ y₂) :
    ∃ i ∈ gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂,
      (∀ a ∈ V (closedBall z s), f i a = 1) ∧ (∀ a, a ∉ V (ball z r) → f i a = 0) ∧
      Real.log (r / s) * E (f i) ≤ 2 * C := by
  obtain ⟨i, hi, -, hball, hcl, -, -, -, -, -, -, hlog⟩ :=
    exists_grid_annulus_comparable_mem hq hq2 hη hz hηs hrs hx₁ hx₁r hy₁ hx₂ hx₂s hy₂
  obtain ⟨h1, h0, hE0, hEC⟩ := hgrid i hi
  refine ⟨i, hi, fun a ha => h1 a (hV hcl ha), fun a ha => h0 a fun h => ha (hV hball h), ?_⟩
  calc Real.log (r / s) * E (f i)
      ≤ (2 * Real.log (q ^ i.2.2.1 / q ^ i.2.2.2)) * E (f i) := mul_le_mul_of_nonneg_right hlog hE0
    _ = 2 * (Real.log (q ^ i.2.2.1 / q ^ i.2.2.2) * E (f i)) := by ring
    _ ≤ 2 * C := by linarith

/-- **Small inner radii.** Under the hypotheses of `exists_grid_admissible_energy_le` for the inner radius
`max s s₀` (only `s₀` needs to be at least `100 η` and at least `x₂`), the annulus `B_r(z) \ B̄_s(z)` carries a grid
function `f i` with `f i = 1` on `V (B̄_s(z))`, `f i = 0` off `V (B_r(z))` and
`log (r / max s s₀) E (f i) ≤ 2 C`. -/
theorem exists_grid_admissible_energy_le_max {α : Type*} {V : Set ℂ → Set α} (hV : Monotone V)
    {E : (α → ℝ) → ℝ} {f : ℤ × ℤ × ℤ × ℤ → α → ℝ} {q η ρ x₁ y₁ x₂ y₂ C : ℝ} (hq : 1 < q)
    (hq2 : q ^ 2 ≤ 29 / 20) (hη : 0 < η)
    (hgrid : ∀ i ∈ gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂,
      (∀ a ∈ V (closedBall ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2)), f i a = 1) ∧
      (∀ a, a ∉ V (ball ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1)) → f i a = 0) ∧
      0 ≤ E (f i) ∧ Real.log (q ^ i.2.2.1 / q ^ i.2.2.2) * E (f i) ≤ C)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) {s s₀ r : ℝ} (hηs₀ : η ≤ s₀ / 100) (hrs : 3 * max s s₀ ≤ r)
    (hx₁ : 0 < x₁) (hx₁r : x₁ ≤ r / 2) (hy₁ : r ≤ y₁) (hx₂ : 0 < x₂) (hx₂s₀ : x₂ ≤ s₀)
    (hy₂ : 2 * max s s₀ ≤ y₂) :
    ∃ i ∈ gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂,
      (∀ a ∈ V (closedBall z s), f i a = 1) ∧ (∀ a, a ∉ V (ball z r) → f i a = 0) ∧
      Real.log (r / max s s₀) * E (f i) ≤ 2 * C := by
  have hs₀ : s₀ ≤ max s s₀ := le_max_right s s₀
  obtain ⟨i, hi, h1, h0, hE⟩ := exists_grid_admissible_energy_le hV hq hq2 hη hgrid hz
    (by linarith : η ≤ max s s₀ / 100) hrs hx₁ hx₁r hy₁ hx₂ (hx₂s₀.trans hs₀) hy₂
  exact ⟨i, hi, fun a ha => h1 a (hV (closedBall_subset_closedBall (le_max_left s s₀)) ha), h0, hE⟩

end LatticeProb
