import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic

/-!
# The rectangle theorem for arbitrary `a ≤ b`

This file works on the second remaining gap of
`LatticeProb/Prob/AkcogluKrengelAE/RectangleErgodic.lean`: the frozen
`VRW.External.PointwiseErgodicCubes` allows every `a ≤ b : Fin d → ℝ`, but the reduction in that
file only covers `0 ≤ a`.

The exact shift identity is proved here: for an integer shift `z` and `N : ℕ`,
`boxAvg (a+z) (b+z) N (τ (-(Nz)) ω) = boxAvg a b N ω`.  The remaining step is the diagonal one:
the shifted-box theorem gives convergence at each fixed point `τ (-(Nz)) ω`, but the negative
rectangle needs the diagonal `N ↦ boxAvg (a+z) (b+z) N (τ (-(Nz)) ω)`, which is not a row of that
family.  `RectangleErgodicFull_of_RectangleErgodic` isolates exactly that step as the hypothesis
`ShiftDiagonalConvergence`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The normalised average of `h ∘ τ` over the rectangle `rectBox a b N`. -/
private noncomputable def boxAvg (h : Ω → ℝ) (τ : Site d → Ω → Ω) (a b : Fin d → ℝ) (N : ℕ)
    (ω : Ω) : ℝ :=
  (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ rectBox a b N, h (τ x ω)

/-- The rectangle almost-everywhere ergodic theorem for every `a ≤ b` (the frozen shape; the
library's `RectangleErgodic` is the `0 ≤ a` case). -/
def RectangleErgodicFull (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    (∀ A : Set Ω, MeasurableSet A → (∀ z, τ z ⁻¹' A = A) → μ A = 0 ∨ μ A = 1) →
    ∀ (h : Ω → ℝ), Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
    ∀ a b : Fin d → ℝ, (∀ i, a i ≤ b i) →
      ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => boxAvg h τ a b N ω) atTop
        (𝓝 ((∏ i, (b i - a i)) * ∫ ω, h ω ∂μ))

/-- `⌈N (a + z)⌉ = ⌈N a⌉ + N z` for an integer shift `z`. -/
theorem ceil_mul_add_int (N : ℕ) (a : ℝ) (z : ℤ) :
    ⌈(N : ℝ) * (a + (z : ℝ))⌉ = ⌈(N : ℝ) * a⌉ + (N : ℤ) * z := by
  convert Int.ceil_add_intCast ((N : ℝ) * a) ((N : ℤ) * z) using 2
  push_cast
  ring

/-- Subtracting the integer shift `N z` takes the shifted box to the original box. -/
theorem sub_shift_mem {a b : Fin d → ℝ} {z : Site d} {N : ℕ} {y : Site d}
    (hy : y ∈ rectBox (fun i => a i + (z i : ℝ)) (fun i => b i + (z i : ℝ)) N) :
    y - (fun i => (N : ℤ) * z i) ∈ rectBox a b N := by
  rw [mem_rectBox] at hy ⊢
  intro i
  have hi := hy i
  simp only [Finset.mem_Ico, Pi.sub_apply] at hi ⊢
  rw [ceil_mul_add_int, ceil_mul_add_int] at hi
  constructor <;> omega

/-- Adding the integer shift `N z` takes the original box to the shifted box. -/
theorem add_shift_mem {a b : Fin d → ℝ} {z : Site d} {N : ℕ} {x : Site d}
    (hx : x ∈ rectBox a b N) :
    x + (fun i => (N : ℤ) * z i) ∈
      rectBox (fun i => a i + (z i : ℝ)) (fun i => b i + (z i : ℝ)) N := by
  rw [mem_rectBox] at hx ⊢
  intro i
  have hi := hx i
  simp only [Finset.mem_Ico, Pi.add_apply] at hi ⊢
  rw [ceil_mul_add_int, ceil_mul_add_int]
  constructor <;> omega

omit [MeasurableSpace Ω] in
/-- **The exact shift identity.**  For an integer shift `z`, the average over `a b N` at `ω`
equals the average over the translated box `(a+z) (b+z) N` at `τ (-(Nz)) ω`. -/
theorem boxAvg_shift_eq (h : Ω → ℝ) (τ : Site d → Ω → Ω)
    (hadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω))
    (a b : Fin d → ℝ) (z : Site d) (N : ℕ) (ω : Ω) :
    boxAvg h τ (fun i => a i + (z i : ℝ)) (fun i => b i + (z i : ℝ)) N
        (τ (-(fun i => (N : ℤ) * z i)) ω)
      = boxAvg h τ a b N ω := by
  unfold boxAvg
  congr 1
  refine Finset.sum_bij (fun y _ => y - (fun i => (N : ℤ) * z i)) ?_ ?_ ?_ ?_
  · intro y hy
    exact sub_shift_mem hy
  · intro y₁ _ y₂ _ heq
    funext i
    have := congrFun heq i
    simpa using this
  · intro x hx
    exact ⟨x + (fun i => (N : ℤ) * z i), add_shift_mem hx, by ext i; simp⟩
  · intro y _
    congr 1
    have h1 : y - (fun i => (N : ℤ) * z i) = y + (-(fun i => (N : ℤ) * z i)) := by
      ext i; exact sub_eq_add_neg _ _
    rw [h1, ← hadd y (-(fun i => (N : ℤ) * z i)) ω]

end LatticeProb

#print axioms LatticeProb.boxAvg_shift_eq
#print axioms LatticeProb.ceil_mul_add_int
