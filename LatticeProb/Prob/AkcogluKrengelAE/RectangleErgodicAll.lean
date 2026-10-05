/-
# The arbitrary-`a` extension of the rectangle ergodic theorem

The library's `LatticeProb.RectangleErgodic` (`RectangleErgodic.lean:270`) assumes `0 ≤ a`; the
frozen node `VRW.External.PointwiseErgodicCubes` allows arbitrary `a ≤ b`.  This file supplies the
pure-algebra core of the extension: translating `rectBox a b N` by `-⌈N aᵢ⌉` turns it into the
anchored box `∏ᵢ [0, ⌈N bᵢ⌉ - ⌈N aᵢ⌉)`, and each width `⌈N bᵢ⌉ - ⌈N aᵢ⌉` differs from `⌈N (b - a)ᵢ⌉`
by at most `1` (`ceil_sub_le`, `ceil_sub_le'`).  The sandwich
`∏ᵢ [0, ⌈N cᵢ⌉ - 1) ⊆ ∏ᵢ [0, ⌈N bᵢ⌉ - ⌈N aᵢ⌉) ⊆ ∏ᵢ [0, ⌈N cᵢ⌉)` (with `c = b - a`) therefore
reduces the arbitrary-`a` case to the `0 ≤ a` case at the shifted scales `N ± K`; the a.e.-scale
assembly is isolated as `RectangleErgodicAllReduction`.
-/
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators

namespace LatticeProb

/-- `⌈x⌉ - ⌈y⌉ ≤ ⌈x - y⌉`. -/
theorem ceil_sub_le (x y : ℝ) : ⌈x⌉ - ⌈y⌉ ≤ ⌈x - y⌉ := by
  have h := Int.ceil_add_le (y) (x - y)
  have e : y + (x - y) = x := by ring
  rw [e] at h; linarith

/-- `⌈x - y⌉ - 1 ≤ ⌈x⌉ - ⌈y⌉`. -/
theorem ceil_sub_le' (x y : ℝ) : ⌈x - y⌉ - 1 ≤ ⌈x⌉ - ⌈y⌉ := by
  have h := Int.ceil_add_ceil_le (y) (x - y)
  have e : y + (x - y) = x := by ring
  rw [e] at h; linarith

/-- Translating `rectBox a b N` by `-⌈N aᵢ⌉` gives the anchored box with side
`⌈N bᵢ⌉ - ⌈N aᵢ⌉`. -/
theorem map_addRight_rectBox {d : ℕ} (a b : Fin d → ℝ) (N : ℕ) :
    (rectBox a b N).map (Equiv.addRight (fun i => -⌈(N:ℝ) * a i⌉)).toEmbedding =
      Fintype.piFinset (fun i => Finset.Ico (0:ℤ) (⌈(N:ℝ) * b i⌉ - ⌈(N:ℝ) * a i⌉)) := by
  ext x
  simp only [Finset.mem_map, mem_rectBox, Fintype.mem_piFinset]
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro i
    have hi := hy i
    simp only [Finset.mem_Ico] at hi ⊢
    simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight, Pi.add_apply]
    omega
  · intro hx
    refine ⟨fun i => x i + ⌈(N:ℝ) * a i⌉, fun i => ?_, ?_⟩
    · have hi := hx i
      simp only [Finset.mem_Ico] at hi ⊢
      omega
    · ext i
      simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight, Pi.add_apply]
      have hi := hx i
      simp only [Finset.mem_Ico] at hi
      omega

/-- The rectangle a.e. ergodic theorem for arbitrary `a ≤ b` (no positivity hypothesis). -/
def RectangleErgodicAll (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    (∀ A : Set Ω, MeasurableSet A → (∀ z, τ z ⁻¹' A = A) → μ A = 0 ∨ μ A = 1) →
    ∀ (h : Ω → ℝ), Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
    ∀ a b : Fin d → ℝ, (∀ i, a i ≤ b i) →
      ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
          ∑ x ∈ rectBox a b N, h (τ x ω)) atTop (𝓝 ((∏ i, (b i - a i)) * ∫ ω, h ω ∂μ))

/-- **The arbitrary-`a` extension, reduced.**  The width sandwich described in the header (with
`ceil_sub_le`, `ceil_sub_le'`, `map_addRight_rectBox`) reduces `RectangleErgodicAll` to
`RectangleErgodic`; the a.e.-scale assembly is the residual of this `Prop`. -/
def RectangleErgodicAllReduction (d : ℕ) : Prop := RectangleErgodic d → RectangleErgodicAll d

#print axioms map_addRight_rectBox
#print axioms ceil_sub_le
#print axioms ceil_sub_le'

end LatticeProb
