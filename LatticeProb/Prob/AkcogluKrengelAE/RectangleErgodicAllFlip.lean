/-
# Reflected actions and the arbitrary-anchor rectangle theorem

Because `Site d = Fin d → ℤ`, for any `z` the index `-z` is part of the data, and the reflected
action `reflectAction τ z := τ (-z)` is again measure-preserving and additive with the same
invariant sets — no invertibility of the maps `τ z` is used.  This lets the arbitrary-anchor
rectangle theorem (`RectangleErgodicAll`) be reduced to the `0 ≤ a` one (`RectangleErgodic`) by
reflecting the coordinates.
-/
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The reflected action `z ↦ τ (-z)`. -/
noncomputable def reflectAction {d : ℕ} (τ : Site d → Ω → Ω) : Site d → Ω → Ω :=
  fun z => τ (-z)

/-- **Transfer lemma.**  If `τ` is a measure-preserving additive `ℤᵈ`-action with trivial invariant
σ-algebra, then so is its reflection `reflectAction τ`, with the *same* invariant sets. -/
theorem reflectAction_props {d : ℕ} {μ : Measure Ω} {τ : Site d → Ω → Ω}
    (h1 : ∀ z, MeasurePreserving (τ z) μ μ)
    (h2 : ∀ z w ω, τ (z + w) ω = τ z (τ w ω))
    (h3 : ∀ A : Set Ω, MeasurableSet A → (∀ z, τ z ⁻¹' A = A) → μ A = 0 ∨ μ A = 1) :
    (∀ z, MeasurePreserving (reflectAction τ z) μ μ) ∧
      (∀ z w ω, reflectAction τ (z + w) ω = reflectAction τ z (reflectAction τ w ω)) ∧
      (∀ A : Set Ω, MeasurableSet A → (∀ z, (reflectAction τ z) ⁻¹' A = A) → μ A = 0 ∨ μ A = 1) := by
  refine ⟨fun z => h1 (-z), ?_, ?_⟩
  · intro z w ω
    show τ (-(z + w)) ω = τ (-z) (τ (-w) ω)
    rw [neg_add, h2 (-z) (-w)]
  · intro A hA hInv
    exact h3 A hA fun w => by simpa [reflectAction] using hInv (-w)

#print axioms reflectAction_props

end LatticeProb
