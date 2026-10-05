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

/-- Coordinate-wise reflection in a subset `S` of the coordinates. -/
noncomputable def flipSubset {d : ℕ} (S : Finset (Fin d)) : Site d → Site d :=
  fun x i => if i ∈ S then -x i else x i

theorem flipSubset_add {d : ℕ} (S : Finset (Fin d)) (z w : Site d) :
    flipSubset S (z + w) = flipSubset S z + flipSubset S w := by
  funext i
  by_cases hi : i ∈ S
  · simp only [flipSubset, hi, if_true, Pi.add_apply]; abel
  · simp only [flipSubset, hi, if_false, Pi.add_apply]

theorem flipSubset_involutive {d : ℕ} (S : Finset (Fin d)) (z : Site d) :
    flipSubset S (flipSubset S z) = z := by
  funext i
  by_cases hi : i ∈ S <;> simp [flipSubset, hi]

/-- The action reflected in the coordinate subset `S`. -/
noncomputable def reflectActionS {d : ℕ} (τ : Site d → Ω → Ω) (S : Finset (Fin d)) :
    Site d → Ω → Ω :=
  fun z => τ (flipSubset S z)

/-- **Transfer lemma (general flip).**  For every coordinate subset `S`, the reflected action
`reflectActionS τ S` is again measure-preserving and additive, with the *same* invariant sets as
`τ` (no invertibility of the maps `τ z` is used, only that `flipSubset S` is an involutive
automorphism of `Site d`). -/
theorem reflectActionS_props {d : ℕ} {μ : Measure Ω} {τ : Site d → Ω → Ω}
    (h1 : ∀ z, MeasurePreserving (τ z) μ μ)
    (h2 : ∀ z w ω, τ (z + w) ω = τ z (τ w ω))
    (h3 : ∀ A : Set Ω, MeasurableSet A → (∀ z, τ z ⁻¹' A = A) → μ A = 0 ∨ μ A = 1)
    (S : Finset (Fin d)) :
    (∀ z, MeasurePreserving (reflectActionS τ S z) μ μ) ∧
      (∀ z w ω, reflectActionS τ S (z + w) ω = reflectActionS τ S z (reflectActionS τ S w ω)) ∧
      (∀ A : Set Ω, MeasurableSet A → (∀ z, (reflectActionS τ S z) ⁻¹' A = A) → μ A = 0 ∨ μ A = 1) := by
  refine ⟨fun z => h1 (flipSubset S z), ?_, ?_⟩
  · intro z w ω
    show τ (flipSubset S (z + w)) ω = τ (flipSubset S z) (τ (flipSubset S w) ω)
    rw [flipSubset_add, h2]
  · intro A hA hInv
    refine h3 A hA fun w => ?_
    have := hInv (flipSubset S w)
    simpa [reflectActionS, flipSubset_involutive] using this

#print axioms reflectActionS_props
#print axioms flipSubset_add
#print axioms flipSubset_involutive

end LatticeProb
