import LatticeProb.Walk.PhysicalBrownianAbsorbedComparison
import LatticeProb.Walk.PhysicalGoodExcursionAnchors

/-! # Absorbed path comparison from good excursions -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal ENNReal
open LatticeProb.ParentBlock LatticeProb.CellConfigInterpolation

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- Good paired excursions and an initial distance bound control the physical walk
and Brownian paths through their finite absorbed skeleton endpoints. -/
theorem physical_brownian_absorbed_comparison_of_good_excursions
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (H : CellConfig) (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ C, p C ∈ (C.1 : Set Plane)) (cell : V → H.cells)
    (centres : J → ℂ) (initial : J) (select : ℕ → V → Option J) (ω : ℕ → V)
    (hpos : ∀ C, 0 < H.holding C) (hunb : H.JumpTimesUnbounded (cell ∘ ω))
    (hadj : ∀ n, H.Adj (cell (ω n)) (cell (ω (n + 1))))
    {ε : ℝ≥0} (hε : 0 < ε) (a : ℂ) (S s r R δ : ℝ)
    (hS : 0 ≤ S) (hs : 0 < s) (hδ : 0 ≤ δ) (hr : 4 * S < r)
    (hmargin : r + 4 * s + (ε : ℝ) * δ ≤ R)
    (houter : Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell (ω 0))) ∈
      parentBlock a S)
    (hinit : Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell (ω 0))) ∈
      closedSquare (centres initial) s)
    (hselect : ∀ n v j, select n v = some j →
      Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈ parentBlock a S ∧
      Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        closedSquare (centres j) s)
    (hmesh : ∀ C : H.cells, (∃ z ∈ (C.1 : Set Plane),
      (ε : ℝ) • z ∈ Metric.ball (Complex.orthonormalBasisOneI.repr a) R) →
      Metric.diam (C.1 : Set Plane) ≤ δ)
    (K : ℕ) (k : ℕ → ℕ)
    (hclock : ∀ i ≤ K, (actualWalkStage (fun v => (ε : ℝ) • p (cell v))
      (fun j => {v | Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        parentBlock (centres j) s}) initial select i ω).1 = k i)
    (z : Euc 2) (j₀ : J) (selector : ℕ → Euc 2 → Option J) (β : BrownianPath 2)
    (hbselect : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ parentBlock a S ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈ closedSquare (centres j) s)
    (hbstart : Complex.orthonormalBasisOneI.repr.symm (z + β 0) ∈ closedSquare (centres j₀) s)
    (hbStop : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹' interior (parentBlock (centres j) s))
      z j₀ selector K β).1 = true)
    (hbFinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹' interior (parentBlock (centres j) s))
      z j₀ selector K β).2 ≠ ∞)
    (η : ℝ)
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc 2))
    (hstart : dist (H.interpolatedWalk p ε (cell ∘ ω) 0) (z + β 0) ≤ η)
    (hdiam : ∀ i ≤ K, ∀ j, ∀ x ∈ E i j, ∀ y ∈ E i j, dist x y ≤ η)
    (hgood : ∀ i ≤ K,
      ((actualWalkStage (fun v => (ε : ℝ) • p (cell v))
        (fun j => {v | Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
          parentBlock (centres j) s}) initial select i ω).2,
        brownianSkeletonExcursion
          (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (centres j) s)) z j₀ selector i β) ∈
          goodExcursionPair (fun v => (ε : ℝ) • p (cell v)) (E i) η) :
    let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
      (fun i => scaledJumpTime H (cell ∘ ω) hpos ε (k (min i K)))
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (parentBlock (centres j) s)
    let Q : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
      (fun i => (brownianSkeletonClock U z j₀ selector (min i K) β).2.toNNReal)
    ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t,
      dist (Complex.orthonormalBasisOneI.repr.symm
        (H.interpolatedWalk p ε (cell ∘ ω) (min t (T (K + 1)))))
        (Complex.orthonormalBasisOneI.repr.symm (z + β (min (φ t) (Q (K + 1))))) ≤
        max ((ε : ℝ) * (2 * δ) + 4 * s) (4 * s + 4 * s) + η +
          max ((ε : ℝ) * (2 * δ) + 4 * s) (4 * s + 4 * s) := by
  apply physical_brownian_absorbed_comparison H hH p hp cell centres initial select ω
    hpos hunb hadj hε a S s r R δ hS hs hδ hr hmargin houter hinit hselect hmesh
    K k hclock z j₀ selector β hbselect hbstart hbStop hbFinite η
  exact physical_skeleton_anchor_bounds_of_good_excursions H p cell
    (fun j => {v | Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
      parentBlock (centres j) s}) initial select ω hpos hunb hε K k hclock
    (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (parentBlock (centres j) s)) z j₀ selector β hbFinite η m E hstart hdiam hgood

end BouRabeeGwynne.FiniteConductanceNetwork
end
