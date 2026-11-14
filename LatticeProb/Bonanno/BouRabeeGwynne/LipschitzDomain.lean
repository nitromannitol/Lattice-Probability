/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.LipschitzDomain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.PaperObjects

open scoped Topology NNReal

namespace BouRabeeGwynne

/-- Orthogonal cylinder coordinates with one distinguished vertical coordinate.
For `d = 1`, the horizontal coordinate space has dimension zero. -/
def cylinderCoordinates {d : ℕ} (q : Euc (d - 1)) (t : ℝ) :
    EuclideanSpace ℝ (Option (Fin (d - 1))) :=
  WithLp.toLp 2 (fun i => Option.casesOn i t (fun j => q j))

/-- Genuine local Lipschitz graph charts for the boundary. Each chart is a rigid
orthogonal coordinate system centered at a boundary point; in a positive open
cylinder, the domain is exactly the strict epigraph of a Lipschitz function.

This is the standard geometric cylinder definition, not a probabilistic exit
regularity assumption. Compare the definition on page 111 of
https://numdam.org/item/10.5802/aif.1062.pdf. The graph stays strictly between the
cylinder bases, and its value at the centered boundary point is zero. -/
def HasLipschitzBoundary {d : ℕ} (U : Set (Euc d)) : Prop :=
  ∀ p ∈ frontier U, ∃ r : ℝ, ∃ h : ℝ, 0 < r ∧ 0 < h ∧
    ∃ R : Euc d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Option (Fin (d - 1))),
    ∃ φ : Euc (d - 1) → ℝ, ∃ K : ℝ≥0,
      LipschitzWith K φ ∧ φ 0 = 0 ∧
      (∀ q : Euc (d - 1), ‖q‖ < r → |φ q| < h) ∧
      ∀ q : Euc (d - 1), ∀ t : ℝ, ‖q‖ < r → |t| < h →
        (p + R.symm (cylinderCoordinates q t) ∈ U ↔ φ q < t)

/-- An open, nonempty, connected domain with genuine local Lipschitz graph charts.
Boundedness is stated separately in Theorems A and B. -/
def IsLipschitzDomain {d : ℕ} (U : Set (Euc d)) : Prop :=
  IsDomain U ∧ HasLipschitzBoundary U

lemma IsLipschitzDomain.isDomain {d : ℕ} {U : Set (Euc d)}
    (h : IsLipschitzDomain U) : IsDomain U := h.1

lemma IsLipschitzDomain.hasLipschitzBoundary {d : ℕ} {U : Set (Euc d)}
    (h : IsLipschitzDomain U) : HasLipschitzBoundary U := h.2

end BouRabeeGwynne
