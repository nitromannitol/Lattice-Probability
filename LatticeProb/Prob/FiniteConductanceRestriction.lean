import LatticeProb.Bonanno.BouRabeeGwynne.StoppedWalk

/-! # Finite restrictions of conductance networks

Restricting a conductance network to a finite set preserves the total
conductance and the interior transition row when no conductance is discarded.
-/

set_option autoImplicit false

open scoped BigOperators

namespace LatticeProb

variable {V : Type*} (c : V → V → ℝ)
variable (hsymm : ∀ v w, c v w = c w v)
variable (hnonneg : ∀ v w, 0 ≤ c v w) (hloop : ∀ v, c v v = 0)

/-- The network induced by a finite set of vertices. -/
def finiteConductanceRestriction (R : Set V) [Fintype R] :
    BouRabeeGwynne.FiniteConductanceNetwork R where
  a v w := c v w
  symm v w := hsymm v w
  nonneg v w := hnonneg v w
  loop_zero v := hloop v

/-- Retaining every nonzero neighbor retains the ambient total conductance. -/
theorem finiteConductanceRestriction_total (R : Set V) [Fintype R] (v : R)
    (hretain : ∀ w, w ∉ R → c v w = 0) :
    (finiteConductanceRestriction c hsymm hnonneg hloop R).totalConductance v =
      ∑' w, c v w := by
  change (∑ w : R, c v w) = ∑' w, c v w
  have hs : (fun w => c v w).support ⊆ R := by
    intro w hw
    by_contra hn
    exact hw (hretain w hn)
  simpa only [tsum_fintype] using
    (tsum_subtype_eq_of_support_subset hs : (∑' w : R, c v w) = ∑' w, c v w)

/-- At an active vertex the restricted and ambient normalized rows agree. -/
theorem finiteConductanceRestriction_transition (R : Set V) [Fintype R]
    (A : Set R) (v w : R) (hv : v ∈ A)
    (hretain : ∀ z, z ∉ R → c v z = 0) :
    (finiteConductanceRestriction c hsymm hnonneg hloop R).transitionProbability A v w =
      c v w / (∑' z, c v z) := by
  classical
  simp only [BouRabeeGwynne.FiniteConductanceNetwork.transitionProbability, hv, ↓reduceIte]
  rw [finiteConductanceRestriction_total c hsymm hnonneg hloop R v hretain]
  rfl

end LatticeProb
