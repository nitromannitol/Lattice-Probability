import LatticeProb.Prob.Percolation.ComponentGradientBonds
import LatticeProb.Prob.Percolation.MeasurableRootedPlane

/-!
# Cofinite constancy from finite integer-gradient energy

All-finite-flips uniqueness supplies unique infinitude after the canonical gradient patch
is deleted. This produces the exact deleted-component hypothesis of the network theorem.
On a flip-stable subset of the genuine corrector validity event, uniqueness is derived
from event membership at the actual configuration and its actual canonical flip.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open scoped BigOperators

variable {d : ℕ} {ω : Configuration d}

/-- Integer drops and bounded finite ordered energy sums make the canonical edge set finite. -/
theorem componentGradientEdges_finite_of_integer_energy (C : OpenComponent ω) (w : C → ℝ)
    (hint : ∀ x y, (componentGraph C).Adj x y → ∃ z : ℤ, w x - w y = (z : ℝ))
    (henergy : ∃ M : ℝ, ∀ A : Finset (C × C),
      (∀ e ∈ A, (componentGraph C).Adj e.1 e.2) →
        ∑ e ∈ A, (w e.1 - w e.2) ^ 2 ≤ M) :
    (componentGradientEdges C w).Finite :=
  Network.finite_nonzero_gradient_edges hint henergy

/-- Uniqueness after the canonical flip produces uniqueness for the exact deleted graph. -/
theorem componentGradient_deleted_existsUnique_infinite (C : OpenComponent ω) (w : C → ℝ)
    (hfinite : (componentGradientEdges C w).Finite)
    (hOld : HasUniqueInfiniteOpenComponent ω) (hC : C.supp.Infinite)
    (hNew : HasUniqueInfiniteOpenComponent
      (finiteBondFlip (componentGradientPatch C w hfinite) ω)) :
    ∃! K : ((componentGraph C).deleteEdges (componentGradientEdges C w)).ConnectedComponent,
      K.supp.Infinite := by
  have hEq : C = uniqueInfiniteComponent hOld :=
    (eq_uniqueInfiniteComponent_iff hOld C).mpr hC
  have huniq := finiteBondFlip_induce_existsUnique_infinite_component
    (componentGradientPatch C w hfinite) hOld hNew (componentGradientPatch_all_open C w hfinite)
  rw [← hEq, componentGradientPatch_induce_eq_deleteEdges] at huniq
  exact huniq

/-- Conditional graph helper: actual all-finite-flips uniqueness and integer-gradient energy
produce cofinite constancy, without assuming uniqueness of the deleted graph. -/
theorem exists_finite_exception_constant_of_all_finite_flips_unique
    (C : OpenComponent ω) (hC : C.supp.Infinite)
    (hOld : HasUniqueInfiniteOpenComponent ω)
    (hflips : ∀ F : Finset (Bond d), HasUniqueInfiniteOpenComponent (finiteBondFlip F ω))
    (w : C → ℝ)
    (hint : ∀ x y, (componentGraph C).Adj x y → ∃ z : ℤ, w x - w y = (z : ℝ))
    (henergy : ∃ M : ℝ, ∀ A : Finset (C × C),
      (∀ e ∈ A, (componentGraph C).Adj e.1 e.2) →
        ∑ e ∈ A, (w e.1 - w e.2) ^ 2 ≤ M) :
    ∃ S : Set C, S.Finite ∧ ∃ c : ℝ, ∀ x, x ∉ S → w x = c := by
  have hfinite := componentGradientEdges_finite_of_integer_energy C w hint henergy
  obtain ⟨K, hK, huniq⟩ := componentGradient_deleted_existsUnique_infinite C w hfinite
    hOld hC (hflips (componentGradientPatch C w hfinite))
  exact Network.exists_finite_exception_constant_of_integer_gradient_energy
    C.connected_toSimpleGraph hint henergy K hK huniq

/-- On any actual configuration in a flip-stable subset of the genuine validity event,
finite integer-gradient energy gives a real constant outside a finite vertex set. -/
theorem exists_finite_exception_constant_on_flip_stable_valid_set
    (G : Set (Configuration d)) (hvalid : G ⊆ correctorValidEvent d)
    (hstable : ∀ F : Finset (Bond d), ∀ η ∈ G, finiteBondFlip F η ∈ G)
    (hω : ω ∈ G) (C : OpenComponent ω) (hC : C.supp.Infinite) (w : C → ℝ)
    (hint : ∀ x y, (componentGraph C).Adj x y → ∃ z : ℤ, w x - w y = (z : ℝ))
    (henergy : ∃ M : ℝ, ∀ A : Finset (C × C),
      (∀ e ∈ A, (componentGraph C).Adj e.1 e.2) →
        ∑ e ∈ A, (w e.1 - w e.2) ^ 2 ≤ M) :
    ∃ S : Set C, S.Finite ∧ ∃ c : ℝ, ∀ x, x ∉ S → w x = c := by
  exact exists_finite_exception_constant_of_all_finite_flips_unique C hC (hvalid hω).1
    (fun F => (hvalid (hstable F ω hω)).1) w hint henergy

/-- The source-valid-event conclusion with a finite enumeration of exceptional vertices. -/
theorem exists_finset_exception_constant_on_flip_stable_valid_set
    (G : Set (Configuration d)) (hvalid : G ⊆ correctorValidEvent d)
    (hstable : ∀ F : Finset (Bond d), ∀ η ∈ G, finiteBondFlip F η ∈ G)
    (hω : ω ∈ G) (C : OpenComponent ω) (hC : C.supp.Infinite) (w : C → ℝ)
    (hint : ∀ x y, (componentGraph C).Adj x y → ∃ z : ℤ, w x - w y = (z : ℝ))
    (henergy : ∃ M : ℝ, ∀ A : Finset (C × C),
      (∀ e ∈ A, (componentGraph C).Adj e.1 e.2) →
        ∑ e ∈ A, (w e.1 - w e.2) ^ 2 ≤ M) :
    ∃ S : Finset C, ∃ c : ℝ, ∀ x, x ∉ S → w x = c := by
  obtain ⟨S, hS, c, hc⟩ := exists_finite_exception_constant_on_flip_stable_valid_set
    G hvalid hstable hω C hC w hint henergy
  exact ⟨hS.toFinset, c, fun x hx => hc x (by simpa only [Set.Finite.mem_toFinset] using hx)⟩

end LatticeProb.Percolation
