import LatticeProb.Prob.Percolation.LatticePoissonPole

/-!
# A Poisson pole on the fully open lattice

The zero real potential on the actual component of the origin in the fully open planar
configuration consumes the general producer. Its ambient pole is characterized as zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation.LatticePoissonPoleConsumer

/-- The actual open-graph component of the origin in the fully open planar configuration. -/
abbrev originComponent : OpenComponent (allOpen 2) :=
  (openGraph (allOpen 2)).connectedComponentMk 0

/-- The general producer supplies the finite ambient pole for the zero real potential. -/
theorem exists_zero_potential_pole :
    ∃ g : Vertex 2 → ℤ, Function.HasFiniteSupport g ∧
      (∀ x : originComponent,
        -componentLaplacian originComponent (fun _ => (0 : ℝ)) x = (g x.val : ℝ)) ∧
      (∀ x ∉ originComponent.supp, g x = 0) ∧ g = fun _ => 0 := by
  have hlap (x : originComponent) :
      -componentLaplacian originComponent (fun _ => (0 : ℝ)) x = 0 := by
    simp only [componentLaplacian, sub_self, Finset.sum_const_zero, neg_zero]
  have hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
      ∀ x : originComponent, (R : ℝ) < ∑ j, |(x.val j : ℝ)| → |(0 : ℝ)| < ε := by
    intro ε hε
    exact ⟨0, fun _ _ => by simpa only [abs_zero] using hε⟩
  obtain ⟨_, g, _, hgfinite, _, _, hgeq, hgzero⟩ :=
    exists_lattice_pole_of_real_abs_decay originComponent (fun _ => (0 : ℝ))
      hdecay (fun x => ⟨0, by simpa only [Int.cast_zero] using hlap x⟩)
  refine ⟨g, hgfinite, hgeq, hgzero, ?_⟩
  exact lattice_pole_unique originComponent (fun _ => (0 : ℝ)) g (fun _ => 0)
    hgeq (fun x => by simpa only [Int.cast_zero] using hlap x) hgzero (fun _ _ => rfl)

end LatticeProb.Percolation.LatticePoissonPoleConsumer
