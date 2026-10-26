import LatticeProb.Prob.Percolation.MeasurableCorrectorGradients
import LatticeProb.Prob.Percolation.SupercriticalBondUniquenessConsumer

/-!
# A nonzero coefficient on an actual infinite-component edge

The same two literature inputs give a strictly supercritical two-dimensional law and a
configuration in the conull valid set. The unique-slope clause makes its first coordinate
plane nonconstant. Connectedness forces a nonzero drop on an actual component edge, so
the measurable coefficient field cannot be identically zero there.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory LatticeProb.External
open scoped BigOperators

/-- The actual coefficient producer has a nonzero coordinate on a legitimate open edge
of the unique infinite component, without a fixed-root positive-probability premise. -/
theorem exists_nonzero_measurable_corrector_gradient_of_cited_inputs
    (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput) :
    ∃ p : unitInterval, criticalProbability 2 < (p : ℝ) ∧ (p : ℝ) < 1 ∧
      ∃ G : Set (Configuration 2), MeasurableSet G ∧ latticeBondLaw 2 p G = 1 ∧
        ∃ hvalid : G ⊆ correctorValidEvent 2,
          ∃ g : G → (Vertex 2 × Vertex 2) → Fin 2 → ℝ,
            (∀ e j, Measurable (fun ω => g ω e j)) ∧
            (∀ (ω : G) (q : Fin 2 → ℝ)
              (u : uniqueInfiniteComponent (hvalid ω.property).1 → ℝ),
              IsCorrectedPlane (uniqueInfiniteComponent (hvalid ω.property).1) q u →
              ∀ x y : uniqueInfiniteComponent (hvalid ω.property).1,
                (openGraph ω.val).Adj x.val y.val →
                ∑ j, q j * g ω (x.val, y.val) j = u y - u x) ∧
            (∀ (ω : G) (q : Fin 2 → ℝ),
              q ∈ LatticeProb.Prob.Percolation.integerSlopeSubgroup (g ω) ↔
                ∃ u : uniqueInfiniteComponent (hvalid ω.property).1 → ℝ,
                  IsCorrectedPlane (uniqueInfiniteComponent (hvalid ω.property).1) q u ∧
                  ∀ x y : uniqueInfiniteComponent (hvalid ω.property).1,
                    (openGraph ω.val).Adj x.val y.val →
                      ∃ z : ℤ, u y - u x = (z : ℝ)) ∧
            ∃ (ω : G) (x y : uniqueInfiniteComponent (hvalid ω.property).1),
              (openGraph ω.val).Adj x.val y.val ∧ g ω (x.val, y.val) 0 ≠ 0 := by
  classical
  obtain ⟨p, hpc, hp1⟩ := exists_supercritical_parameter_of_classical_input hclassical 2
    (by decide)
  obtain ⟨G, hG, hmass, hvalid, g, hmeas, _, hgradient, hiff⟩ :=
    exists_measurable_corrector_gradients_of_cited_inputs hclassical hcorrector 2
      (by decide) p hpc hp1
  have hae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G :=
    (mem_ae_iff_prob_eq_one hG).mpr hmass
  obtain ⟨ω, hω⟩ := hae.exists
  let w : G := ⟨ω, hω⟩
  let C := uniqueInfiniteComponent (hvalid w.property).1
  obtain ⟨o, ho⟩ := C.nonempty_supp
  let root : C := ⟨o, ho⟩
  obtain ⟨u, hu, _⟩ := ((hvalid w.property).2 (hvalid w.property).1).1
    (Pi.single 0 1) root
  have hedge : ∃ x y : C, (componentGraph C).Adj x y ∧ u x ≠ u y := by
    by_contra hnone
    have heq : ∀ x y : C, (componentGraph C).Adj x y → u x = u y := by
      intro x y hxy
      by_contra hne
      exact hnone ⟨x, y, hxy, hne⟩
    have hwalk : ∀ (a b : C), (componentGraph C).Walk a b → u a = u b := by
      intro a b walk
      induction walk with
      | nil => rfl
      | @cons a b c hab walk ih => exact (heq a b hab).trans ih
    have hconstant : u = fun _ => u root := by
      funext x
      obtain ⟨walk⟩ := (uniqueInfiniteComponent_connected (hvalid w.property).1) x root
      exact hwalk x root walk
    have hzero : IsCorrectedPlane C 0 u := by
      rw [hconstant]
      exact isCorrectedPlane_const C _
    obtain ⟨s, _, hs⟩ := ((hvalid w.property).2 (hvalid w.property).1).2 u hu.1.1
    have hbad := (hs (Pi.single 0 1) hu.1).trans (hs 0 hzero).symm
    have hcoord := congrFun hbad 0
    norm_num at hcoord
  obtain ⟨x, y, hxy, hne⟩ := hedge
  refine ⟨p, hpc, hp1, G, hG, hmass, hvalid, g, hmeas, hgradient, hiff,
    w, x, y, hxy, ?_⟩
  have hdrop := hgradient w (Pi.single 0 1) u hu.1 x y hxy
  have hcoeff : g w (x.val, y.val) 0 = u y - u x := by
    simpa only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using hdrop
  intro hz
  apply hne
  exact (sub_eq_zero.mp (hcoeff.symm.trans hz)).symm

end LatticeProb.Percolation
