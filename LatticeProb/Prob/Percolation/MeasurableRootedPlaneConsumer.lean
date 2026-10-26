import LatticeProb.Prob.Percolation.MeasurableRootedPlane
import LatticeProb.Prob.Percolation.SupercriticalBondUniquenessConsumer

/-!
# A nonconstant value of the actual measurable plane field

The two cited inputs supply a strictly supercritical two-dimensional parameter and a
configuration in the measurable conull good set. A root of its unique infinite component
makes the field domain inhabited. The coordinate slope gives a genuinely nonconstant
normalized source plane, by the source unique-slope clause and the zero-slope constant theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory LatticeProb.External

/-- A measurable field supplied by the cited inputs has an actual nonconstant coordinate
plane value on an inhabited root carrier. No fixed-root positive-probability premise is used. -/
theorem exists_nonconstant_measurable_rooted_plane_of_cited_inputs
    (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput) :
    ∃ p : unitInterval, criticalProbability 2 < (p : ℝ) ∧ (p : ℝ) < 1 ∧
      ∃ G : Set (Configuration 2), MeasurableSet G ∧ latticeBondLaw 2 p G = 1 ∧
        G ⊆ correctorValidEvent 2 ∧ ∃ o : Vertex 2,
          ∃ F : (↥(G ∩ infiniteComponentEvent o) × (Fin 2 → ℝ)) → (Vertex 2 → ℝ),
            Measurable F ∧
            (∀ z U, (U o = 0 ∧
              IsCorrectedPlane ((openGraph z.1.val).connectedComponentMk o) z.2
                (fun x => U x.val) ∧
              ∀ x, ¬ (openGraph z.1.val).Reachable o x → U x = 0) ↔ F z = U) ∧
            ∃ ω : ↥(G ∩ infiniteComponentEvent o),
              F (ω, Pi.single 0 1) o = 0 ∧
              IsCorrectedPlane ((openGraph ω.val).connectedComponentMk o) (Pi.single 0 1)
                (fun x => F (ω, Pi.single 0 1) x.val) ∧
              ∃ x y : (openGraph ω.val).connectedComponentMk o,
                F (ω, Pi.single 0 1) x.val ≠ F (ω, Pi.single 0 1) y.val := by
  classical
  obtain ⟨p, hpc, hp1⟩ := exists_supercritical_parameter_of_classical_input hclassical 2
    (by decide)
  obtain ⟨G, hG, hmass, hvalid, hfields⟩ :=
    exists_measurable_rooted_plane_of_cited_inputs hclassical hcorrector 2
      (by decide) p hpc hp1
  have hae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G :=
    (mem_ae_iff_prob_eq_one hG).mpr hmass
  obtain ⟨ω, hω⟩ := hae.exists
  have hv := hvalid hω
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent hv.1).nonempty_supp
  have hinf := (mem_uniqueInfiniteComponent_iff hv.1 o).mp ho
  let w : ↥(G ∩ infiniteComponentEvent o) := ⟨ω, hω, hinf⟩
  obtain ⟨F, hF, hgraph⟩ := hfields o
  have hvalue := (hgraph (w, Pi.single 0 1) (F (w, Pi.single 0 1))).mpr rfl
  refine ⟨p, hpc, hp1, G, hG, hmass, hvalid, o, F, hF, hgraph,
    w, hvalue.1, hvalue.2.1, ?_⟩
  let C := (openGraph ω).connectedComponentMk o
  let u : C → ℝ := fun x => F (w, Pi.single 0 1) x.val
  have hu : IsCorrectedPlane C (Pi.single 0 1) u := hvalue.2.1
  have hC := (eq_uniqueInfiniteComponent_iff hv.1 C).mpr hinf
  have hslopes := (hv.2 hv.1).2
  rw [← hC] at hslopes
  by_contra hconstant
  have heq : u = fun _ => u ⟨o, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩ := by
    funext x
    by_contra hx
    exact hconstant ⟨x, ⟨o, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩, hx⟩
  have hzero : IsCorrectedPlane C 0 u := by
    rw [heq]
    exact isCorrectedPlane_const C _
  obtain ⟨q, _, hunique⟩ := hslopes u hu.1
  have hbad := (hunique (Pi.single 0 1) hu).trans (hunique 0 hzero).symm
  have hcoord := congrFun hbad 0
  norm_num at hcoord

end LatticeProb.Percolation
