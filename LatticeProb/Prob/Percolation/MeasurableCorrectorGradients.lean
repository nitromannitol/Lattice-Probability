import LatticeProb.Prob.Percolation.RootedPlaneFieldAlgebra
import LatticeProb.Prob.Percolation.IntegerSlopeSubgroup

/-!
# Measurable coefficients of actual source-plane gradients

Ordered vertex pairs carry coefficients of the normalized coordinate planes when the
first vertex has infinite component and the pair is an actual open edge. All other
constraints have coefficient zero. The resulting subgroup is characterized by literal
existence of a source plane with integer differences on its actual component edges.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory LatticeProb.External
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Auxiliary edge coefficients from rooted encodings. The guard gives zero constraints
on inactive ordered pairs; the source planes themselves retain their restricted domains. -/
def rootedPlaneEdgeCoefficients (G : Set (Configuration d))
    (F : ∀ o : Vertex d,
      (↥(G ∩ infiniteComponentEvent o) × (Fin d → ℝ)) → Vertex d → ℝ)
    (ω : G) (e : Vertex d × Vertex d) (j : Fin d) : ℝ := by
  classical
  exact if h : ω.val ∈ infiniteComponentEvent e.1 ∧ (openGraph ω.val).Adj e.1 e.2 then
    F e.1 (⟨ω.val, ω.property, h.1⟩, Pi.single j 1) e.2
  else 0

/-- Jointly measurable rooted encodings give measurable coordinates of the guarded
ordered-pair coefficient field, using the actual measurable adjacency and root events. -/
theorem measurable_rootedPlaneEdgeCoefficients
    (G : Set (Configuration d))
    (F : ∀ o : Vertex d,
      (↥(G ∩ infiniteComponentEvent o) × (Fin d → ℝ)) → Vertex d → ℝ)
    (hF : ∀ o, Measurable (F o)) (e : Vertex d × Vertex d) (j : Fin d) :
    Measurable (fun ω : G => rootedPlaneEdgeCoefficients G F ω e j) := by
  classical
  let S : Set G := {ω | ω.val ∈ infiniteComponentEvent e.1 ∧
    (openGraph ω.val).Adj e.1 e.2}
  have hS : MeasurableSet S :=
    ((measurableSet_infiniteComponentEvent e.1).preimage measurable_subtype_coe).inter
      ((measurableSet_openGraph_adj e.1 e.2).preimage measurable_subtype_coe)
  have hm : Measurable (fun ω : S =>
      (⟨ω.val.val, ω.val.property, ω.property.1⟩ : ↥(G ∩ infiniteComponentEvent e.1))) :=
    (measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk
  have hval : Measurable (fun ω : S =>
      F e.1 (⟨ω.val.val, ω.val.property, ω.property.1⟩, Pi.single j 1) e.2) :=
    (measurable_pi_apply e.2).comp ((hF e.1).comp (hm.prodMk measurable_const))
  exact hval.dite (g := fun _ => (0 : ℝ)) measurable_const hS

/-- On any measurable valid set there is a measurable coefficient field with its full
source gradient characterization and exact literal source-existential subgroup iff. -/
theorem exists_measurable_corrector_gradients_on_valid_set
    (G : Set (Configuration d)) (hG : MeasurableSet G)
    (hvalid : G ⊆ correctorValidEvent d) :
    ∃ g : G → (Vertex d × Vertex d) → Fin d → ℝ,
      (∀ e j, Measurable (fun ω => g ω e j)) ∧
      (∀ (ω : G) e, ¬ (ω.val ∈ infiniteComponentEvent e.1 ∧
        (openGraph ω.val).Adj e.1 e.2) → ∀ j, g ω e j = 0) ∧
      (∀ (ω : G) (q : Fin d → ℝ)
        (u : uniqueInfiniteComponent (hvalid ω.property).1 → ℝ),
        IsCorrectedPlane (uniqueInfiniteComponent (hvalid ω.property).1) q u →
        ∀ x y : uniqueInfiniteComponent (hvalid ω.property).1,
          (openGraph ω.val).Adj x.val y.val →
          ∑ j, q j * g ω (x.val, y.val) j = u y - u x) ∧
      (∀ (ω : G) (q : Fin d → ℝ),
        q ∈ LatticeProb.Prob.Percolation.integerSlopeSubgroup (g ω) ↔
          ∃ u : uniqueInfiniteComponent (hvalid ω.property).1 → ℝ,
            IsCorrectedPlane (uniqueInfiniteComponent (hvalid ω.property).1) q u ∧
            ∀ x y : uniqueInfiniteComponent (hvalid ω.property).1,
              (openGraph ω.val).Adj x.val y.val → ∃ z : ℤ, u y - u x = (z : ℝ)) := by
  classical
  choose F hF hgraph using exists_measurable_rooted_plane_on_valid_set G hG hvalid
  let g := rootedPlaneEdgeCoefficients G F
  have hzero : ∀ (ω : G) e, ¬ (ω.val ∈ infiniteComponentEvent e.1 ∧
      (openGraph ω.val).Adj e.1 e.2) → ∀ j, g ω e j = 0 := by
    intro ω e he j
    exact dif_neg he
  have hgradient : ∀ (ω : G) (q : Fin d → ℝ)
      (u : uniqueInfiniteComponent (hvalid ω.property).1 → ℝ),
      IsCorrectedPlane (uniqueInfiniteComponent (hvalid ω.property).1) q u →
      ∀ x y : uniqueInfiniteComponent (hvalid ω.property).1,
        (openGraph ω.val).Adj x.val y.val →
        ∑ j, q j * g ω (x.val, y.val) j = u y - u x := by
    intro ω q u hu x y hxy
    have hx := (mem_uniqueInfiniteComponent_iff (hvalid ω.property).1 x.val).mp x.property
    let w : ↥(G ∩ infiniteComponentEvent x.val) := ⟨ω.val, ω.property, hx⟩
    have hvalue := fun q => (hgraph x.val (w, q) (F x.val (w, q))).mpr rfl
    calc
      ∑ j, q j * g ω (x.val, y.val) j =
          ∑ j, q j * F x.val (w, Pi.single j 1) y.val := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show g ω (x.val, y.val) j = F x.val (w, Pi.single j 1) y.val from
          dif_pos ⟨hx, hxy⟩]
      _ = F x.val (w, q) y.val :=
        (rooted_encoded_plane_basis_expansion (hvalid ω.property) x.val hx
          (fun q => F x.val (w, q)) hvalue q y.val).symm
      _ = u y - u x := rooted_encoded_plane_uniqueComponent_eq_sub
        (hvalid ω.property) x y q _ ⟨(hvalue q).1, (hvalue q).2.1⟩ u hu
  refine ⟨g, measurable_rootedPlaneEdgeCoefficients G F hF, hzero, hgradient, ?_⟩
  intro ω q
  constructor
  · intro hq
    obtain ⟨o, ho⟩ := (uniqueInfiniteComponent (hvalid ω.property).1).nonempty_supp
    obtain ⟨u, hu, _⟩ := ((hvalid ω.property).2 (hvalid ω.property).1).1 q ⟨o, ho⟩
    refine ⟨u, hu.1, ?_⟩
    intro x y hxy
    obtain ⟨z, hz⟩ := hq (x.val, y.val)
    exact ⟨z, (hgradient ω q u hu.1 x y hxy).symm.trans hz⟩
  · rintro ⟨u, hu, hint⟩ e
    by_cases he : ω.val ∈ infiniteComponentEvent e.1 ∧ (openGraph ω.val).Adj e.1 e.2
    · have hx := (mem_uniqueInfiniteComponent_iff (hvalid ω.property).1 e.1).mpr he.1
      have hy := (uniqueInfiniteComponent (hvalid ω.property).1).mem_supp_of_adj_mem_supp
        hx he.2
      let x : uniqueInfiniteComponent (hvalid ω.property).1 := ⟨e.1, hx⟩
      let y : uniqueInfiniteComponent (hvalid ω.property).1 := ⟨e.2, hy⟩
      obtain ⟨z, hz⟩ := hint x y he.2
      exact ⟨z, (hgradient ω q u hu x y he.2).trans hz⟩
    · refine ⟨0, ?_⟩
      simp only [hzero ω e he, mul_zero, Finset.sum_const_zero, Int.cast_zero]

/-- The same two cited inputs give actual measurable gradient coefficients on a conull
valid set, with the literal integer-gradient source-plane existential characterization. -/
theorem exists_measurable_corrector_gradients_of_cited_inputs
    (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ G : Set (Configuration d), MeasurableSet G ∧ latticeBondLaw d p G = 1 ∧
      ∃ hvalid : G ⊆ correctorValidEvent d,
        ∃ g : G → (Vertex d × Vertex d) → Fin d → ℝ,
          (∀ e j, Measurable (fun ω => g ω e j)) ∧
          (∀ (ω : G) e, ¬ (ω.val ∈ infiniteComponentEvent e.1 ∧
            (openGraph ω.val).Adj e.1 e.2) → ∀ j, g ω e j = 0) ∧
          (∀ (ω : G) (q : Fin d → ℝ)
            (u : uniqueInfiniteComponent (hvalid ω.property).1 → ℝ),
            IsCorrectedPlane (uniqueInfiniteComponent (hvalid ω.property).1) q u →
            ∀ x y : uniqueInfiniteComponent (hvalid ω.property).1,
              (openGraph ω.val).Adj x.val y.val →
              ∑ j, q j * g ω (x.val, y.val) j = u y - u x) ∧
          (∀ (ω : G) (q : Fin d → ℝ),
            q ∈ LatticeProb.Prob.Percolation.integerSlopeSubgroup (g ω) ↔
              ∃ u : uniqueInfiniteComponent (hvalid ω.property).1 → ℝ,
                IsCorrectedPlane (uniqueInfiniteComponent (hvalid ω.property).1) q u ∧
                ∀ x y : uniqueInfiniteComponent (hvalid ω.property).1,
                  (openGraph ω.val).Adj x.val y.val →
                    ∃ z : ℤ, u y - u x = (z : ℝ)) := by
  obtain ⟨G, hG, hmass, hvalid⟩ :=
    exists_measurable_corrector_valid_set hclassical hcorrector d hd p hpc hp1
  exact ⟨G, hG, hmass, hvalid,
    exists_measurable_corrector_gradients_on_valid_set G hG hvalid⟩

end

end LatticeProb.Percolation
