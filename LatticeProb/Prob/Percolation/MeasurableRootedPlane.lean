import LatticeProb.Prob.Percolation.RootedEncodedPlaneUnique
import LatticeProb.Prob.MeasurableUniqueGraph
import LatticeProb.External.SupercriticalBondCorrectorInput
import LatticeProb.External.SupercriticalBondUniquenessInput

/-!
# A measurable normalized-plane field on a conull valid carrier

The two literal literature inputs give a measurable conull subset of their genuine
common validity event. On its intersection with each root's infinite-component event,
the normalized source plane has a jointly measurable ambient coordinate encoding.
Every value has the complete source characterization on the actual root component.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory LatticeProb.External

variable {d : ℕ}

/-- The genuine event of unique infinitude and both literal corrector clauses. No
measurability assertion for this all-slopes event is part of the definition. -/
def correctorValidEvent (d : ℕ) : Set (Configuration d) :=
  {ω | HasUniqueInfiniteOpenComponent ω ∧
    ∀ h : HasUniqueInfiniteOpenComponent ω,
      (∀ q : Fin d → ℝ, ∀ o : uniqueInfiniteComponent h,
        ∃! u : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0) ∧
      (∀ u : uniqueInfiniteComponent h → ℝ,
        u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
        ∃! q : Fin d → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u)}

/-- The actual probability law admits a measurable conull subset of the genuine
validity event, without assuming measurable projection of the all-slopes clauses. -/
theorem exists_measurable_corrector_valid_set
    (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ G : Set (Configuration d), MeasurableSet G ∧ latticeBondLaw d p G = 1 ∧
      G ⊆ correctorValidEvent d := by
  have hcluster : ∀ᵐ ω ∂latticeBondLaw d p, HasUniqueInfiniteOpenComponent ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent d)).mpr
      (hclassical.2 d hd p hpc hp1)
  have hae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ correctorValidEvent d :=
    hcluster.and (hcorrector d hd p hpc hp1)
  have heq : (Set.univ : Set (Configuration d)) =ᵐ[latticeBondLaw d p]
      correctorValidEvent d := by
    filter_upwards [hae] with ω hω
    exact propext ⟨fun _ => hω, fun _ => Set.mem_univ ω⟩
  have hnull : NullMeasurableSet (correctorValidEvent d) (latticeBondLaw d p) :=
    MeasurableSet.univ.nullMeasurableSet.congr heq
  obtain ⟨G, hsub, hG, heqG⟩ := hnull.exists_measurable_subset_ae_eq
  have hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G := by
    filter_upwards [hae, heqG] with ω hω heqω
    exact heqω.mpr hω
  exact ⟨G, hG, (mem_ae_iff_prob_eq_one hG).mp hGae, hsub⟩

/-- The genuine validity clauses transport to the actual infinite root component.
The normalization point is the given ambient root, viewed in its component. -/
theorem existsUnique_rooted_plane_of_valid
    {ω : Configuration d} (hvalid : ω ∈ correctorValidEvent d)
    (o : Vertex d) (ho : ω ∈ infiniteComponentEvent o) (q : Fin d → ℝ) :
    ∃! u : (openGraph ω).connectedComponentMk o → ℝ,
      IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q u ∧
        u ⟨o, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩ = 0 := by
  have hC := (eq_uniqueInfiniteComponent_iff hvalid.1
    ((openGraph ω).connectedComponentMk o)).mpr ho
  have hplanes := (hvalid.2 hvalid.1).1 q
  rw [← hC] at hplanes
  exact hplanes ⟨o, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

/-- On any measurable subset of the genuine validity event, each root has a jointly
measurable encoded field. Its full graph characterizes every value, including outside-zero. -/
theorem exists_measurable_rooted_plane_on_valid_set
    (G : Set (Configuration d)) (hG : MeasurableSet G)
    (hvalid : G ⊆ correctorValidEvent d) (o : Vertex d) :
    ∃ F : (↥(G ∩ infiniteComponentEvent o) × (Fin d → ℝ)) → (Vertex d → ℝ),
      Measurable F ∧ ∀ z U,
        (U o = 0 ∧
          IsCorrectedPlane ((openGraph z.1.val).connectedComponentMk o) z.2
            (fun x => U x.val) ∧
          ∀ x, ¬ (openGraph z.1.val).Reachable o x → U x = 0) ↔ F z = U := by
  let B := G ∩ infiniteComponentEvent o
  have hB : MeasurableSet B := hG.inter (measurableSet_infiniteComponentEvent o)
  letI : StandardBorelSpace B := hB.standardBorel
  let Γ : Set ((B × (Fin d → ℝ)) × (Vertex d → ℝ)) :=
    {z | z.2 o = 0 ∧
      IsCorrectedPlane ((openGraph z.1.1.val).connectedComponentMk o) z.1.2
        (fun x => z.2 x.val) ∧
      ∀ x, ¬ (openGraph z.1.1.val).Reachable o x → z.2 x = 0}
  have hΓ : MeasurableSet Γ :=
    (measurableSet_rooted_encoded_correctedPlane o).preimage
      (((measurable_subtype_coe.comp measurable_fst).comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  apply LatticeProb.Prob.exists_measurable_of_unique_graph hΓ
  intro z
  exact existsUnique_rooted_encoded_correctedPlane z.1.val o z.2
    (existsUnique_rooted_plane_of_valid (hvalid z.1.property.1) o z.1.property.2 z.2)

/-- The two cited inputs produce a measurable conull good set and, for every actual
root, a measurable plane field with full pointwise source and encoding characterization. -/
theorem exists_measurable_rooted_plane_of_cited_inputs
    (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ G : Set (Configuration d), MeasurableSet G ∧ latticeBondLaw d p G = 1 ∧
      G ⊆ correctorValidEvent d ∧ ∀ o : Vertex d,
        ∃ F : (↥(G ∩ infiniteComponentEvent o) × (Fin d → ℝ)) → (Vertex d → ℝ),
          Measurable F ∧ ∀ z U,
            (U o = 0 ∧
              IsCorrectedPlane ((openGraph z.1.val).connectedComponentMk o) z.2
                (fun x => U x.val) ∧
              ∀ x, ¬ (openGraph z.1.val).Reachable o x → U x = 0) ↔ F z = U := by
  obtain ⟨G, hG, hmass, hvalid⟩ :=
    exists_measurable_corrector_valid_set hclassical hcorrector d hd p hpc hp1
  exact ⟨G, hG, hmass, hvalid, exists_measurable_rooted_plane_on_valid_set G hG hvalid⟩

end LatticeProb.Percolation
