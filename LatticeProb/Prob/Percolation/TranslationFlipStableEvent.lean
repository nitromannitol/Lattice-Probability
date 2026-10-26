import LatticeProb.Prob.Percolation.BondFlipTranslation
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw
import LatticeProb.Prob.Percolation.MeasurableRootedPlane

/-!
# A conull corrector event stable under translations and finite flips

First intersect all lattice translates of a measurable conull event. Then intersect
all finite bond flips. Conjugation of actual unordered bond patches gives pointwise
translation invariance of the resulting event, without invariance of the initial event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory LatticeProb.External

variable {d : ℕ}

/-- The literal countable intersection of all translates of an event. -/
def allLatticeTranslationsEvent (G : Set (Configuration d)) : Set (Configuration d) :=
  {ω | ∀ z : Vertex d, configurationTranslation z ω ∈ G}

/-- Countably many measurable translation preimages form a measurable event. -/
theorem measurableSet_allLatticeTranslationsEvent {G : Set (Configuration d)}
    (hG : MeasurableSet G) : MeasurableSet (allLatticeTranslationsEvent G) := by
  have heq : allLatticeTranslationsEvent G =
      ⋂ z : Vertex d, configurationTranslation z ⁻¹' G := by
    ext ω
    simp only [allLatticeTranslationsEvent, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_preimage]
  rw [heq]
  exact MeasurableSet.iInter fun z =>
    hG.preimage (configurationTranslationMeasurableEquiv z).measurable

/-- All translated memberships hold simultaneously with probability one. -/
theorem latticeBondLaw_allLatticeTranslationsEvent (p : unitInterval)
    {G : Set (Configuration d)} (hG : MeasurableSet G) (hmass : latticeBondLaw d p G = 1) :
    latticeBondLaw d p (allLatticeTranslationsEvent G) = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_allLatticeTranslationsEvent hG)).mp
  apply ae_all_iff.mpr
  intro z
  apply ae_of_ae_map (configurationTranslationMeasurableEquiv z).measurable.aemeasurable
  change ∀ᵐ y ∂(latticeBondLaw d p).map (configurationTranslation z), y ∈ G
  rw [latticeBondLaw_map_translation]
  exact (mem_ae_iff_prob_eq_one hG).mpr hmass

/-- The zero translate shows containment in the initial event. -/
theorem allLatticeTranslationsEvent_subset (G : Set (Configuration d)) :
    allLatticeTranslationsEvent G ⊆ G := by
  intro ω hω
  simpa only [configurationTranslation_zero] using hω 0

/-- The literal intersection is invariant under every translation at every point. -/
theorem configurationTranslation_mem_allLatticeTranslationsEvent_iff
    (G : Set (Configuration d)) (z : Vertex d) (ω : Configuration d) :
    configurationTranslation z ω ∈ allLatticeTranslationsEvent G ↔
      ω ∈ allLatticeTranslationsEvent G := by
  constructor
  · intro h w
    have hw := h (w - z)
    simpa only [configurationTranslation_add, sub_add_cancel] using hw
  · intro h w
    rw [configurationTranslation_add]
    exact h (w + z)

/-- Finite-flip completion of the translate intersection is also translation invariant. -/
theorem configurationTranslation_mem_allFiniteBondFlipsEvent_translations_iff
    (G : Set (Configuration d)) (z : Vertex d) (ω : Configuration d) :
    configurationTranslation z ω ∈ allFiniteBondFlipsEvent (allLatticeTranslationsEvent G) ↔
      ω ∈ allFiniteBondFlipsEvent (allLatticeTranslationsEvent G) := by
  classical
  have hforward (w : Vertex d) (η : Configuration d)
      (hη : η ∈ allFiniteBondFlipsEvent (allLatticeTranslationsEvent G)) :
      configurationTranslation w η ∈
        allFiniteBondFlipsEvent (allLatticeTranslationsEvent G) := by
    intro F
    have h := (configurationTranslation_mem_allLatticeTranslationsEvent_iff G w
      (finiteBondFlip (F.image (bondTranslation (-w))) η)).mpr
        (hη (F.image (bondTranslation (-w))))
    rw [configurationTranslation_finiteBondFlip] at h
    simpa only [Finset.image_image, Function.comp_def, bondTranslation_add, add_neg_cancel,
      bondTranslation_zero, Finset.image_id'] using h
  constructor
  · intro h
    have hinv := hforward (-z) (configurationTranslation z ω) h
    simpa only [configurationTranslation_add, neg_add_cancel,
      configurationTranslation_zero] using hinv
  · exact hforward z ω

/-- The two literature hypotheses produce an actual measurable conull corrector-valid
set stable pointwise under every lattice translation and every finite bond flip. -/
theorem exists_translation_flip_stable_corrector_event
    (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ E : Set (Configuration d), MeasurableSet E ∧ latticeBondLaw d p E = 1 ∧
      E ⊆ correctorValidEvent d ∧
      (∀ z ω, configurationTranslation z ω ∈ E ↔ ω ∈ E) ∧
      ∀ ω ∈ E, ∀ F : Finset (Bond d), finiteBondFlip F ω ∈ E := by
  obtain ⟨G, hG, hmass, hvalid⟩ :=
    exists_measurable_corrector_valid_set hclassical hcorrector d hd p hpc hp1
  let Gtr := allLatticeTranslationsEvent G
  have hGtr : MeasurableSet Gtr := measurableSet_allLatticeTranslationsEvent hG
  have hmassTr : latticeBondLaw d p Gtr = 1 :=
    latticeBondLaw_allLatticeTranslationsEvent p hG hmass
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  refine ⟨allFiniteBondFlipsEvent Gtr, measurableSet_allFiniteBondFlipsEvent hGtr,
    latticeBondLaw_allFiniteBondFlipsEvent p hp0 hp1 hGtr hmassTr, ?_, ?_, ?_⟩
  · exact (allFiniteBondFlipsEvent_subset Gtr).trans
      ((allLatticeTranslationsEvent_subset G).trans hvalid)
  · exact configurationTranslation_mem_allFiniteBondFlipsEvent_translations_iff G
  · intro ω hω F
    exact finiteBondFlip_mem_allFiniteBondFlipsEvent hω F

end LatticeProb.Percolation
