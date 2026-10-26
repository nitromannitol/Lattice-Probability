import LatticeProb.Prob.Percolation.CorrectedSlopeTranslation
import LatticeProb.Prob.Percolation.IntegerSlopeOpenHit
import LatticeProb.Prob.Percolation.LatticeBondErgodicity
import LatticeProb.Prob.Percolation.LatticeBondFiniteFlip
import LatticeProb.Prob.ErgodicClosedSets
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Deterministic actual integer-gradient slope subgroup

Measurable corrector coefficients on an invariant conull valid set produce one realized
closed subgroup. One measurable conull event classifies all real slopes simultaneously;
its finite-flip stabilization classifies all slopes after every finite bond flip.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Auxiliary closed-set family: the actual subgroup on G and literally empty off G. -/
def guardedIntegerSlopeSet (G : Set (Configuration d))
    (g : G → (Vertex d × Vertex d) → Fin d → ℝ) (ω : Configuration d) :
    Set (Fin d → ℝ) :=
  {q | ∃ h : ω ∈ G, q ∈ LatticeProb.Prob.Percolation.integerSlopeSubgroup (g ⟨ω, h⟩)}

/-- On its actual carrier, the auxiliary family is the whole coefficient subgroup. -/
theorem guardedIntegerSlopeSet_eq (G : Set (Configuration d))
    (g : G → (Vertex d × Vertex d) → Fin d → ℝ) (ω : G) :
    guardedIntegerSlopeSet G g ω.val =
      (LatticeProb.Prob.Percolation.integerSlopeSubgroup (g ω) : Set (Fin d → ℝ)) := by
  ext q
  exact ⟨fun ⟨_, hq⟩ => hq, fun hq => ⟨ω.property, hq⟩⟩

/-- Off the valid carrier the auxiliary family has no members. -/
theorem guardedIntegerSlopeSet_eq_empty (G : Set (Configuration d))
    (g : G → (Vertex d × Vertex d) → Fin d → ℝ) {ω : Configuration d}
    (hω : ω ∉ G) : guardedIntegerSlopeSet G g ω = ∅ := by
  ext q
  exact ⟨fun ⟨h, _⟩ => (hω h).elim, fun h => h.elim⟩

/-- The literal auxiliary family is closed everywhere, including outside G. -/
theorem isClosed_guardedIntegerSlopeSet (G : Set (Configuration d))
    (g : G → (Vertex d × Vertex d) → Fin d → ℝ) (ω : Configuration d) :
    IsClosed (guardedIntegerSlopeSet G g ω) := by
  by_cases hω : ω ∈ G
  · rw [guardedIntegerSlopeSet_eq G g ⟨ω, hω⟩]
    exact LatticeProb.Prob.Percolation.isClosed_integerSlopeSubgroup _
  · rw [guardedIntegerSlopeSet_eq_empty G g hω]
    exact isClosed_empty

/-- Relative open hits push forward through the measurable subtype embedding of G. -/
theorem measurableSet_guardedIntegerSlopeSet_hit (G : Set (Configuration d))
    (hG : MeasurableSet G) (g : G → (Vertex d × Vertex d) → Fin d → ℝ)
    (hg : ∀ e j, Measurable (fun ω => g ω e j))
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    MeasurableSet {ω | (guardedIntegerSlopeSet G g ω ∩ U).Nonempty} := by
  have hrel := LatticeProb.Prob.Percolation.measurableSet_integerSlopeOpenHit g hg U hU
  have heq : {ω | (guardedIntegerSlopeSet G g ω ∩ U).Nonempty} =
      Subtype.val '' {ω : G | ∃ q ∈ U,
        q ∈ LatticeProb.Prob.Percolation.integerSlopeSubgroup (g ω)} := by
    ext ω
    constructor
    · rintro ⟨q, ⟨hω, hq⟩, hUq⟩
      exact ⟨⟨ω, hω⟩, ⟨q, hUq, hq⟩, rfl⟩
    · rintro ⟨⟨ω, hω⟩, ⟨q, hUq, hq⟩, rfl⟩
      exact ⟨q, ⟨hω, hq⟩, hUq⟩
  rw [heq]
  exact (MeasurableEmbedding.subtype_coe hG).measurableSet_image.mpr hrel

/-- Subgroup covariance and exact invariance of G imply covariance of the empty extension. -/
theorem guardedIntegerSlopeSet_translation (G : Set (Configuration d))
    (hinv : ∀ z ω, configurationTranslation z ω ∈ G ↔ ω ∈ G)
    (g : G → (Vertex d × Vertex d) → Fin d → ℝ)
    (hcov : ∀ (ω : G) z,
      LatticeProb.Prob.Percolation.integerSlopeSubgroup
          (g ⟨configurationTranslation z ω.val, (hinv z ω.val).mpr ω.property⟩) =
        LatticeProb.Prob.Percolation.integerSlopeSubgroup (g ω))
    (ω : Configuration d) (z : Vertex d) :
    guardedIntegerSlopeSet G g (configurationTranslation z ω) =
      guardedIntegerSlopeSet G g ω := by
  by_cases hω : ω ∈ G
  · rw [guardedIntegerSlopeSet_eq G g
      ⟨configurationTranslation z ω, (hinv z ω).mpr hω⟩,
      guardedIntegerSlopeSet_eq G g ⟨ω, hω⟩, hcov ⟨ω, hω⟩ z]
  · rw [guardedIntegerSlopeSet_eq_empty G g (fun h => hω ((hinv z ω).mp h)),
      guardedIntegerSlopeSet_eq_empty G g hω]

/-- A realized closed subgroup and two measurable conull events with literal all-slope
classification on the actual unique component, before and after all finite bond flips. -/
structure DeterministicIntegerSlopeData (G : Set (Configuration d))
    (hvalid : G ⊆ correctorValidEvent d) (p : unitInterval) where
  /-- The fixed subgroup is realized by actual coefficients in the construction below. -/
  subgroup : AddSubgroup (Fin d → ℝ)
  /-- The fixed subgroup is closed in real slope space. -/
  closed : IsClosed (subgroup : Set (Fin d → ℝ))
  /-- A common classification event for every real slope. -/
  event : Set (Configuration d)
  /-- The common event is measurable. -/
  measurable_event : MeasurableSet event
  /-- The common event has probability one under the actual bond law. -/
  mass_event : latticeBondLaw d p event = 1
  /-- Every configuration in the common event is source-valid. -/
  event_subset : event ⊆ G
  /-- All slopes are classified pointwise on the common event. -/
  source_iff : ∀ ω (hω : ω ∈ event) q,
    q ∈ subgroup ↔ HasIntegerGradientCorrectedPlane (hvalid (event_subset hω)).1 q
  /-- The literal event of membership after every finite flip. -/
  flipEvent : Set (Configuration d)
  /-- No slope-dependent event is used in finite-flip stabilization. -/
  flipEvent_eq : flipEvent = allFiniteBondFlipsEvent event
  /-- The simultaneous finite-flip event is measurable. -/
  measurable_flipEvent : MeasurableSet flipEvent
  /-- The simultaneous finite-flip event has probability one. -/
  mass_flipEvent : latticeBondLaw d p flipEvent = 1
  /-- The finite-flip event is contained in the classification event. -/
  flipEvent_subset : flipEvent ⊆ event
  /-- Actual validity holds after each finite flip on the common event. -/
  flip_mem : ∀ ω ∈ flipEvent, ∀ F : Finset (Bond d), finiteBondFlip F ω ∈ G
  /-- One common event classifies every real slope after every finite bond flip. -/
  flip_source_iff : ∀ ω (hω : ω ∈ flipEvent) (F : Finset (Bond d)) q,
    q ∈ subgroup ↔ HasIntegerGradientCorrectedPlane (hvalid (flip_mem ω hω F)).1 q

/-- An invariant measurable conull valid set produces deterministic actual slopes on one
common measurable event and on its simultaneous finite-flip stabilization. -/
theorem exists_deterministicIntegerSlopeData [NeZero d]
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (G : Set (Configuration d)) (hG : MeasurableSet G)
    (hmass : latticeBondLaw d p G = 1) (hvalid : G ⊆ correctorValidEvent d)
    (hinv : ∀ z ω, configurationTranslation z ω ∈ G ↔ ω ∈ G) :
    Nonempty (DeterministicIntegerSlopeData G hvalid p) := by
  obtain ⟨g, hg, _, _, hsource⟩ :=
    exists_measurable_corrector_gradients_on_valid_set G hG hvalid
  have hcov := integerSlopeSubgroup_translation_on_valid_set G hvalid hinv g hsource
  let z : Vertex d := Pi.single (0 : Fin d) 1
  have hz : z ≠ 0 := by
    intro h
    have hi := congrFun h 0
    norm_num [z] at hi
  obtain ⟨K, _, hK⟩ := LatticeProb.Prob.exists_isClosed_ae_eq_of_ergodic
    (ergodic_configurationTranslation p hz) (guardedIntegerSlopeSet G g)
    (isClosed_guardedIntegerSlopeSet G g)
    (measurableSet_guardedIntegerSlopeSet_hit G hG g hg)
    (fun ω => guardedIntegerSlopeSet_translation G hinv g hcov ω z)
  have hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G :=
    (mem_ae_iff_prob_eq_one hG).mpr hmass
  obtain ⟨ω₀, hω₀, hK₀⟩ := (hGae.and hK).exists
  let S := LatticeProb.Prob.Percolation.integerSlopeSubgroup (g ⟨ω₀, hω₀⟩)
  have hS : (S : Set (Fin d → ℝ)) = K :=
    (guardedIntegerSlopeSet_eq G g ⟨ω₀, hω₀⟩).symm.trans hK₀
  have hcommon : ∀ᵐ ω ∂latticeBondLaw d p,
      ω ∈ G ∧ guardedIntegerSlopeSet G g ω = (S : Set (Fin d → ℝ)) := by
    filter_upwards [hGae, hK] with ω hω hk
    exact ⟨hω, hk.trans hS.symm⟩
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hcommon)
  let D := Nᶜ
  have hD : MeasurableSet D := hNmeas.compl
  have hDgood : ∀ ω ∈ D,
      ω ∈ G ∧ guardedIntegerSlopeSet G g ω = (S : Set (Fin d → ℝ)) := by
    intro ω hω
    by_contra hbad
    exact hω (hNsub hbad)
  have hDmass : latticeBondLaw d p D = 1 := by
    apply (mem_ae_iff_prob_eq_one hD).mp
    exact compl_mem_ae_iff.mpr hNzero
  have hDG : D ⊆ G := fun ω hω => (hDgood ω hω).1
  have hclass : ∀ ω (hω : ω ∈ D) q,
      q ∈ S ↔ HasIntegerGradientCorrectedPlane (hvalid (hDG hω)).1 q := by
    intro ω hω q
    have heq := (guardedIntegerSlopeSet_eq G g ⟨ω, hDG hω⟩).symm.trans
      (hDgood ω hω).2
    exact (Set.ext_iff.mp heq q).symm.trans (hsource ⟨ω, hDG hω⟩ q)
  refine ⟨{
    subgroup := S
    closed := LatticeProb.Prob.Percolation.isClosed_integerSlopeSubgroup _
    event := D
    measurable_event := hD
    mass_event := hDmass
    event_subset := hDG
    source_iff := hclass
    flipEvent := allFiniteBondFlipsEvent D
    flipEvent_eq := rfl
    measurable_flipEvent := measurableSet_allFiniteBondFlipsEvent hD
    mass_flipEvent := latticeBondLaw_allFiniteBondFlipsEvent p hp0 hp1 hD hDmass
    flipEvent_subset := allFiniteBondFlipsEvent_subset D
    flip_mem := fun ω hω F => hDG (hω F)
    flip_source_iff := fun ω hω F q => hclass (finiteBondFlip F ω) (hω F) q }⟩

end

end LatticeProb.Percolation
