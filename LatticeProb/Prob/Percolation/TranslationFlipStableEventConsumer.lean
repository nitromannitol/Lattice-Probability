import LatticeProb.Prob.Percolation.TranslationFlipStableEvent
import LatticeProb.Prob.Percolation.SupercriticalBondUniquenessConsumer

/-!
# A nonempty patch and nonzero shift on the conull corrector carrier

The two literature inputs supply a two-dimensional supercritical parameter and an
inhabitant of the constructed event. Flipping the horizontal unit bond changes this
configuration. The original, flipped, vertically shifted, and shifted flipped states
all belong to the event and have actual unique infinite open components.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory LatticeProb.External

/-- A singleton flip changes every configuration at the actual horizontal unit bond. -/
theorem horizontal_singleton_flip_ne (ω : Configuration 2) :
    finiteBondFlip {horizontalUnitBond} ω ≠ ω := by
  classical
  intro h
  have he := congrFun h horizontalUnitBond
  simp only [finiteBondFlip, BernoulliFiniteFlip.flip_apply,
    Finset.mem_singleton, ↓reduceIte] at he
  exact (Bool.not_eq_iff.mp he) rfl

/-- An actual event inhabitant remains corrector-valid with a unique infinite component
through a nonempty horizontal singleton flip and a nonzero vertical unit translation. -/
theorem exists_translation_flip_stable_corrector_consumer
    (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput) :
    ∃ p : unitInterval, criticalProbability 2 < (p : ℝ) ∧ (p : ℝ) < 1 ∧
      ∃ E : Set (Configuration 2), MeasurableSet E ∧ latticeBondLaw 2 p E = 1 ∧
        E ⊆ correctorValidEvent 2 ∧
        ({horizontalUnitBond} : Finset (Bond 2)).Nonempty ∧
        (unit (1 : Fin 2) : Vertex 2) ≠ 0 ∧
        ∃ ω ∈ E, finiteBondFlip {horizontalUnitBond} ω ≠ ω ∧
          finiteBondFlip {horizontalUnitBond} ω ∈ E ∧
          configurationTranslation (unit (1 : Fin 2)) ω ∈ E ∧
          configurationTranslation (unit (1 : Fin 2))
            (finiteBondFlip {horizontalUnitBond} ω) ∈ E ∧
          ∀ η : Configuration 2,
            (η = ω ∨ η = finiteBondFlip {horizontalUnitBond} ω ∨
              η = configurationTranslation (unit (1 : Fin 2)) ω ∨
              η = configurationTranslation (unit (1 : Fin 2))
                (finiteBondFlip {horizontalUnitBond} ω)) →
            η ∈ correctorValidEvent 2 ∧ ∃! C : OpenComponent η, C.supp.Infinite := by
  classical
  obtain ⟨p, hpc, hp1⟩ :=
    exists_supercritical_parameter_of_classical_input hclassical 2 (by decide)
  obtain ⟨E, hE, hmass, hvalid, hshift, hflip⟩ :=
    exists_translation_flip_stable_corrector_event hclassical hcorrector 2
      (by decide) p hpc hp1
  have hae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ E :=
    (mem_ae_iff_prob_eq_one hE).mpr hmass
  obtain ⟨ω, hω⟩ := hae.exists
  have hF := hflip ω hω {horizontalUnitBond}
  have hT := (hshift (unit (1 : Fin 2)) ω).mpr hω
  have hTF := (hshift (unit (1 : Fin 2)) (finiteBondFlip {horizontalUnitBond} ω)).mpr hF
  refine ⟨p, hpc, hp1, E, hE, hmass, hvalid, Finset.singleton_nonempty _,
    verticalUnit_ne_zero, ω, hω, horizontal_singleton_flip_ne ω, hF, hT, hTF, ?_⟩
  intro η hη
  have hmem : η ∈ E := by
    rcases hη with rfl | rfl | rfl | rfl
    · exact hω
    · exact hF
    · exact hT
    · exact hTF
  exact ⟨hvalid hmem, (hvalid hmem).1⟩

end LatticeProb.Percolation
