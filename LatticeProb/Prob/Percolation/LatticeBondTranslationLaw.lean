import LatticeProb.Prob.Percolation.LatticeBondTranslation
import LatticeProb.Prob.Percolation.LatticeBondProbability

/-!
# Translation invariance of the canonical Bernoulli bond law

Configuration translation is a measurable equivalence of the full product space.
Its pushforward preserves the actual Bernoulli product law at every unit-interval parameter.
-/

namespace LatticeProb.Percolation

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-- Product reindexing by inverse bond translation is measurable in both directions. -/
def configurationTranslationMeasurableEquiv (z : Vertex d) :
    Configuration d ≃ᵐ Configuration d where
  toEquiv := configurationTranslation z
  measurable_toFun :=
    measurable_pi_lambda _ fun e => measurable_pi_apply (bondTranslation (-z) e)
  measurable_invFun :=
    measurable_pi_lambda _ fun e => measurable_pi_apply (bondTranslation z e)

/-- The measurable equivalence has exactly the literal pullback value at every bond. -/
theorem configurationTranslationMeasurableEquiv_apply (z : Vertex d)
    (ω : Configuration d) (e : Bond d) :
    configurationTranslationMeasurableEquiv z ω e = ω (bondTranslation (-z) e) := rfl

/-- Canonical configuration translation equals Mathlib's product coordinate permutation. -/
theorem configurationTranslation_eq_piCongrLeft (z : Vertex d) :
    configurationTranslationMeasurableEquiv z =
      MeasurableEquiv.piCongrLeft (fun _ : Bond d => Bool) (bondTranslation z) := by
  ext ω e
  obtain ⟨a, rfl⟩ := (bondTranslation z).surjective e
  exact (configurationTranslation_apply_translated z ω a).trans
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Bond d => Bool)
      (bondTranslation z) ω a).symm

/-- Pushing forward the canonical Bernoulli law by translation leaves it unchanged. -/
theorem latticeBondLaw_map_translation (p : unitInterval) (z : Vertex d) :
    (latticeBondLaw d p).map (configurationTranslation z) = latticeBondLaw d p := by
  change (latticeBondLaw d p).map (configurationTranslationMeasurableEquiv z) = _
  rw [configurationTranslation_eq_piCongrLeft]
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Bond d => bernoulliMeasure true false p) (bondTranslation z)

/-- Translation preserves the actual canonical product probability measure. -/
theorem measurePreserving_configurationTranslation (p : unitInterval) (z : Vertex d) :
    MeasurePreserving (configurationTranslation z) (latticeBondLaw d p)
      (latticeBondLaw d p) where
  measurable := (configurationTranslationMeasurableEquiv z).measurable
  map_eq := latticeBondLaw_map_translation p z

/-- The two-dimensional horizontal unit bond, as an actual unordered canonical bond. -/
def horizontalUnitBond : Bond 2 :=
  bondOfAdjacent (show (nearestNeighborGraph 2).Adj 0 (unit (0 : Fin 2)) from
    ⟨0, Or.inl (zero_add _).symm⟩)

/-- Translating the unit bond vertically evaluates both endpoints with the positive sign. -/
theorem horizontalUnitBond_translate_endpoints :
    (bondTranslation (unit (1 : Fin 2)) horizontalUnitBond).val =
      s(unit (1 : Fin 2), unit (0 : Fin 2) + unit (1 : Fin 2)) := by
  simpa only [zero_add] using bondTranslation_endpoints (unit (1 : Fin 2))
    horizontalUnitBond 0 (unit (0 : Fin 2)) rfl

/-- The consumer displacement is nonzero. -/
theorem verticalUnit_ne_zero : (unit (1 : Fin 2) : Vertex 2) ≠ 0 := by
  intro h
  have := congrFun h (1 : Fin 2)
  norm_num [unit] at this

/-- The concrete vertical translation changes the actual unordered unit bond. -/
theorem horizontalUnitBond_translate_ne :
    bondTranslation (unit (1 : Fin 2)) horizontalUnitBond ≠ horizontalUnitBond := by
  intro h
  have he := congrArg Subtype.val h
  rw [horizontalUnitBond_translate_endpoints] at he
  change s(unit (1 : Fin 2), unit (0 : Fin 2) + unit (1 : Fin 2)) =
    s((0 : Vertex 2), unit (0 : Fin 2)) at he
  rcases Sym2.eq_iff.mp he with ⟨hfirst, _⟩ | ⟨hfirst, _⟩
  all_goals
    have hc := congrFun hfirst (1 : Fin 2)
    norm_num [unit, Pi.single_apply] at hc

/-- The inverse sends the translated unit bond back to the original endpoint pair. -/
theorem horizontalUnitBond_translate_inverse :
    ((bondTranslation (unit (1 : Fin 2))).symm
      (bondTranslation (unit (1 : Fin 2)) horizontalUnitBond)).val =
      s((0 : Vertex 2), unit (0 : Fin 2)) := by
  rw [Equiv.symm_apply_apply]
  rfl

/-- A genuine nonconstant Boolean configuration records exactly the horizontal unit bond. -/
noncomputable def horizontalUnitConfiguration : Configuration 2 :=
  fun e => if e = horizontalUnitBond then true else false

/-- The translated singleton-bond configuration is open at the translated unit bond. -/
theorem horizontalUnitConfiguration_translate_open :
    configurationTranslation (unit (1 : Fin 2)) horizontalUnitConfiguration
      (bondTranslation (unit (1 : Fin 2)) horizontalUnitBond) = true := by
  rw [configurationTranslation_apply_translated]
  simp only [horizontalUnitConfiguration, ↓reduceIte]

/-- Before translating, the same Boolean configuration is closed at the moved bond. -/
theorem horizontalUnitConfiguration_closed_at_translated :
    horizontalUnitConfiguration
      (bondTranslation (unit (1 : Fin 2)) horizontalUnitBond) = false := by
  simp only [horizontalUnitConfiguration, horizontalUnitBond_translate_ne, ↓reduceIte]

/-- The same concrete nonzero translation preserves every canonical Bernoulli parameter. -/
theorem horizontalUnitBond_translation_preserves_law (p : unitInterval) :
    MeasurePreserving (configurationTranslation (unit (1 : Fin 2)))
      (latticeBondLaw 2 p) (latticeBondLaw 2 p) :=
  measurePreserving_configurationTranslation p _

end LatticeProb.Percolation
