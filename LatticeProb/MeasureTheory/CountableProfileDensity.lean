import LatticeProb.MeasureTheory.CountableSimpleProfiles
import LatticeProb.MeasureTheory.ProfileSimpleApproximation
import LatticeProb.MeasureTheory.DenseLabelledSimpleProfile

/-! # Countable dense families of measurable profiles -/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace LatticeProb.MeasurableProfile

/-- The profiles induced by simple functions with labels in a countable dense set and
fibres in a countable measure-dense algebra form a countable dense family. -/
theorem countable_dense_simple_profiles {α E : Type*} [MeasurableSpace α]
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] (μ : Measure α) [IsFiniteMeasure μ]
    {D : Set E} (hDc : D.Countable) (hD : Dense D)
    {𝒜 : Set (Set α)} (hAc : 𝒜.Countable) (h𝒜 : IsSetAlgebra 𝒜)
    (hA : μ.MeasureDense 𝒜) :
    let family : Set (SimpleFunc α E) := {f | Set.range f ⊆ D ∧
      ∀ y ∈ Set.range f, f ⁻¹' {y} ∈ 𝒜}
    let profiles := (fun f : SimpleFunc α E =>
      (⟨f, f.measurable.aemeasurable⟩ : MeasurableProfile (E := E) μ)) '' family
    profiles.Countable ∧ @Dense _ (instPseudoMetricSpace μ).toUniformSpace.toTopologicalSpace profiles := by
  classical
  let : PseudoMetricSpace (MeasurableProfile (E := E) μ) := instPseudoMetricSpace μ
  dsimp only
  constructor
  · exact (countable_simpleFunc_of_range_fibres hDc hAc).image _
  · apply Metric.dense_iff.mpr
    intro f ε hε
    by_cases hE : Nonempty E
    · let : Nonempty E := hE
      obtain ⟨s, hs⟩ := exists_simple_tendsto μ f
      let p : ℕ → MeasurableProfile (E := E) μ := fun n =>
        ⟨s n, (s n).measurable.aemeasurable⟩
      have hs' : ∀ᶠ n in atTop, dist (p n) f < ε / 2 :=
        ((Metric.tendsto_nhds (u := p) (a := f)).mp hs) (ε / 2) (by positivity)
      obtain ⟨n, hn⟩ := Filter.Eventually.exists hs'
      obtain ⟨g, hgD, hgA, hg⟩ :=
        exists_simpleFunc_dense_labels_measureDense_fibres μ h𝒜 hA hD (s n)
          (by positivity : 0 < ε / 2)
      let gp : MeasurableProfile (E := E) μ := ⟨g, g.measurable.aemeasurable⟩
      let sp : MeasurableProfile (E := E) μ := ⟨s n, (s n).measurable.aemeasurable⟩
      have hdist : dist sp gp < ε / 2 := by
        change (integralDist μ sp gp).toReal < ε / 2
        apply (ENNReal.toReal_lt_toReal (integralDist_ne_top μ sp gp)
          ENNReal.ofReal_ne_top).2 at hg
        simpa only [ENNReal.toReal_ofReal (le_of_lt (by positivity : 0 < ε / 2))] using hg
      refine ⟨gp, ?_, ⟨g, ⟨hgD, hgA⟩, rfl⟩⟩
      change dist gp f < ε
      rw [dist_comm gp f]
      have := dist_triangle f sp gp
      rw [dist_comm f sp] at this
      linarith
    · let : IsEmpty E := not_nonempty_iff.mp hE
      let : IsEmpty α := ⟨fun x => isEmptyElim (f.1 x)⟩
      let g : SimpleFunc α E := SimpleFunc.ofIsEmpty
      let gp : MeasurableProfile (E := E) μ := ⟨g, g.measurable.aemeasurable⟩
      have hfg : f = gp := by
        apply Subtype.ext
        funext x
        exact isEmptyElim x
      refine ⟨gp, ?_, ⟨g, ⟨?_, ?_⟩, rfl⟩⟩
      · simp [← hfg, hε]
      · rintro y ⟨x, rfl⟩
        exact isEmptyElim x
      · rintro y ⟨x, _⟩
        exact isEmptyElim x

end LatticeProb.MeasurableProfile
