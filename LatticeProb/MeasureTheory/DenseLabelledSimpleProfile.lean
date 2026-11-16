import LatticeProb.MeasureTheory.MeasureDenseLabelledProfile

/-! # Approximation of simple profiles by dense labels -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- A simple profile on a finite measure space can be approximated in integrated
truncated edistance by a simple profile with values in a dense set and fibres
in a measure-dense algebra. -/
theorem exists_simpleFunc_dense_labels_measureDense_fibres {α E : Type*}
    [MeasurableSpace α] [PseudoEMetricSpace E] (μ : Measure α) [IsFiniteMeasure μ]
    {𝒜 : Set (Set α)} (h𝒜 : IsSetAlgebra 𝒜) (hA : μ.MeasureDense 𝒜)
    {D : Set E} (hD : Dense D) (f : SimpleFunc α E) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SimpleFunc α E, Set.range g ⊆ D ∧
      (∀ y ∈ Set.range g, g ⁻¹' {y} ∈ 𝒜) ∧
      (∫⁻ x, min 1 (edist (f x) (g x)) ∂μ) < ENNReal.ofReal ε := by
  classical
  by_cases hα : Nonempty α
  · let : Nonempty α := hα
    have hε2 : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨δ, hδ, hδμ⟩ := ENNReal.exists_pos_mul_lt (measure_ne_top μ univ) hε2.ne'
    let : Fintype (Set.range f) := f.finite_range.fintype
    let e := (Fintype.equivFin (Set.range f)).symm
    let s : Fin (Fintype.card (Set.range f)) → Set α := fun i => f ⁻¹' {(e i).1}
    have hs : Pairwise (Function.onFun Disjoint s) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      have he : e i = e j := Subtype.ext (by simpa [s] using hxi.symm.trans hxj)
      exact hij (e.injective he)
    have hsm : ∀ i, MeasurableSet (s i) := fun i => f.measurableSet_fiber _
    have hsfinite : ∀ i, μ (s i) ≠ ∞ := fun i => measure_ne_top μ _
    have hcover : ∀ x, ∃ i, x ∈ s i := by
      intro x
      refine ⟨e.symm ⟨f x, ⟨x, rfl⟩⟩, ?_⟩
      simp [s]
    have hlabels : ∀ i, ∃ y ∈ D, edist ((e i).1) y < δ := by
      intro i
      exact (EMetric.mem_closure_iff.mp (hD ((e i).1))) δ hδ
    choose v hv hvclose using hlabels
    obtain ⟨v₀, hv₀, _⟩ := (EMetric.mem_closure_iff.mp (hD (f (Classical.choice hα)))) δ hδ
    obtain ⟨g, hgD, hgA, hg⟩ :=
      exists_simpleFunc_measureDense_partition_bound μ h𝒜 hA s hs hsm hsfinite hcover
        v v₀ hv hv₀ f δ (by
          intro i x hx
          have hx' : f x = (e i).1 := by simpa [s] using hx
          rw [hx']
          exact le_of_lt (hvclose i)) (by positivity : 0 < ε / 2)
    refine ⟨g, hgD, hgA, hg.trans_lt ?_⟩
    calc
      δ * μ univ + ENNReal.ofReal (ε / 2) <
          ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add_right (ENNReal.ofReal_ne_top) hδμ
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 2)]; congr 1; ring; positivity
  · let : IsEmpty α := not_nonempty_iff.mp hα
    refine ⟨f, ?_, ?_, ?_⟩
    · rintro y ⟨x, rfl⟩
      exact isEmptyElim x
    · intro y hy
      obtain ⟨x, _⟩ := hy
      exact isEmptyElim x
    · simpa using ENNReal.ofReal_pos.mpr hε

end LatticeProb
