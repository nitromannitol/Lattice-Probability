import LatticeProb.Prob.AnalyticWitnessTransfer

/-! # Witnesses from a source sample with the same law -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A full event on a Polish Borel source supplies witnesses over any random
variable with the same law, without a measurable choice of witness. -/
theorem ae_exists_source_witness_of_same_law
    {X S Ω : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    [MeasurableSpace Ω] (ν : Measure S) [IsFiniteMeasure ν] (P : Measure Ω)
    (f : S → X) (Z : Ω → X) (hf : Measurable f) (hZ : Measurable Z)
    (hlaw : P.map Z = ν.map f) {Good : S → Prop}
    (hGood : ∀ᵐ s ∂ν, Good s) :
    ∀ᵐ ω ∂P, ∃ s, f s = Z ω ∧ Good s := by
  have hnull : NullMeasurableSet {s | Good s} ν := by
    simpa only [compl_compl] using
      (NullMeasurableSet.of_null (show ν {s | Good s}ᶜ = 0 from ae_iff.1 hGood)).compl
  obtain ⟨B, hBsub, hBm, hBeq⟩ := hnull.exists_measurable_subset_ae_eq
  have hBfull : ∀ᵐ s ∂ν, s ∈ B := by
    filter_upwards [hGood, hBeq] with s hs he
    exact he.mpr hs
  let g : S → X × S := fun s => (f s, s)
  have hg : Measurable g := hf.prodMk measurable_id
  let μ : Measure (X × S) := ν.map g
  have : IsFiniteMeasure μ := Measure.isFiniteMeasure_map ν g
  let A : Set (X × S) := {p | p.1 = f p.2 ∧ p.2 ∈ B}
  have hAm : MeasurableSet A :=
    (measurableSet_eq_fun measurable_fst (hf.comp measurable_snd)).inter
      (hBm.preimage measurable_snd)
  have hAfull : ∀ᵐ p ∂μ, p ∈ A := by
    apply (ae_map_iff hg.aemeasurable hAm).2
    filter_upwards [hBfull] with s hs
    exact ⟨rfl, hs⟩
  have hmarg : μ.map Prod.fst = ν.map f := by
    rw [show μ = ν.map g from rfl, Measure.map_map measurable_fst hg]
    rfl
  have hlaw' : P.map Z = μ.map Prod.fst := hlaw.trans hmarg.symm
  filter_upwards [ae_exists_witness_of_marginal_law μ P Z hZ hlaw' hAm.nullMeasurableSet hAfull]
    with ω hω
  obtain ⟨s, hs⟩ := hω
  exact ⟨s, hs.1.symm, hBsub hs.2⟩

end LatticeProb
