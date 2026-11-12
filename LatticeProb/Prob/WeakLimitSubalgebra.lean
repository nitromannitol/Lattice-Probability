/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Topology.PolishContinuousMap

/-!
# Weak limits of tight families determined by a separating subalgebra

Let `E` be a Polish space with its Borel sigma-algebra and `μ i`, `i ∈ s`, probability measures on
`E` indexed along a filter `l`.  If the family is tight and, for every element `g` of a subalgebra `A`
of `E →ᵇ ℝ` separating points, the integrals `∫ g d(μ i)` converge along `l`, then the family
converges weakly along `l` to a probability measure.

The proof combines Prokhorov's theorem (the closure of a tight set of probability measures is
compact) with the fact that a subalgebra separating points separates finite measures: every cluster
point has the same integrals against `A`, hence there is only one cluster point.

* `LatticeProb.exists_tendsto_of_isTightMeasureSet_subalgebra`: the general limit theorem.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace LatticeProb

section WeakLimit

variable {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [Nonempty E]

/-- **Weak limit of a tight family.**  Let `μ i`, `i ∈ s ∈ l`, be probability measures on a Polish
space `E` forming a tight set, and `A` a subalgebra of bounded continuous functions that separates
points, such that `∫ g d(μ i)` converges along `l` for every `g ∈ A`.  Then there is a probability
measure `ν` with `∫ f d(μ i) → ∫ f dν` along `l` for every bounded continuous `f`. -/
theorem exists_tendsto_of_isTightMeasureSet_subalgebra {ι : Type*} {l : Filter ι} [l.NeBot]
    {s : Set ι} (hs : s ∈ l) {μ : ι → Measure E} (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hT : IsTightMeasureSet (μ '' s)) (A : StarSubalgebra ℝ (E →ᵇ ℝ))
    (hA : (A.map (toContinuousMapStarₐ ℝ)).SeparatesPoints)
    (hconv : ∀ g ∈ A, ∃ a : ℝ, Tendsto (fun i => ∫ x, g x ∂μ i) l (𝓝 a)) :
    ∃ ν : Measure E, IsProbabilityMeasure ν ∧
      ∀ f : E →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ν)) := by
  classical
  let x0 : E := Classical.arbitrary E
  let m : ι → ProbabilityMeasure E := fun i =>
    if h : IsProbabilityMeasure (μ i) then ⟨μ i, h⟩ else ⟨Measure.dirac x0, inferInstance⟩
  have hm : ∀ i ∈ s, ((m i : ProbabilityMeasure E) : Measure E) = μ i := by
    intro i hi
    have h := hprob i hi
    simp [m, h]
  set S : Set (ProbabilityMeasure E) := m '' s with hS
  have hSt : IsTightMeasureSet {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ S} := by
    have : {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ S} = μ '' s := by
      ext ν'
      constructor
      · rintro ⟨ν, ⟨i, hi, rfl⟩, rfl⟩
        exact ⟨i, hi, (hm i hi).symm⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨m i, ⟨i, hi, rfl⟩, hm i hi⟩
    rw [this]
    exact hT
  have hK : IsCompact (closure S) := isCompact_closure_of_isTightMeasureSet hSt
  have hmem : ∀ᶠ i in l, m i ∈ closure S := by
    filter_upwards [hs] with i hi using subset_closure ⟨i, hi, rfl⟩
  have hclu : ∀ g ∈ A, ∀ a : ℝ, Tendsto (fun i => ∫ x, g x ∂μ i) l (𝓝 a) →
      ∀ x : ProbabilityMeasure E, MapClusterPt x l m → ∫ y, g y ∂(x : Measure E) = a := by
    intro g _ a ha x hx
    have hcont := ProbabilityMeasure.continuous_integral_boundedContinuousFunction g
    have h1 := hx.tendsto_comp (hcont.tendsto x)
    have h2 : Tendsto (fun i => ∫ y, g y ∂(m i : Measure E)) l (𝓝 a) := by
      refine ha.congr' ?_
      filter_upwards [hs] with i hi
      rw [hm i hi]
    have h3 : NeBot (𝓝 (∫ y, g y ∂(x : Measure E)) ⊓ 𝓝 a) :=
      Filter.NeBot.mono h1 (inf_le_inf_left _ h2)
    exact eq_of_nhds_neBot h3
  have huniq : ∀ x x' : ProbabilityMeasure E, MapClusterPt x l m → MapClusterPt x' l m →
      x = x' := by
    intro x x' hx hx'
    apply ProbabilityMeasure.toMeasure_injective
    refine ext_of_forall_mem_subalgebra_integral_eq_of_polish hA (fun g hg => ?_)
    obtain ⟨a, ha⟩ := hconv g hg
    rw [hclu g hg a ha x hx, hclu g hg a ha x' hx']
  obtain ⟨ν, -, hν⟩ := hK.exists_mapClusterPt (f := l) (u := m) (Filter.le_principal_iff.2 hmem)
  have hlim : Tendsto m l (𝓝 ν) :=
    hK.tendsto_nhds_of_unique_mapClusterPt hmem (fun x _ hx => huniq x ν hx hν)
  refine ⟨(ν : Measure E), inferInstance, fun f => ?_⟩
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) f
  refine this.congr' ?_
  filter_upwards [hs] with i hi
  rw [hm i hi]

end WeakLimit

end LatticeProb
