import LatticeProb.Topology.AreaCurveComponentLength
import LatticeProb.Topology.AreaCurveComponentVisitCover

/-! # Total length of component intervals -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- Countably many distinct components with interval witnesses covering the
interior of a curve segment have total interval length equal to the segment length. -/
theorem tsum_component_interval_lengths_eq
    {ι : Type*} [Countable ι] (η : C(ℝ, ℂ)) (μ : Measure ℂ)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {s t : ℝ} (hst : s < t) (x : ι → ℂ) (a b : ι → ℝ)
    (hne : ∀ i, (connectedComponentIn (interior (η '' Icc s t)) (x i)).Nonempty)
    (himage : ∀ i, η '' Icc (a i) (b i) =
      closure (connectedComponentIn (interior (η '' Icc s t)) (x i)))
    (hdistinct : Pairwise fun i j =>
      connectedComponentIn (interior (η '' Icc s t)) (x i) ≠
        connectedComponentIn (interior (η '' Icc s t)) (x j))
    (hcover : ∀ z ∈ interior (η '' Icc s t), ∃ i,
      z ∈ connectedComponentIn (interior (η '' Icc s t)) (x i)) :
    (∑' i, ENNReal.ofReal (b i - a i)) = ENNReal.ofReal (t - s) := by
  have hbds : ∀ i, s ≤ a i ∧ a i < b i ∧ b i ≤ t := by
    intro i
    exact component_interval_bounds_of_area_curve η μ (x i) s t (a i) (b i)
      hst harea (hne i) (himage i)
  have hdisj : Pairwise (Disjoint on fun i => Ioo (a i) (b i)) := by
    intro i j hij
    have hord := component_interval_order_of_proper_area_curve η μ η.continuous hp hs hmap
      harea hst (hbds i).2.1 (hbds j).2.1 (x i) (x j)
      (hdistinct hij) (himage i) (himage j)
    apply Set.disjoint_left.mpr
    intro z hz hz'
    rcases hord with h | h <;> linarith [hz.1, hz.2, hz'.1, hz'.2]
  have hsub : (⋃ i, Ioo (a i) (b i)) ⊆ Icc s t := by
    intro u hu
    obtain ⟨i, hi⟩ := mem_iUnion.mp hu
    exact ⟨(hbds i).1.trans hi.1.le, hi.2.le.trans (hbds i).2.2⟩
  have hae := ae_mem_component_intervals_of_proper_area_curve η μ hp hs hmap harea hst
    x a b univ (by simpa using fun i => (hbds i).2.1)
    (by simpa using himage) (by simpa using hcover)
  have heq : (⋃ i, Ioo (a i) (b i)) =ᵐ[volume] Icc s t := by
    filter_upwards [hae] with u hu
    apply propext
    constructor
    · exact fun h => hsub h
    · intro h
      obtain ⟨i, _, hi⟩ := hu h
      exact mem_iUnion.mpr ⟨i, hi⟩
  calc
    (∑' i, ENNReal.ofReal (b i - a i)) = ∑' i, volume (Ioo (a i) (b i)) := by
      simp only [Real.volume_Ioo]
    _ = volume (⋃ i, Ioo (a i) (b i)) :=
      (measure_iUnion hdisj fun i => measurableSet_Ioo).symm
    _ = volume (Icc s t) := measure_congr heq
    _ = ENNReal.ofReal (t - s) := Real.volume_Icc

end LatticeProb
