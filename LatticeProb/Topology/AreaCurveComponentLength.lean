import LatticeProb.Topology.AreaCurveComponentIntervalOrder
import LatticeProb.Topology.AreaComponentWitnessTransfer

/-! # Lengths of component intervals of area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory Function
open scoped BigOperators

namespace LatticeProb

/-- The intervals tracing finitely many distinct nonempty components of a
segment have total length at most the length of the segment. -/
theorem sum_component_interval_lengths_le
    {ι : Type*} (F : Finset ι) (η : C(ℝ, ℂ)) (μ : Measure ℂ)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {s t : ℝ} (hst : s < t) (x : ι → ℂ) (a b : ι → ℝ)
    (hne : ∀ i ∈ F, (connectedComponentIn (interior (η '' Icc s t)) (x i)).Nonempty)
    (himage : ∀ i ∈ F, η '' Icc (a i) (b i) =
      closure (connectedComponentIn (interior (η '' Icc s t)) (x i)))
    (hdistinct : (F : Set ι).Pairwise fun i j =>
      connectedComponentIn (interior (η '' Icc s t)) (x i) ≠
        connectedComponentIn (interior (η '' Icc s t)) (x j)) :
    ∑ i ∈ F, (b i - a i) ≤ t - s := by
  classical
  have hbds : ∀ i ∈ F, s ≤ a i ∧ a i < b i ∧ b i ≤ t := by
    intro i hi
    exact component_interval_bounds_of_area_curve η μ (x i) s t (a i) (b i)
      hst harea (hne i hi) (himage i hi)
  have hdisj : (F : Set ι).PairwiseDisjoint fun i => Ioo (a i) (b i) := by
    intro i hi j hj hij
    have hord := component_interval_order_of_proper_area_curve η μ η.continuous hp hs hmap
      harea hst (hbds i hi).2.1 (hbds j hj).2.1 (x i) (x j)
      (hdistinct hi hj hij) (himage i hi) (himage j hj)
    apply Set.disjoint_left.mpr
    intro z hz hz'
    rcases hord with h | h <;> linarith [hz.1, hz.2, hz'.1, hz'.2]
  have hsum : ENNReal.ofReal (∑ i ∈ F, (b i - a i)) ≤ ENNReal.ofReal (t - s) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => sub_nonneg.mpr (hbds i hi).2.1.le),
      ← Real.volume_Icc]
    calc
      ∑ i ∈ F, ENNReal.ofReal (b i - a i) = ∑ i ∈ F, volume (Ioo (a i) (b i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Real.volume_Ioo.symm
      _ = volume (⋃ i ∈ F, Ioo (a i) (b i)) :=
        (measure_biUnion_finset hdisj fun i hi => measurableSet_Ioo).symm
      _ ≤ volume (Icc s t) := by
        apply measure_mono
        apply iUnion₂_subset
        intro i hi z hz
        exact ⟨(hbds i hi).1.trans hz.1.le, hz.2.le.trans (hbds i hi).2.2⟩
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hst.le)).1 hsum

end LatticeProb
