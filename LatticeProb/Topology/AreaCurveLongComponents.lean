import LatticeProb.Topology.AreaCurveComponentIntervalOrder
import LatticeProb.Topology.AreaComponentWitnessTransfer

/-! # Long component intervals of area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- Only finitely many distinct witnessed components of a segment can be traced
by intervals whose length is at least a fixed positive threshold. -/
theorem finite_long_component_intervals
    {ι : Type*} (η : C(ℝ, ℂ)) (μ : Measure ℂ)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {s t ε : ℝ} (hst : s < t) (hε : 0 < ε) (x : ι → ℂ) (a b : ι → ℝ)
    (A : Set ι)
    (hne : ∀ i ∈ A, (connectedComponentIn (interior (η '' Icc s t)) (x i)).Nonempty)
    (himage : ∀ i ∈ A, η '' Icc (a i) (b i) =
      closure (connectedComponentIn (interior (η '' Icc s t)) (x i)))
    (hdistinct : A.Pairwise fun i j =>
      connectedComponentIn (interior (η '' Icc s t)) (x i) ≠
        connectedComponentIn (interior (η '' Icc s t)) (x j)) :
    {i ∈ A | ε ≤ b i - a i}.Finite := by
  let S := {i ∈ A | ε ≤ b i - a i}
  have hbds : ∀ i : S, s ≤ a i ∧ a i < b i ∧ b i ≤ t := by
    intro i
    exact component_interval_bounds_of_area_curve η μ (x i) s t (a i) (b i)
      hst harea (hne i i.2.1) (himage i i.2.1)
  have hfin := Measure.finite_const_le_meas_of_disjoint_iUnion (volume : Measure ℝ)
    (ENNReal.ofReal_pos.mpr hε) (As := fun i : S => Ioo (a i) (b i))
    (fun _ => measurableSet_Ioo)
    (fun i j hij => by
      rw [Function.onFun]
      have hord := component_interval_order_of_proper_area_curve η μ η.continuous hp hs hmap
        harea hst (hbds i).2.1 (hbds j).2.1 (x i) (x j)
        (hdistinct i.2.1 j.2.1 (fun h => hij (Subtype.ext h)))
        (himage i i.2.1) (himage j j.2.1)
      apply Set.disjoint_left.mpr
      intro z hz hz'
      rcases hord with h | h <;> linarith [hz.1, hz.2, hz'.1, hz'.2])
    (ne_top_of_le_ne_top (measure_Icc_lt_top (a := s) (b := t)).ne
      (measure_mono (iUnion_subset fun i z hz =>
        ⟨(hbds i).1.trans hz.1.le, hz.2.le.trans (hbds i).2.2⟩)))
  have huniv : {i : S | ENNReal.ofReal ε ≤ volume (Ioo (a i) (b i))} = univ := by
    refine eq_univ_of_forall fun i => ?_
    show ENNReal.ofReal ε ≤ volume (Ioo (a i) (b i))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_le_ofReal i.2.2
  rw [huniv] at hfin
  exact Set.finite_coe_iff.mp (Set.finite_univ_iff.mp hfin)

end LatticeProb
