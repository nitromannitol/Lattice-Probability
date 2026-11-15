import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! # Finiteness of long disjoint intervals -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- In a bounded interval, a pairwise disjoint family of open intervals contains
only finitely many intervals of length at least a given positive number. -/
theorem finite_long_disjoint_intervals
    {ι : Type*} (a b ε : ℝ) (A B : ι → ℝ) (S : Set ι) (hε : 0 < ε)
    (hbounds : ∀ i ∈ S, a ≤ A i ∧ B i ≤ b)
    (hdis : S.Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j))) :
    {i ∈ S | ε ≤ B i - A i}.Finite := by
  let T := {i ∈ S | ε ≤ B i - A i}
  have hfin := Measure.finite_const_le_meas_of_disjoint_iUnion (volume : Measure ℝ)
    (ENNReal.ofReal_pos.mpr hε) (As := fun i : T => Ioo (A i) (B i))
    (fun _ => measurableSet_Ioo)
    (fun i j hij => by
      rw [Function.onFun]
      exact hdis i.2.1 j.2.1 (fun h => hij (Subtype.ext h)))
    (ne_top_of_le_ne_top (measure_Icc_lt_top (a := a) (b := b)).ne
      (measure_mono (iUnion_subset fun i x hx =>
        ⟨(hbounds i i.2.1).1.trans hx.1.le, hx.2.le.trans (hbounds i i.2.1).2⟩)))
  have huniv : {i : T | ENNReal.ofReal ε ≤ volume (Ioo (A i) (B i))} = univ := by
    refine eq_univ_of_forall fun i => ?_
    show ENNReal.ofReal ε ≤ volume (Ioo (A i) (B i))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_le_ofReal i.2.2
  rw [huniv] at hfin
  exact Set.finite_coe_iff.mp (Set.finite_univ_iff.mp hfin)

end LatticeProb
