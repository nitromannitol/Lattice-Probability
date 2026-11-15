import LatticeProb.Prob.UniformPhaseCells
import LatticeProb.Prob.TVCommonMass
import LatticeProb.Analysis.IntervalCellPartition

/-! Uniform control of phase distributions on bounded intervals. -/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- The phase of Lebesgue measure on an interval differs from the
corresponding multiple of uniform measure by at most one period in total variation. -/
theorem tvDist_map_fract_mul_restrict_Ico_le {a u v : ℝ} (ha : 0 < a)
    (huv : u ≤ v) (c : ℝ) :
    QuantumZipper.TV.tvDist
        (Measure.map (fun x : ℝ => Int.fract (a * x - c)) (volume.restrict (Ico u v)))
        (ENNReal.ofReal (v - u) • volume.restrict (Ico 0 1)) ≤
      ENNReal.ofReal a⁻¹ := by
  let f : ℝ → ℝ := fun x => Int.fract (a * x - c)
  let U : Measure ℝ := volume.restrict (Ico 0 1)
  have hf : Measurable f := measurable_fract.comp (by fun_prop)
  obtain ⟨n, hun, hnv, hvn⟩ := exists_cell_endpoint u v a⁻¹ huv (inv_pos.mpr ha)
  let w := u + (n : ℝ) * a⁻¹
  have huw : u ≤ w := hun
  have hwv : w ≤ v := hnv
  have hrem : v - w ≤ a⁻¹ := by dsimp [w]; linarith
  have hn : 0 ≤ (n : ℝ) * a⁻¹ := mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr ha.le)
  have hr : 0 ≤ v - w := sub_nonneg.mpr hwv
  have hsplit : Ico u v = Ico u w ∪ Ico w v :=
    (Ico_union_Ico_eq_Ico huw hwv).symm
  have hmap : Measure.map f (volume.restrict (Ico u v)) =
      n • (ENNReal.ofReal a⁻¹ • U) + Measure.map f (volume.restrict (Ico w v)) := by
    rw [hsplit, Measure.restrict_union Ico_disjoint_Ico_same measurableSet_Ico,
      Measure.map_add _ _ hf]
    congr 1
    exact map_fract_mul_restrict_cells ha u c n
  have hcoeff : ENNReal.ofReal (v - u) =
      (n : ℝ≥0∞) * ENNReal.ofReal a⁻¹ + ENNReal.ofReal (v - w) := by
    have heq : v - u = (n : ℝ) * a⁻¹ + (v - w) := by dsimp [w]; ring
    rw [heq, ENNReal.ofReal_add hn hr, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp
  have htarget : ENNReal.ofReal (v - u) • U =
      n • (ENNReal.ofReal a⁻¹ • U) + ENNReal.ofReal (v - w) • U := by
    rw [hcoeff, add_smul, mul_smul]
    simp only [Nat.cast_smul_eq_nsmul]
  have hmass : Measure.map f (volume.restrict (Ico w v)) univ =
      ENNReal.ofReal (v - w) := by
    rw [Measure.map_apply hf MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ, Real.volume_Ico]
  have hU : U univ = 1 := by
    simp [U, Real.volume_Ico]
  rw [hmap, htarget]
  calc
    _ ≤ (Measure.map f (volume.restrict (Ico w v))) univ ⊔
        (ENNReal.ofReal (v - w) • U) univ := tvDist_add_common_le _ _ _
    _ = ENNReal.ofReal (v - w) := by simp [hmass, Measure.smul_apply, hU]
    _ ≤ ENNReal.ofReal a⁻¹ := ENNReal.ofReal_le_ofReal hrem

end LatticeProb
