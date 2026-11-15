import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.D3PlusLSCCInd
import Mathlib.MeasureTheory.Constructions.Pi

/-! Total variation of finite products of probability measures. -/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- The total variation distance of finite products of probability measures
is at most the sum of the distances of the factors. -/
theorem tvDist_pi_fin_le_sum {α : Type*} [MeasurableSpace α] (n : ℕ)
    (μ ν : Fin n → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] :
    QuantumZipper.TV.tvDist (Measure.pi μ) (Measure.pi ν) ≤
      ∑ i, QuantumZipper.TV.tvDist (μ i) (ν i) := by
  classical
  induction n with
  | zero =>
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
    rw [QuantumZipper.TV.tvDist_self]
    exact bot_le
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
    have hμ := (measurePreserving_piFinSuccAbove μ 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove ν 0).map_eq
    have hmap : QuantumZipper.TV.tvDist (Measure.pi μ) (Measure.pi ν) ≤
        QuantumZipper.TV.tvDist (Measure.map e (Measure.pi μ))
          (Measure.map e (Measure.pi ν)) := by
      have h := QuantumZipper.TV.tvDist_map_le (μ := Measure.map e (Measure.pi μ))
        (ν := Measure.map e (Measure.pi ν)) e.symm.measurable
      have hμmap : Measure.map e.symm (Measure.map e (Measure.pi μ)) = Measure.pi μ := by
        simpa only [MeasurableEquiv.symm_symm] using (e.symm.map_map_symm (ν := Measure.pi μ))
      have hνmap : Measure.map e.symm (Measure.map e (Measure.pi ν)) = Measure.pi ν := by
        simpa only [MeasurableEquiv.symm_symm] using (e.symm.map_map_symm (ν := Measure.pi ν))
      simpa only [hμmap, hνmap] using h
    rw [hμ, hν] at hmap
    have heq : QuantumZipper.TV.tvDist (Measure.pi μ) (Measure.pi ν) ≤
        QuantumZipper.TV.tvDist ((μ 0).prod (Measure.pi fun i : Fin n => μ i.succ))
          ((ν 0).prod (Measure.pi fun i : Fin n => ν i.succ)) := by
      simpa only [Fin.succAbove_zero] using hmap
    have htail := ih (fun i : Fin n => μ i.succ) (fun i : Fin n => ν i.succ)
    rw [Fin.sum_univ_succ]
    refine heq.trans ?_
    refine QuantumZipper.D3Plus.lscc_tvDist_prod_le.trans ?_
    exact add_le_add le_rfl htail

end LatticeProb
