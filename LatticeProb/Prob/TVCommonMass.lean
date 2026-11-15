import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.TVLocal

/-! A total variation bound for measures with a common summand. -/

open MeasureTheory

namespace LatticeProb

/-- A common summand leaves at most the larger residual mass in total variation. -/
theorem tvDist_add_common_le {α : Type*} [MeasurableSpace α] (μ ν ρ : Measure α) :
    QuantumZipper.TV.tvDist (μ + ν) (μ + ρ) ≤ ν Set.univ ⊔ ρ Set.univ := by
  refine iSup_le fun s => iSup_le fun _ => sup_le ?_ ?_
  · calc
      (μ + ν) s - (μ + ρ) s ≤ ν s - ρ s := by
        simpa only [Measure.add_apply] using
          (add_tsub_add_le_tsub_left (a := μ s) (b := ν s) (c := ρ s))
      _ ≤ ν Set.univ := (tsub_le_self).trans (measure_mono (Set.subset_univ s))
      _ ≤ ν Set.univ ⊔ ρ Set.univ := le_sup_left
  · calc
      (μ + ρ) s - (μ + ν) s ≤ ρ s - ν s := by
        simpa only [Measure.add_apply] using
          (add_tsub_add_le_tsub_left (a := μ s) (b := ρ s) (c := ν s))
      _ ≤ ρ Set.univ := (tsub_le_self).trans (measure_mono (Set.subset_univ s))
      _ ≤ ν Set.univ ⊔ ρ Set.univ := le_sup_right

end LatticeProb
