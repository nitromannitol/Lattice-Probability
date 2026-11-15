import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.TVLocal

/-! Total variation bounds for sums of measures. -/

open MeasureTheory

namespace LatticeProb

/-- The total variation distance of sums is bounded by the sum of distances. -/
theorem tvDist_add_add_le {α : Type*} [MeasurableSpace α]
    (μ₁ μ₂ ν₁ ν₂ : Measure α) :
    QuantumZipper.TV.tvDist (μ₁ + μ₂) (ν₁ + ν₂) ≤
      QuantumZipper.TV.tvDist μ₁ ν₁ + QuantumZipper.TV.tvDist μ₂ ν₂ := by
  refine iSup_le fun s => iSup_le fun hs => sup_le ?_ ?_
  · calc
      (μ₁ + μ₂) s - (ν₁ + ν₂) s ≤ (μ₁ s - ν₁ s) + (μ₂ s - ν₂ s) := by
        simpa only [Measure.add_apply] using
          (add_tsub_add_le_tsub_add_tsub (a := μ₁ s) (b := μ₂ s)
            (c := ν₁ s) (d := ν₂ s))
      _ ≤ _ := add_le_add (QuantumZipper.TV.le_tvDist hs) (QuantumZipper.TV.le_tvDist hs)
  · calc
      (ν₁ + ν₂) s - (μ₁ + μ₂) s ≤ (ν₁ s - μ₁ s) + (ν₂ s - μ₂ s) := by
        simpa only [Measure.add_apply] using
          (add_tsub_add_le_tsub_add_tsub (a := ν₁ s) (b := ν₂ s)
            (c := μ₁ s) (d := μ₂ s))
      _ ≤ _ := add_le_add (QuantumZipper.TV.le_tvDist' hs) (QuantumZipper.TV.le_tvDist' hs)

/-- A finite sum of measure pairs has total variation distance at most the
sum of the pairwise distances. -/
theorem tvDist_finset_sum_le {α ι : Type*} [MeasurableSpace α]
    (s : Finset ι) (μ ν : ι → Measure α) :
    QuantumZipper.TV.tvDist (∑ i ∈ s, μ i) (∑ i ∈ s, ν i) ≤
      ∑ i ∈ s, QuantumZipper.TV.tvDist (μ i) (ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, QuantumZipper.TV.tvDist_self, le_refl]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (tvDist_add_add_le _ _ _ _).trans (add_le_add le_rfl ih)

end LatticeProb
