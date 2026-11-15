import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.TVLocal

/-! # Total variation and uniform absolute continuity -/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace LatticeProb

/-- Total variation convergence of image measures gives uniform control of
preimages of sets of small reference measure, eventually along the filter. -/
theorem eventually_preimage_measure_le_of_tendsto_tvDist
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (ν : Measure E) (l : Filter ι) (X : ι → Ω → E)
    (hX : ∀ i, AEMeasurable (X i) P)
    (htv : Tendsto (fun i => QuantumZipper.TV.tvDist (Measure.map (X i) P) ν)
      l (𝓝 0)) :
    ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ≥0∞, 0 < d ∧
      ∀ᶠ i in l, ∀ T : Set E, ν T ≤ d → P ((X i) ⁻¹' T) ≤ e := by
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  refine ⟨e / 2, he2, ?_⟩
  filter_upwards [ENNReal.tendsto_nhds_zero.1 htv _ he2] with i hi T hT
  obtain ⟨S, hTS, hS, hν⟩ := exists_measurable_superset ν T
  calc
    P ((X i) ⁻¹' T) ≤ P ((X i) ⁻¹' S) := measure_mono (preimage_mono hTS)
    _ = Measure.map (X i) P S := (Measure.map_apply₀ (hX i) hS.nullMeasurableSet).symm
    _ ≤ ν S + QuantumZipper.TV.tvDist (Measure.map (X i) P) ν :=
      tsub_le_iff_left.mp (QuantumZipper.TV.le_tvDist hS)
    _ ≤ e / 2 + e / 2 := add_le_add (hν ▸ hT) hi
    _ = e := ENNReal.add_halves e

end LatticeProb
