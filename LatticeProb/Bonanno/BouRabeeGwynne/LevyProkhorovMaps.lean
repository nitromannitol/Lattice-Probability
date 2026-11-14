/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.LevyProkhorovMaps at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws

/-!
# Pushing forward the actual curve laws

A measurable map with Lipschitz constant one contracts the Lévy–Prokhorov
edistance. In particular, convergence of the stopped curve laws controls their
actual endpoint laws, as required for the Section 4 implication to Theorem B(b).
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace BouRabeeGwynne

private lemma thickening_preimage_subset_of_lipschitz_one
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {f : X → Y} (hf : LipschitzWith 1 f) (r : ℝ) (S : Set Y) :
    thickening r (f ⁻¹' S) ⊆ f ⁻¹' thickening r S := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (mem_thickening_iff_exists_edist_lt _ _).mp hx
  apply (mem_thickening_iff_exists_edist_lt _ _).mpr
  refine ⟨f y, hy, ?_⟩
  have hle : edist (f x) (f y) ≤ edist x y := by
    simpa only [ENNReal.coe_one, one_mul] using hf x y
  exact hle.trans_lt hxy

/-- The actual Lévy–Prokhorov edistance contracts under a measurable
map whose Lipschitz constant is one. No coupling existence is assumed. -/
theorem levyProkhorovEDist_map_le_of_lipschitz_one
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {f : X → Y} (hf : LipschitzWith 1 f) (hm : Measurable f)
    (μ ν : Measure X) :
    levyProkhorovEDist (μ.map f) (ν.map f) ≤ levyProkhorovEDist μ ν := by
  apply levyProkhorovEDist_le_of_forall
  intro ε S hε _ hS
  have hpre : thickening ε.toReal (f ⁻¹' S) ⊆ f ⁻¹' thickening ε.toReal S :=
    thickening_preimage_subset_of_lipschitz_one hf _ _
  constructor
  · rw [Measure.map_apply hm hS, Measure.map_apply hm isOpen_thickening.measurableSet]
    exact (left_measure_le_of_levyProkhorovEDist_lt hε (hS.preimage hm)).trans
      (add_le_add (measure_mono hpre) le_rfl)
  · rw [Measure.map_apply hm hS, Measure.map_apply hm isOpen_thickening.measurableSet]
    exact (right_measure_le_of_levyProkhorovEDist_lt hε (hS.preimage hm)).trans
      (add_le_add (measure_mono hpre) le_rfl)

/-- The Fréchet endpoint map transfers the same probability-law error to spatial
endpoint laws. Its Lipschitz property was proved from the actual time-change metric. -/
theorem levyProkhorovEDist_endpoint_map_le {d : ℕ}
    (μ ν : Measure (CurveSpace d)) :
    levyProkhorovEDist (μ.map CurveSpace.endPoint) (ν.map CurveSpace.endPoint) ≤
      levyProkhorovEDist μ ν :=
  levyProkhorovEDist_map_le_of_lipschitz_one CurveSpace.endPoint_lipschitz
    CurveSpace.continuous_endPoint.measurable μ ν

end BouRabeeGwynne
