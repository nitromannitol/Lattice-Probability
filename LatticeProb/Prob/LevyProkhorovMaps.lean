/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/LevyProkhorovMaps.lean and BouRabeeGwynne/PartitionCouplingDistance.lean.
-/
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import LatticeProb.Topology.CurveSpace

/-!
# Lévy–Prokhorov edistance under maps and couplings

A measurable map with Lipschitz constant one contracts the Lévy–Prokhorov
edistance `MeasureTheory.levyProkhorovEDist`, and a coupling whose mass away from
the diagonal is small bounds it. The endpoint map of continuous curves is such a map.
-/

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace LatticeProb

/-- The Borel σ-algebra on curve space, used for measures on `CurveSpace d`. -/
noncomputable instance CurveSpace.measurableSpace (d : ℕ) : MeasurableSpace (CurveSpace d) :=
  borel (CurveSpace d)

/-- The σ-algebra on curve space is the Borel σ-algebra. -/
instance CurveSpace.borelSpace (d : ℕ) : BorelSpace (CurveSpace d) :=
  ⟨rfl⟩

/-- Thickening a preimage under a 1-Lipschitz map stays inside the preimage of the thickening. -/
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

/-- A measurable map with Lipschitz constant one contracts the Lévy–Prokhorov edistance.
No coupling existence is assumed, and the measures are arbitrary. -/
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

/-- The endpoint map of continuous curves contracts the Lévy–Prokhorov edistance between
the laws of curves. -/
theorem levyProkhorovEDist_map_endPoint_le {d : ℕ} (μ ν : Measure (CurveSpace d)) :
    levyProkhorovEDist (μ.map CurveSpace.endPoint) (ν.map CurveSpace.endPoint) ≤
      levyProkhorovEDist μ ν :=
  levyProkhorovEDist_map_le_of_lipschitz_one CurveSpace.endPoint_lipschitz
    CurveSpace.continuous_endPoint.measurable μ ν

/-- A coupling `ρ` of `μ` and `ν` whose mass on pairs at edistance at least `r` is at most `r`
bounds the Lévy–Prokhorov edistance between `μ` and `ν` by `r`. -/
theorem levyProkhorovEDist_le_of_coupling {X : Type*} [PseudoEMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ ν : Measure X) (ρ : Measure (X × X))
    (hfst : ρ.fst = μ) (hsnd : ρ.snd = ν) (r : ℝ≥0)
    (hbad : ρ {p | (r : ℝ≥0∞) ≤ edist p.1 p.2} ≤ r) :
    levyProkhorovEDist μ ν ≤ r := by
  apply sInf_le
  intro A hA
  have hleft : Prod.fst ⁻¹' A ⊆
      (Prod.snd ⁻¹' thickening (r : ℝ) A) ∪ {p : X × X | (r : ℝ≥0∞) ≤ edist p.1 p.2} := by
    intro p hp
    by_cases h : (r : ℝ≥0∞) ≤ edist p.1 p.2
    · exact Or.inr h
    · apply Or.inl
      apply (mem_thickening_iff_exists_edist_lt _ _).mpr
      refine ⟨p.1, hp, ?_⟩
      simpa only [edist_comm, ENNReal.ofReal_coe_nnreal] using (lt_of_not_ge h)
  have hright : Prod.snd ⁻¹' A ⊆
      (Prod.fst ⁻¹' thickening (r : ℝ) A) ∪ {p : X × X | (r : ℝ≥0∞) ≤ edist p.1 p.2} := by
    intro p hp
    by_cases h : (r : ℝ≥0∞) ≤ edist p.1 p.2
    · exact Or.inr h
    · apply Or.inl
      apply (mem_thickening_iff_exists_edist_lt _ _).mpr
      refine ⟨p.2, hp, ?_⟩
      simpa only [ENNReal.ofReal_coe_nnreal] using (lt_of_not_ge h)
  constructor
  · change μ A ≤ ν (thickening (r : ℝ) A) + (r : ℝ≥0∞)
    rw [← hfst, ← hsnd, Measure.fst_apply hA,
      Measure.snd_apply isOpen_thickening.measurableSet]
    exact (measure_mono hleft).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbad))
  · change ν A ≤ μ (thickening (r : ℝ) A) + (r : ℝ≥0∞)
    rw [← hfst, ← hsnd, Measure.snd_apply hA,
      Measure.fst_apply isOpen_thickening.measurableSet]
    exact (measure_mono hright).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbad))

/-! ### Nonvacuity examples -/

/-- Translation by one is a measurable 1-Lipschitz map on `ℝ`, so it contracts the
Lévy–Prokhorov edistance between Dirac masses. -/
example : levyProkhorovEDist ((Measure.dirac (0 : ℝ)).map (fun x : ℝ => x + 1))
    ((Measure.dirac (2 : ℝ)).map (fun x : ℝ => x + 1)) ≤
      levyProkhorovEDist (Measure.dirac (0 : ℝ)) (Measure.dirac (2 : ℝ)) :=
  levyProkhorovEDist_map_le_of_lipschitz_one
    (LipschitzWith.of_edist_le fun x y => by simp [edist_dist, Real.dist_eq])
    (continuous_id.add continuous_const).measurable _ _

/-- The absolute value is a measurable 1-Lipschitz map on `ℝ`, so it contracts the
Lévy–Prokhorov edistance between Dirac masses. -/
example : levyProkhorovEDist ((Measure.dirac (-1 : ℝ)).map abs)
    ((Measure.dirac (1 : ℝ)).map abs) ≤
      levyProkhorovEDist (Measure.dirac (-1 : ℝ)) (Measure.dirac (1 : ℝ)) :=
  levyProkhorovEDist_map_le_of_lipschitz_one
    (LipschitzWith.of_edist_le fun x y => by
      simp only [edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le_abs_sub x y))
    continuous_abs.measurable _ _

/-- The diagonal coupling `μ.map (fun x ↦ (x, x))` of a probability measure with itself
satisfies the coupling bound at every `r > 0`. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ≥0) (hr : 0 < r) :
    levyProkhorovEDist μ μ ≤ r := by
  have hdiag : Measurable fun x : ℝ => (x, x) := measurable_id.prodMk measurable_id
  have hs : MeasurableSet {p : ℝ × ℝ | (r : ℝ≥0∞) ≤ edist p.1 p.2} :=
    measurableSet_le measurable_const (continuous_fst.edist continuous_snd).measurable
  have hempty : (fun x : ℝ => (x, x)) ⁻¹' {p : ℝ × ℝ | (r : ℝ≥0∞) ≤ edist p.1 p.2} = ∅ := by
    ext x
    simp only [mem_preimage, mem_setOf_eq, edist_self, mem_empty_iff_false, iff_false, not_le]
    exact ENNReal.coe_pos.mpr hr
  apply levyProkhorovEDist_le_of_coupling μ μ (μ.map fun x : ℝ => (x, x))
  · simp only [Measure.fst, Measure.map_map measurable_fst hdiag, Function.comp_def]
    exact Measure.map_id
  · simp only [Measure.snd, Measure.map_map measurable_snd hdiag, Function.comp_def]
    exact Measure.map_id
  · rw [Measure.map_apply hdiag hs, hempty, measure_empty]
    exact zero_le

end LatticeProb
