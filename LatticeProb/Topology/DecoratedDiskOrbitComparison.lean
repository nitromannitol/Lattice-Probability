import LatticeProb.Topology.DecoratedDiskMobiusAction
import LatticeProb.Topology.DecoratedMeasureComparison
import LatticeProb.Topology.ContinuousOrbitInfimum

/-! # Comparisons of decorated disk orbits -/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- A finite measure, a parametrized curve and finitely many points in the closed disk. -/
abbrev DiskDecoration (T ι : Type*) [TopologicalSpace T] :=
  FiniteMeasure ClosedUnitDisk × C(T, ClosedUnitDisk) × (ι → ClosedUnitDisk)

/-- Apply a disk Möbius map to every coordinate of a decoration. -/
def diskDecorationAction {T ι : Type*} [TopologicalSpace T]
    (d : DiskDecoration T ι) (p : DiskMobiusParameters) : DiskDecoration T ι :=
  ((d.1).map (fun x => diskMobiusAction (x, p)),
    ⟨fun t => diskMobiusAction (d.2.1 t, p),
      continuous_diskMobiusAction.comp (d.2.1.continuous.prodMk continuous_const)⟩,
    fun i => diskMobiusAction (d.2.2 i, p))

/-- The finite-measure, full-curve and marked-point comparison of two decorations. -/
def diskDecorationComparison {T ι : Type*} [TopologicalSpace T] [CompactSpace T]
    [Fintype ι] (d e : DiskDecoration T ι) : ℝ≥0∞ :=
  ENNReal.ofReal (levyProkhorovDist (d.1 : Measure ClosedUnitDisk) (e.1 : Measure ClosedUnitDisk) +
    dist d.2.1 e.2.1 + ∑ i, dist (d.2.2 i) (e.2.2 i))

/-- The two-sided disk orbit comparison of continuously varying decorations is measurable. -/
theorem measurable_iInf_diskDecorationComparison
    {Z T ι : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [Fintype ι]
    {d e : Z → DiskDecoration T ι} (hd : Continuous d) (he : Continuous e) :
    Measurable (fun z => ⨅ p : DiskMobiusParameters, ⨅ q : DiskMobiusParameters,
      diskDecorationComparison (diskDecorationAction (d z) p) (diskDecorationAction (e z) q)) := by
  let A : Z × DiskMobiusParameters → DiskDecoration T ι :=
    fun v => diskDecorationAction (d v.1) v.2
  let B : Z × DiskMobiusParameters → DiskDecoration T ι :=
    fun v => diskDecorationAction (e v.1) v.2
  have hA : Continuous A := by
    exact continuous_varyingDecorated_diskMobiusAction
      ((continuous_fst.comp hd).comp continuous_fst)
      ((continuous_fst.comp (continuous_snd.comp hd)).comp continuous_fst)
      ((continuous_snd.comp (continuous_snd.comp hd)).comp continuous_fst) continuous_snd
  have hB : Continuous B := by
    exact continuous_varyingDecorated_diskMobiusAction
      ((continuous_fst.comp he).comp continuous_fst)
      ((continuous_fst.comp (continuous_snd.comp he)).comp continuous_fst)
      ((continuous_snd.comp (continuous_snd.comp he)).comp continuous_fst) continuous_snd
  have hc : Continuous (fun v : DiskDecoration T ι × DiskDecoration T ι =>
      diskDecorationComparison v.1 v.2) := by
    apply ENNReal.continuous_ofReal.comp
    exact continuous_decoratedMeasureComparison
      (continuous_fst.comp continuous_fst) (continuous_fst.comp continuous_snd)
      (continuous_fst.comp (continuous_snd.comp continuous_fst))
      (continuous_fst.comp (continuous_snd.comp continuous_snd))
      (continuous_snd.comp (continuous_snd.comp continuous_fst))
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
  let : Nonempty DiskMobiusParameters := ⟨⟨⟨0, by simp [Metric.mem_ball]⟩,
    ⟨1, by simp⟩⟩⟩
  exact measurable_iInf_comparison A B (fun v => diskDecorationComparison v.1 v.2) hA hB hc

end LatticeProb
