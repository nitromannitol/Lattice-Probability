import LatticeProb.Topology.DiskMobiusMeasureComparison
import LatticeProb.Topology.DecoratedDiskOrbitComparison

/-! # Comparisons of disk decorations with interior measures -/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- A disk decoration with its finite measure on the open disk and its curve and marks
    on the closed disk. -/
abbrev OpenMeasureDiskDecoration (T ι : Type*) [TopologicalSpace T] :=
  FiniteMeasure (ball (0 : ℂ) 1) × C(T, ClosedUnitDisk) × (ι → ClosedUnitDisk)

/-- Regard the interior measure as a measure on the closed disk. -/
def OpenMeasureDiskDecoration.toClosed {T ι : Type*} [TopologicalSpace T]
    (d : OpenMeasureDiskDecoration T ι) : DiskDecoration T ι :=
  (d.1.map openDiskToClosed, d.2.1, d.2.2)

/-- The interior-measure comparison keeps the entire transformed curves and all marks. -/
def openMeasureDiskComparison {T ι : Type*} [TopologicalSpace T] [CompactSpace T]
    [Fintype ι] (d e : OpenMeasureDiskDecoration T ι) (p q : DiskMobiusParameters) : ℝ≥0∞ :=
  ENNReal.ofReal (levyProkhorovDist ((d.1 : Measure _).map (openDiskMobiusAction p))
      ((e.1 : Measure _).map (openDiskMobiusAction q)) +
    dist (diskDecorationAction d.toClosed p).2.1 (diskDecorationAction e.toClosed q).2.1 +
    ∑ i, dist ((diskDecorationAction d.toClosed p).2.2 i)
      ((diskDecorationAction e.toClosed q).2.2 i))

/-- The interior-measure and closed-disk comparisons agree for independently chosen maps. -/
theorem diskDecorationComparison_toClosed {T ι : Type*} [TopologicalSpace T] [CompactSpace T]
    [Fintype ι] (d e : OpenMeasureDiskDecoration T ι) (p q : DiskMobiusParameters) :
    diskDecorationComparison (diskDecorationAction d.toClosed p)
      (diskDecorationAction e.toClosed q) = openMeasureDiskComparison d e p q := by
  unfold diskDecorationComparison openMeasureDiskComparison
  change ENNReal.ofReal (levyProkhorovDist
      (((d.1 : Measure _).map openDiskToClosed).map (fun z => diskMobiusAction (z, p)))
      (((e.1 : Measure _).map openDiskToClosed).map (fun z => diskMobiusAction (z, q))) + _ + _) = _
  rw [levyProkhorovDist_diskMobiusAction]

/-- The two independently optimized comparisons agree. -/
theorem iInf_diskDecorationComparison_toClosed {T ι : Type*} [TopologicalSpace T]
    [CompactSpace T] [Fintype ι] (d e : OpenMeasureDiskDecoration T ι) :
    (⨅ p : DiskMobiusParameters, ⨅ q : DiskMobiusParameters,
      diskDecorationComparison (diskDecorationAction d.toClosed p)
        (diskDecorationAction e.toClosed q)) =
    (⨅ p : DiskMobiusParameters, ⨅ q : DiskMobiusParameters, openMeasureDiskComparison d e p q) := by
  simp only [diskDecorationComparison_toClosed]

/-- Inclusion of the open disk into the closed disk is continuous. -/
theorem continuous_openDiskToClosed : Continuous openDiskToClosed := by
  exact continuous_induced_rng.mpr continuous_subtype_val

/-- The comparison infimum is measurable for continuously varying interior measures,
    parametrized curves and marked points. -/
theorem measurable_iInf_openMeasureDiskComparison
    {Z T ι : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [Fintype ι]
    {d e : Z → OpenMeasureDiskDecoration T ι} (hd : Continuous d) (he : Continuous e) :
    Measurable (fun z => ⨅ p : DiskMobiusParameters, ⨅ q : DiskMobiusParameters,
      openMeasureDiskComparison (d z) (e z) p q) := by
  have hlift : Continuous (fun x : OpenMeasureDiskDecoration T ι => x.toClosed) := by
    exact (FiniteMeasure.continuous_map continuous_openDiskToClosed |>.comp continuous_fst).prodMk
      ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd))
  have h := measurable_iInf_diskDecorationComparison (hlift.comp hd) (hlift.comp he)
  simpa only [Function.comp_apply, iInf_diskDecorationComparison_toClosed] using h

end LatticeProb
