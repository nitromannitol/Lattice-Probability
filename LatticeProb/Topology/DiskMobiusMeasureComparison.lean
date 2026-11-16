import LatticeProb.Topology.DiskMobiusBijection
import LatticeProb.Prob.NestedSubspaceProkhorov

/-! # Open and closed disk measure comparisons -/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory

namespace LatticeProb

/-- The inclusion of the open unit disk in the closed unit disk. -/
def openDiskToClosed (z : ball (0 : ℂ) 1) : ClosedUnitDisk :=
  ⟨z, ball_subset_closedBall z.property⟩

/-- The restriction of a disk Möbius map to the open unit disk. -/
def openDiskMobiusAction (p : DiskMobiusParameters) (z : ball (0 : ℂ) 1) :
    ball (0 : ℂ) 1 :=
  ⟨(p.2 : ℂ) * QuantumZipper.CA.diskMobius p.1 z,
    (diskMobiusParameters_holomorphic_bijOn p).2.1 z.property⟩

/-- Inclusion commutes with the disk Möbius action on the open disk. -/
theorem openDiskToClosed_mobius (p : DiskMobiusParameters) (z : ball (0 : ℂ) 1) :
    openDiskToClosed (openDiskMobiusAction p z) = diskMobiusAction (openDiskToClosed z, p) := by
  rfl

/-- The open-disk Möbius action is continuous. -/
theorem continuous_openDiskMobiusAction (p : DiskMobiusParameters) :
    Continuous (openDiskMobiusAction p) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun z : ball (0 : ℂ) 1 =>
    ((diskMobiusAction (openDiskToClosed z, p) : ClosedUnitDisk) : ℂ))
  exact continuous_subtype_val.comp (continuous_diskMobiusAction.comp
    ((continuous_subtype_val.subtype_mk _).prodMk continuous_const))

/-- Möbius pushforward commutes with inclusion of the open disk in the closed disk. -/
theorem map_openDiskMobiusAction (p : DiskMobiusParameters)
    (μ : Measure (ball (0 : ℂ) 1)) :
    (μ.map openDiskToClosed).map (fun z => diskMobiusAction (z, p)) =
      (μ.map (openDiskMobiusAction p)).map openDiskToClosed := by
  have hi : Measurable openDiskToClosed := measurable_subtype_coe.subtype_mk
  have hc : Measurable (fun z => diskMobiusAction (z, p)) :=
    (continuous_diskMobiusAction.comp (continuous_id.prodMk continuous_const)).measurable
  rw [Measure.map_map hc hi, Measure.map_map hi (continuous_openDiskMobiusAction p).measurable]
  rfl

/-- Open- and closed-disk extended Lévy–Prokhorov comparisons agree after Möbius pushforward. -/
theorem levyProkhorovEDist_diskMobiusAction (p q : DiskMobiusParameters)
    (μ ν : Measure (ball (0 : ℂ) 1)) :
    levyProkhorovEDist ((μ.map openDiskToClosed).map (fun z => diskMobiusAction (z, p)))
      ((ν.map openDiskToClosed).map (fun z => diskMobiusAction (z, q))) =
    levyProkhorovEDist (μ.map (openDiskMobiusAction p)) (ν.map (openDiskMobiusAction q)) := by
  rw [map_openDiskMobiusAction, map_openDiskMobiusAction]
  exact levyProkhorovEDist_map_nestedSubtype isOpen_ball.measurableSet
    isClosed_closedBall.measurableSet ball_subset_closedBall _ _

/-- The corresponding real-valued Lévy–Prokhorov comparisons agree. -/
theorem levyProkhorovDist_diskMobiusAction (p q : DiskMobiusParameters)
    (μ ν : Measure (ball (0 : ℂ) 1)) :
    levyProkhorovDist ((μ.map openDiskToClosed).map (fun z => diskMobiusAction (z, p)))
      ((ν.map openDiskToClosed).map (fun z => diskMobiusAction (z, q))) =
    levyProkhorovDist (μ.map (openDiskMobiusAction p)) (ν.map (openDiskMobiusAction q)) := by
  unfold levyProkhorovDist
  rw [levyProkhorovEDist_diskMobiusAction]

end LatticeProb
