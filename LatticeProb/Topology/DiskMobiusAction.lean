import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley
import LatticeProb.Prob.FiniteMeasureContinuousAction

/-! # Continuous disk Möbius actions -/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped ComplexConjugate

namespace LatticeProb

/-- The closed unit disk in the complex plane. -/
abbrev ClosedUnitDisk := closedBall (0 : ℂ) 1

/-- Parameters for a disk Möbius map, including a unit-modulus rotation. -/
abbrev DiskMobiusParameters := ball (0 : ℂ) 1 × {u : ℂ // ‖u‖ = 1}

/-- The rotation of a disk Möbius map preserves the closed disk. -/
theorem diskMobius_mul_mem_closedBall (z : ClosedUnitDisk) (p : DiskMobiusParameters) :
    (p.2 : ℂ) * QuantumZipper.CA.diskMobius p.1 z ∈ closedBall (0 : ℂ) 1 := by
  have ha : ‖(p.1 : ℂ)‖ < 1 := mem_ball_zero_iff.mp p.1.property
  have hz : ‖(z : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
  have h := QuantumZipper.CA.one_sub_sq_norm_diskMobius ha hz
  have hnonneg : 0 ≤ (1 - ‖(p.1 : ℂ)‖ ^ 2) * (1 - ‖(z : ℂ)‖ ^ 2) /
      Complex.normSq (1 - conj (p.1 : ℂ) * (z : ℂ)) := by
    apply div_nonneg
    · apply mul_nonneg <;> nlinarith [norm_nonneg (p.1 : ℂ), norm_nonneg (z : ℂ)]
    · exact Complex.normSq_nonneg _
  rw [mem_closedBall_zero_iff, norm_mul, p.2.property, one_mul]
  nlinarith [norm_nonneg (QuantumZipper.CA.diskMobius p.1 z)]

/-- A disk Möbius map and a unit rotation acting on the closed disk. -/
def diskMobiusAction (q : ClosedUnitDisk × DiskMobiusParameters) : ClosedUnitDisk :=
  ⟨(q.2.2 : ℂ) * QuantumZipper.CA.diskMobius q.2.1 q.1,
    diskMobius_mul_mem_closedBall q.1 q.2⟩

/-- The disk Möbius action is jointly continuous in the point and parameters. -/
theorem continuous_diskMobiusAction : Continuous diskMobiusAction := by
  apply continuous_induced_rng.mpr
  change Continuous (fun q : ClosedUnitDisk × DiskMobiusParameters =>
    (q.2.2 : ℂ) * (((q.1 : ℂ) - (q.2.1 : ℂ)) /
      (1 - conj (q.2.1 : ℂ) * (q.1 : ℂ))))
  apply Continuous.mul (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro q
    exact QuantumZipper.CA.diskMobius_denom_ne_zero
      (mem_ball_zero_iff.mp q.2.1.property) (mem_closedBall_zero_iff.mp q.1.property)

/-- Pushforward of a finite measure varies continuously with the disk Möbius parameters. -/
theorem continuous_finiteMeasure_map_diskMobiusAction (μ : FiniteMeasure ClosedUnitDisk) :
    Continuous (fun p : DiskMobiusParameters => μ.map (fun z => diskMobiusAction (z, p))) :=
  continuous_finiteMeasure_map_family μ continuous_diskMobiusAction

end LatticeProb
