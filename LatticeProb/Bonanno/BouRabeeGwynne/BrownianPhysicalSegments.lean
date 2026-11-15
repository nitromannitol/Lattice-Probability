/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianPhysicalSegments at commit fdb5cad; local import paths are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.PhysicalExcursionRecovery
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianNextExit

/-! The actual normalized Brownian excursions are exactly the restrictions
of their original physical-time path, not merely endpoint-equivalent curves. -/

open Set
open scoped unitInterval NNReal ENNReal
namespace BouRabeeGwynne

theorem stoppedBrownianRepresentative_eq_physicalTimeSegment {d : ℕ}
    (U : Set (Euc d)) (z : Euc d) (ω : BrownianPath d) :
    stoppedBrownianRepresentative U z ω =
      physicalTimeSegment z ω 0 (continuousExitTime U z ω).toNNReal := by
  apply ContinuousMap.ext
  intro u
  simp only [stoppedBrownianRepresentative, physicalTimeSegment, ContinuousMap.coe_mk,
    NNReal.coe_zero, mul_zero, zero_add]

theorem stoppedBrownianNextRepresentative_eq_physicalTimeSegment {d : ℕ}
    (U : Set (Euc d)) (z : Euc d) (τ : BrownianPath d → ℝ≥0∞) (ω : BrownianPath d)
    (hfinite : brownianNextExitTime U z τ ω ≠ ∞) :
    stoppedBrownianRepresentative U (z + ω (τ ω).toNNReal)
      (shiftedBrownianPath (τ ω).toNNReal ω) =
    physicalTimeSegment z ω (τ ω).toNNReal (brownianNextExitTime U z τ ω).toNNReal := by
  let a : ℝ≥0 := (τ ω).toNNReal
  let b : ℝ≥0 := (brownianNextExitTime U z τ ω).toNNReal
  let η : ℝ≥0∞ := continuousExitTime U (z + ω a) (shiftedBrownianPath a ω)
  have hparts : τ ω ≠ ∞ ∧ η ≠ ∞ := ENNReal.add_ne_top.mp hfinite
  have hb : b = a + η.toNNReal := ENNReal.toNNReal_add hparts.1 hparts.2
  apply ContinuousMap.ext
  intro u
  let q : ℝ≥0 := ⟨(u : ℝ) * (η.toNNReal : ℝ), mul_nonneg u.property.1 η.toNNReal.property⟩
  let r : ℝ≥0 := ⟨(1 - (u : ℝ)) * a + (u : ℝ) * b,
    add_nonneg (mul_nonneg (sub_nonneg.mpr u.property.2) a.property)
      (mul_nonneg u.property.1 b.property)⟩
  have htime : a + q = r := by
    apply Subtype.ext
    change (a : ℝ) + (u : ℝ) * (η.toNNReal : ℝ) =
      (1 - (u : ℝ)) * a + (u : ℝ) * b
    rw [hb, NNReal.coe_add]
    ring
  change (z + ω a) + (ω (a + q) - ω a) = z + ω r
  rw [htime]
  abel

end BouRabeeGwynne
