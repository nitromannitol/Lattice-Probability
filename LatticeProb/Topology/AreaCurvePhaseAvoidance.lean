import LatticeProb.Topology.AreaCurveIntervalContainment
import LatticeProb.Topology.CompactCurveRange
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # Phase avoidance for area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

/-- For a positive mesh, a fixed shifted cell determines its phase when the
curve is parametrized by area. -/
theorem shiftedCompactCell_phase_injective_of_areaParametrized
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (η : C(ℝ, X)) (μ : Measure X)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    Function.Injective (fun θ => shiftedCompactCell η ε θ k) := by
  intro θ φ heq
  have hθ : ε * ((k : ℝ) - 1 + θ) < ε * ((k : ℝ) + θ) :=
    mul_lt_mul_of_pos_left (by linarith) hε
  have hφ : ε * ((k : ℝ) - 1 + φ) < ε * ((k : ℝ) + φ) :=
    mul_lt_mul_of_pos_left (by linarith) hε
  have hs := congrArg (fun C : NonemptyCompacts X => (C : Set X)) heq
  simp only [coe_shiftedCompactCell, uIcc_of_le hθ.le, uIcc_of_le hφ.le] at hs
  have hend := (endpoints_eq_of_area_curve_image_eq η μ η.continuous hμ hθ hφ hs).1
  nlinarith

/-- For an atomless phase law, no shifted cell belongs to a fixed countable
family of compact sets, almost surely. -/
theorem ae_shiftedCompactCell_not_mem_countable
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (η : C(ℝ, X)) (μ : Measure X)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {ε : ℝ} (hε : 0 < ε) (A : Set (NonemptyCompacts X)) (hA : A.Countable)
    (Q : Measure ℝ) [NullSingletonClass Q] :
    ∀ᵐ θ ∂Q, ∀ k : ℤ, shiftedCompactCell η ε θ k ∉ A := by
  have hc (k : ℤ) : {θ | shiftedCompactCell η ε θ k ∈ A}.Countable :=
    hA.preimage (shiftedCompactCell_phase_injective_of_areaParametrized η μ hμ hε k)
  have hz : Q (⋃ k : ℤ, {θ | shiftedCompactCell η ε θ k ∈ A}) = 0 :=
    (Set.countable_iUnion hc).measure_zero Q
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with θ hθ k
  exact fun hk => hθ (mem_iUnion.mpr ⟨k, hk⟩)

end LatticeProb
