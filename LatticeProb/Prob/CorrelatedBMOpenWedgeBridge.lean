import LatticeProb.Prob.CorrelatedBMSymmetricWedge

/-! # Open and closed symmetric wedge barriers -/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A continuous path remains in the open symmetric wedge on a time interval. -/
def openSymmetricWedgeBarrier (a b q h : ℝ) : Set Path2 :=
  {ω | ∀ t ∈ Icc 0 h,
    |b * coneIncr 1 t 0 ω| < q + a * coneIncr 0 t 0 ω}

/-- Expanding the wedge by a positive amount includes its closed barrier in
its open barrier, including at the endpoints of the time interval. -/
theorem symmetricWedgeBarrier_subset_open (a b q h δ : ℝ) (hδ : 0 < δ) :
    symmetricWedgeBarrier a b q h ⊆ openSymmetricWedgeBarrier a b (q + δ) h := by
  intro ω hω t ht
  have ht' := hω t ht
  change |b * coneIncr 1 t 0 ω| < (q + δ) + a * coneIncr 0 t 0 ω
  linarith

/-- An open wedge estimate controls the correlated joint barrier after
whitening and a positive enlargement of the wedge. -/
theorem measure_jointZeroBarrier_le_open_wedge {γ : ℝ} {μ : Measure Path2}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (q h δ : ℝ) (hδ : 0 < δ) :
    μ (jointZeroBarrier q h) ≤
      (μ.map (whitenAt γ 0)) (openSymmetricWedgeBarrier
        (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2)
        (Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2) (q + δ) h) := by
  rw [measure_jointZeroBarrier_eq_symmetricWedge hγ0 hγ2 q h]
  exact measure_mono (symmetricWedgeBarrier_subset_open _ _ _ _ _ hδ)

/-- A power estimate for the open wedge along its symmetry axis transfers to
closed correlated barriers, with the starting distance doubled. -/
theorem measure_jointZeroBarrier_le_of_open_wedge_power {γ : ℝ} {μ : Measure Path2}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (q h B p : ℝ) (hq : 0 < q)
    (hopen : (μ.map (whitenAt γ 0)) (openSymmetricWedgeBarrier
        (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2)
        (Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2) (2 * q) h) ≤
      ENNReal.ofReal (B * (2 * q) ^ p)) :
    μ (jointZeroBarrier q h) ≤ ENNReal.ofReal ((B * 2 ^ p) * q ^ p) := by
  have hbound := measure_jointZeroBarrier_le_open_wedge (μ := μ) hγ0 hγ2 q h q hq
  have htwo : q + q = 2 * q := by ring
  rw [htwo] at hbound
  calc
    μ (jointZeroBarrier q h) ≤ _ := hbound
    _ ≤ ENNReal.ofReal (B * (2 * q) ^ p) := hopen
    _ = ENNReal.ofReal ((B * 2 ^ p) * q ^ p) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hq.le]
      congr 1
      ring

end LatticeProb.CorrelatedBM
