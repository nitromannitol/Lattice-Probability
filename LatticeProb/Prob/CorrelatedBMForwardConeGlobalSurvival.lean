import LatticeProb.Prob.CorrelatedBMForwardConeGlobalDimension
import LatticeProb.Prob.CorrelatedBMForwardConeUnseparatedDimension
import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.TransferScaling

/-! # Global forward cone-vector dimension from a survival estimate -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel

namespace LatticeProb.CorrelatedBM

/-- A joint survival estimate controls the global forward cone-vector dimension
simultaneously in both time orientations. -/
theorem ae_dimH_forwardConeVectors_le_of_joint_survival
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (α β : ℝ≥0) (hα : (α : ℝ) < 1 / 2) (hβ : 0 < β)
    (C p : ℝ) (hC : 0 < C)
    (hslack : 2 < (β : ℝ) + (α : ℝ) * (p + 2))
    (hJ : ∀ h : ℝ, 0 < h → ∃ B : ℝ, 0 ≤ B ∧
      ∀ (n : ℕ) (ν : Measure Path2), IsCorrelatedBM2 γ ν →
        ν (jointZeroBarrier (C * (factorialGridMesh n) ^ (α : ℝ)) h) ≤
          ENNReal.ofReal (B * (C * (factorialGridMesh n) ^ (α : ℝ)) ^ p)) :
    ∀ᵐ ω ∂μ, ∀ e : ℝ, (e = 1 ∨ e = -1) →
      dimH (forwardConeVectors (fun t => lrCoord 0 (e * t) ω)
        (fun t => lrCoord 1 (e * t) ω)) ≤ β := by
  apply ae_dimH_forwardConeVectors_le_of_normalized_intervals hμ β
  have hfixed (n : ℕ) (e : ℝ) (he : e = 1 ∨ e = -1) :
      ∀ᵐ ω ∂μ,
        let r : ℝ := (n : ℝ) + 1
        let X : ℝ → ℝ := fun t => lrCoord 0 (e * t) ω
        let Y : ℝ → ℝ := fun t => lrCoord 1 (e * t) ω
        dimH {z : ℝ × ℝ | z ∈ forwardConeVectors
          (fun t => (Real.sqrt (r - -r))⁻¹ * (X (r + (r - -r) * t) - X r))
          (fun t => (Real.sqrt (r - -r))⁻¹ * (Y (r + (r - -r) * t) - Y r)) ∧
          -1 < z.2 ∧ z.1 < 0} ≤ β := by
    let r : ℝ := (n : ℝ) + 1
    let a : ℝ := r - -r
    have ha : 0 < a := by
      dsimp [a, r]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have heabs : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
    let ν := μ.map (recenterPath (e * r) e)
    have hν : IsCorrelatedBM2 γ ν := isCorrelatedBM2_map_recenterPath hμ _ _ heabs
    have hscale := isCorrelatedBM2_map_unitRescalePath ha hν
    have hunit := ae_dimH_neg_unit_forwardConeVectors_le_of_joint_survival
      hscale α β hα hβ C p 1 hC (Or.inl rfl) hslack hJ
    have hpull := ae_of_ae_map (measurable_unitRescalePath a).aemeasurable hunit
    have hpull' := ae_of_ae_map (continuous_recenterPath (e * r) e).measurable.aemeasurable hpull
    filter_upwards [hpull'] with ω hω
    have hcoord (i : Fin 2) (t : ℝ) :
        lrCoord i (1 * t) (unitRescalePath a (recenterPath (e * r) e ω)) =
          (Real.sqrt a)⁻¹ * (lrCoord i (e * (r + a * t)) ω - lrCoord i (e * r) ω) := by
      rw [lrCoord_unitRescalePath, one_mul]
      have hf : lrCoord i (a * t) (recenterPath (e * r) e ω) =
          lrCoord i (e * r + e * (a * t)) ω - lrCoord i (e * r) ω := by
        fin_cases i <;> rfl
      rw [hf]
      rw [show e * r + e * (a * t) = e * (r + a * t) by ring]
    simpa only [hcoord] using hω
  have hpos := ae_all_iff.2 (fun n => hfixed n 1 (Or.inl rfl))
  have hneg := ae_all_iff.2 (fun n => hfixed n (-1) (Or.inr rfl))
  filter_upwards [hpos, hneg] with ω hp hn
  intro n e he
  rcases he with rfl | rfl
  · exact hp n
  · exact hn n

end LatticeProb.CorrelatedBM
