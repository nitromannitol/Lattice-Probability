import LatticeProb.Prob.CorrelatedBMConeVectorAffineDimension
import LatticeProb.Prob.CorrelatedBMConeUnseparatedDimension
import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.TransferScaling

/-! # Global backward cone-vector dimension from a survival estimate -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel

namespace LatticeProb.CorrelatedBM

/-- A joint survival estimate bounds the global backward cone-vector dimension
simultaneously in both time orientations. -/
theorem ae_dimH_backwardConeVectors_global_le_of_joint_survival
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (α β : ℝ≥0) (hα : (α : ℝ) < 1 / 2) (hβ : 0 < β)
    (C p : ℝ) (hC : 0 < C)
    (hslack : 2 < (β : ℝ) + (α : ℝ) * (p + 2))
    (hJ : ∀ h : ℝ, 0 < h → ∃ B : ℝ, 0 ≤ B ∧
      ∀ (n : ℕ) (ν : Measure Path2), IsCorrelatedBM2 γ ν →
        ν (jointZeroBarrier (C * (factorialGridMesh n) ^ (α : ℝ)) h) ≤
          ENNReal.ofReal (B * (C * (factorialGridMesh n) ^ (α : ℝ)) ^ p)) :
    ∀ᵐ ω ∂μ, ∀ e : ℝ, (e = 1 ∨ e = -1) →
      dimH (backwardConeVectors (fun t => lrCoord 0 (e * t) ω)
        (fun t => lrCoord 1 (e * t) ω)) ≤ β := by
  have hfixed (n : ℕ) (e : ℝ) (he : e = 1 ∨ e = -1) :
      ∀ᵐ ω ∂μ,
        let r : ℝ := (n : ℝ) + 1
        let X : ℝ → ℝ := fun t => lrCoord 0 (e * t) ω
        let Y : ℝ → ℝ := fun t => lrCoord 1 (e * t) ω
        dimH {z : ℝ × ℝ | z ∈ backwardConeVectors
          (fun t => (Real.sqrt (r - -r))⁻¹ * (X (-r + (r - -r) * t) - X (-r)))
          (fun t => (Real.sqrt (r - -r))⁻¹ * (Y (-r + (r - -r) * t) - Y (-r))) ∧
          0 < z.1 ∧ z.2 < 1} ≤ β := by
    let r : ℝ := (n : ℝ) + 1
    let a : ℝ := r - -r
    have ha : 0 < a := by
      dsimp [a, r]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have heabs : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
    let ν := μ.map (recenterPath (e * -r) e)
    have hν : IsCorrelatedBM2 γ ν := isCorrelatedBM2_map_recenterPath hμ _ _ heabs
    have hscale := isCorrelatedBM2_map_unitRescalePath ha hν
    have hunit := ae_dimH_unit_backwardConeVectors_le_of_joint_survival
      hscale α β hα hβ C p 1 hC (Or.inl rfl) hslack hJ
    have hpull := ae_of_ae_map (measurable_unitRescalePath a).aemeasurable hunit
    have hpull' := ae_of_ae_map (continuous_recenterPath (e * -r) e).measurable.aemeasurable hpull
    filter_upwards [hpull'] with ω hω
    have hcoord (i : Fin 2) (t : ℝ) :
        lrCoord i (1 * t) (unitRescalePath a (recenterPath (e * -r) e ω)) =
          (Real.sqrt a)⁻¹ * (lrCoord i (e * (-r + a * t)) ω - lrCoord i (e * -r) ω) := by
      rw [lrCoord_unitRescalePath, one_mul]
      have hf : lrCoord i (a * t) (recenterPath (e * -r) e ω) =
          lrCoord i (e * -r + e * (a * t)) ω - lrCoord i (e * -r) ω := by
        fin_cases i <;> rfl
      rw [hf]
      rw [show e * -r + e * (a * t) = e * (-r + a * t) by ring]
    simpa only [hcoord] using hω
  have hpos := ae_all_iff.2 (fun n => hfixed n 1 (Or.inl rfl))
  have hneg := ae_all_iff.2 (fun n => hfixed n (-1) (Or.inr rfl))
  have hbound : ∀ᵐ ω ∂μ, ∀ (n : ℕ) (e : ℝ), (e = 1 ∨ e = -1) →
      let r : ℝ := (n : ℝ) + 1
      let X : ℝ → ℝ := fun t => lrCoord 0 (e * t) ω
      let Y : ℝ → ℝ := fun t => lrCoord 1 (e * t) ω
      dimH {z : ℝ × ℝ | z ∈ backwardConeVectors
        (fun t => (Real.sqrt (r - -r))⁻¹ * (X (-r + (r - -r) * t) - X (-r)))
        (fun t => (Real.sqrt (r - -r))⁻¹ * (Y (-r + (r - -r) * t) - Y (-r))) ∧
        0 < z.1 ∧ z.2 < 1} ≤ β := by
    filter_upwards [hpos, hneg] with ω hp hn
    intro n e he
    rcases he with rfl | rfl
    · exact hp n
    · exact hn n
  filter_upwards [ae_dimH_backwardConeVectors_interval_le_sqrt_rescale hμ, hbound] with ω ht hboundω
  intro e he
  let S := backwardConeVectors (fun t => lrCoord 0 (e * t) ω)
    (fun t => lrCoord 1 (e * t) ω)
  let T : ℕ → Set (ℝ × ℝ) := fun n => {z | z ∈ S ∧ -((n : ℝ) + 1) < z.1 ∧ z.2 < (n : ℝ) + 1}
  have hT (n : ℕ) : dimH (T n) ≤ β := by
    have hr : -((n : ℝ) + 1) < (n : ℝ) + 1 := by
      have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hb := ht e (-((n : ℝ) + 1)) ((n : ℝ) + 1) he hr
    exact hb.trans (hboundω n e he)
  have hcover : S ⊆ ⋃ n, T n := by
    intro z hz
    obtain ⟨n, hn'⟩ := exists_nat_gt (max (-z.1) z.2)
    refine mem_iUnion.mpr ⟨n, hz, ?_, ?_⟩
    · linarith [le_max_left (-z.1) z.2]
    · linarith [le_max_right (-z.1) z.2]
  calc
    dimH S ≤ dimH (⋃ n, T n) := dimH_mono hcover
    _ = ⨆ n, dimH (T n) := dimH_iUnion _
    _ ≤ β := iSup_le hT

end LatticeProb.CorrelatedBM
