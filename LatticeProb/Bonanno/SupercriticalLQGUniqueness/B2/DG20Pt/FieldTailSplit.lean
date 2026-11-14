/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.FieldTailSplit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.FieldDecomposition
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.BandTailLaw

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem measure_full_crossing_lt_split
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (ξ : ℝ) (U : Opens ℂ) (A B : Set ℂ)
    {k n : ℕ} (hkn : k ≤ n) (δ : ℝ) (a : ℝ≥0∞) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ k
    let F : ℂ → ℂ := fun z => (r : ℂ) * z
    P {ω | ENNReal.ofReal (Real.exp (|ξ| * δ)) *
      crossLenIn ξ (fun z => phiMN W P 0 n z ω) (F '' U) (F '' A) (F '' B) <
        ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k 0 ω)) *
          (ENNReal.ofReal r * a)} ≤
      P {ω | ∃ z ∈ F '' U,
        δ < |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} +
      P {ω | crossLenIn ξ (fun z => phiMN W P 0 (n - k) z ω) U A B < a} := by
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  let F : ℂ → ℂ := fun z => (r : ℂ) * z
  let Osc : Set Ω := {ω | ∃ z ∈ F '' U,
    δ < |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|}
  let Band : Set Ω := {ω | crossLenIn ξ (fun z => phiMN W P k n z ω)
    (F '' U) (F '' A) (F '' B) < ENNReal.ofReal r * a}
  have hsub : {ω | ENNReal.ofReal (Real.exp (|ξ| * δ)) *
      crossLenIn ξ (fun z => phiMN W P 0 n z ω) (F '' U) (F '' A) (F '' B) <
        ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k 0 ω)) *
          (ENNReal.ofReal r * a)} ≤ᵐ[P] Osc ∪ Band := by
    filter_upwards [ae_crossLenIn_band_compare_center P W hW ξ δ
      (F '' U) (F '' A) (F '' B) hkn] with ω hcomp hω
    by_cases hosc : ω ∈ Osc
    · exact Or.inl hosc
    · right
      by_contra hnot
      have hgood : ∀ z ∈ F '' U,
          |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω| ≤ δ := by
        intro z hz
        exact le_of_not_gt (fun h => hosc ⟨z, hz, h⟩)
      have hband : ENNReal.ofReal r * a ≤
          crossLenIn ξ (fun z => phiMN W P k n z ω)
            (F '' U) (F '' A) (F '' B) := le_of_not_gt hnot
      have hmul : ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k 0 ω)) *
          (ENNReal.ofReal r * a) ≤
          ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k 0 ω)) *
            crossLenIn ξ (fun z => phiMN W P k n z ω)
              (F '' U) (F '' A) (F '' B) := by gcongr
      exact (not_lt_of_ge (hmul.trans (hcomp hgood).2)) hω
  calc
    _ ≤ P (Osc ∪ Band) := measure_mono_ae hsub
    _ ≤ P Osc + P Band := measure_union_le _ _
    _ = P Osc +
        P {ω | crossLenIn ξ (fun z => phiMN W P 0 (n - k) z ω) U A B < a} := by
      rw [measure_band_crossing_open_lt P W hW ξ U A B hkn a]

 


theorem measure_full_crossing_gt_split
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (ξ : ℝ) (U : Opens ℂ) (A B : Set ℂ)
    {k n : ℕ} (hkn : k ≤ n) (δ : ℝ) (a : ℝ≥0∞) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ k
    let F : ℂ → ℂ := fun z => (r : ℂ) * z
    P {ω | ENNReal.ofReal (Real.exp (|ξ| * δ)) *
      (ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k 0 ω)) *
          (ENNReal.ofReal r * a)) <
      crossLenIn ξ (fun z => phiMN W P 0 n z ω) (F '' U) (F '' A) (F '' B)} ≤
      P {ω | ∃ z ∈ F '' U,
        δ < |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} +
      P {ω | a < crossLenIn ξ (fun z => phiMN W P 0 (n - k) z ω) U A B} := by
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  let F : ℂ → ℂ := fun z => (r : ℂ) * z
  let Osc : Set Ω := {ω | ∃ z ∈ F '' U,
    δ < |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|}
  let Band : Set Ω := {ω | ENNReal.ofReal r * a <
    crossLenIn ξ (fun z => phiMN W P k n z ω) (F '' U) (F '' A) (F '' B)}
  have hsub : {ω | ENNReal.ofReal (Real.exp (|ξ| * δ)) *
      (ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k 0 ω)) *
          (ENNReal.ofReal r * a)) <
      crossLenIn ξ (fun z => phiMN W P 0 n z ω) (F '' U) (F '' A) (F '' B)} ≤ᵐ[P]
      Osc ∪ Band := by
    filter_upwards [ae_crossLenIn_band_compare_center P W hW ξ δ
      (F '' U) (F '' A) (F '' B) hkn] with ω hcomp hω
    by_cases hosc : ω ∈ Osc
    · exact Or.inl hosc
    · right
      by_contra hnot
      have hgood : ∀ z ∈ F '' U,
          |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω| ≤ δ := by
        intro z hz
        exact le_of_not_gt (fun h => hosc ⟨z, hz, h⟩)
      have hband : crossLenIn ξ (fun z => phiMN W P k n z ω)
          (F '' U) (F '' A) (F '' B) ≤ ENNReal.ofReal r * a := le_of_not_gt hnot
      have hmul : ENNReal.ofReal (Real.exp (|ξ| * δ)) *
          (ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k 0 ω)) *
            crossLenIn ξ (fun z => phiMN W P k n z ω)
              (F '' U) (F '' A) (F '' B)) ≤
          ENNReal.ofReal (Real.exp (|ξ| * δ)) *
            (ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k 0 ω)) *
              (ENNReal.ofReal r * a)) := by gcongr
      exact (not_lt_of_ge ((hcomp hgood).1.trans hmul)) hω
  calc
    _ ≤ P (Osc ∪ Band) := measure_mono_ae hsub
    _ ≤ P Osc + P Band := measure_union_le _ _
    _ = P Osc +
        P {ω | a < crossLenIn ξ (fun z => phiMN W P 0 (n - k) z ω) U A B} := by
      rw [measure_band_crossing_open_gt P W hW ξ U A B hkn a]

end SupercriticalLQGUniqueness.B2.DG20Pt
