/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBXbigLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBJointLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBGaussianError
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BXMom

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

private theorem laneB_Xbig_ae_eq_dense
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Q : PsiParams) (D : Set ((rectAB 5 5).toSet)) [Countable D]
    (hD : Dense D) :
    (fun ω => XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5) =ᵐ[P]
    fun ω => ⨆ n : ℕ, ⨆ d : D,
      ENNReal.ofReal |Real.sqrt Real.pi *
        W (phiKernelL2 ((2 : ℝ)⁻¹ ^ n) 1
          ((d : (rectAB 5 5).toSet) + T20C.cBig)) ω -
        Real.sqrt Real.pi *
        W (Q.psiKernelL2 ((2 : ℝ)⁻¹ ^ n) 1
          ((d : (rectAB 5 5).toSet) + T20C.cBig)) ω| := by
  have hφ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ d : D,
      phiMN W P 0 n ((d : (rectAB 5 5).toSet) + T20C.cBig) ω =
        Real.sqrt Real.pi *
          W (phiKernelL2 ((2 : ℝ)⁻¹ ^ n) 1
            ((d : (rectAB 5 5).toSet) + T20C.cBig)) ω := by
    refine ae_all_iff.mpr fun n => ae_all_iff.mpr fun d => ?_
    exact (isPhiVersion_phiMN hW (Nat.zero_le n)).ae_eq
      ((d : (rectAB 5 5).toSet) + T20C.cBig)
  have hψ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ d : D,
      psiMN Q W P 0 n ((d : (rectAB 5 5).toSet) + T20C.cBig) ω =
        Real.sqrt Real.pi *
          W (Q.psiKernelL2 ((2 : ℝ)⁻¹ ^ n) 1
            ((d : (rectAB 5 5).toSet) + T20C.cBig)) ω := by
    refine ae_all_iff.mpr fun n => ae_all_iff.mpr fun d => ?_
    exact (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).ae_eq
      ((d : (rectAB 5 5).toSet) + T20C.cBig)
  filter_upwards [hφ, hψ] with ω heφ heψ
  unfold XAB
  apply iSup_congr
  intro n
  have hcont : Continuous fun y : ℂ =>
      ENNReal.ofReal |phiMN W P 0 n (y + T20C.cBig) ω -
        psiMN Q W P 0 n (y + T20C.cBig) ω| :=
    ENNReal.continuous_ofReal.comp <| continuous_abs.comp <|
      (((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω).comp
        (continuous_id.add continuous_const)).sub
      (((isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).cont ω).comp
        (continuous_id.add continuous_const))
  rw [T20B.biSup_eq_iSup_dense hD hcont]
  apply iSup_congr
  intro d
  rw [heφ n d, heψ n d]

 


theorem laneB_Xbig_tail_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (W : WNSpace → Ω → ℝ) (V : WNSpace → Ω' → ℝ)
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P' V)
    (Q : PsiParams) (x : ℝ) :
    P {ω | ENNReal.ofReal x ≤
      XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
        (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5} =
    P' {ω | ENNReal.ofReal x ≤
      XAB (fun n y => phiMN V P' 0 n (y + T20C.cBig) ω)
        (fun n y => psiMN Q V P' 0 n (y + T20C.cBig) ω) 5 5} := by
  let S : Set ℂ := (rectAB 5 5).toSet
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense S
  letI : Countable D := hDc.to_subtype
  let F : (WNSpace → ℝ) → ℝ≥0∞ := fun w =>
    ⨆ n : ℕ, ⨆ d : D,
      ENNReal.ofReal |Real.sqrt Real.pi *
        w (phiKernelL2 ((2 : ℝ)⁻¹ ^ n) 1 ((d : S) + T20C.cBig)) -
        Real.sqrt Real.pi *
        w (Q.psiKernelL2 ((2 : ℝ)⁻¹ ^ n) 1 ((d : S) + T20C.cBig))|
  have hF : Measurable F := by
    apply Measurable.iSup
    intro n
    apply Measurable.iSup
    intro d
    have hmφ : Measurable (fun w : WNSpace → ℝ =>
        w (phiKernelL2 ((2 : ℝ)⁻¹ ^ n) 1 ((d : S) + T20C.cBig))) :=
      measurable_pi_apply _
    have hmψ : Measurable (fun w : WNSpace → ℝ =>
        w (Q.psiKernelL2 ((2 : ℝ)⁻¹ ^ n) 1 ((d : S) + T20C.cBig))) :=
      measurable_pi_apply _
    exact ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp
        ((hmφ.const_mul _).sub (hmψ.const_mul _)))
  have hFmap : P.map (fun ω => F (fun f => W f ω)) =
      P'.map (fun ω => F (fun f => V f ω)) := by
    calc
      P.map (fun ω => F (fun f => W f ω)) =
          (P.map (fun ω f => W f ω)).map F := by
        rw [Measure.map_map hF (measurable_pi_iff.mpr hW.measurable)]
        rfl
      _ = (P'.map (fun ω f => V f ω)).map F := by
        rw [laneB_map_whiteNoise_eq P P' W V hW hV]
      _ = P'.map (fun ω => F (fun f => V f ω)) := by
        rw [Measure.map_map hF (measurable_pi_iff.mpr hV.measurable)]
        rfl
  have hset : MeasurableSet {r : ℝ≥0∞ | ENNReal.ofReal x ≤ r} :=
    measurableSet_Ici
  have hEventW :
      {ω | ENNReal.ofReal x ≤
        XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
          (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5} =ᵐ[P]
      {ω | ENNReal.ofReal x ≤ F (fun f => W f ω)} := by
    filter_upwards [laneB_Xbig_ae_eq_dense P W hW Q D hD] with ω hω
    simp only [hω]
    rfl
  have hEventV :
      {ω | ENNReal.ofReal x ≤
        XAB (fun n y => phiMN V P' 0 n (y + T20C.cBig) ω)
          (fun n y => psiMN Q V P' 0 n (y + T20C.cBig) ω) 5 5} =ᵐ[P']
      {ω | ENNReal.ofReal x ≤ F (fun f => V f ω)} := by
    filter_upwards [laneB_Xbig_ae_eq_dense P' V hV Q D hD] with ω hω
    simp only [hω]
    rfl
  calc
    P _ = P {ω | ENNReal.ofReal x ≤ F (fun f => W f ω)} :=
      measure_congr hEventW
    _ = (P.map (fun ω => F (fun f => W f ω))) {r | ENNReal.ofReal x ≤ r} :=
      (Measure.map_apply (hF.comp (measurable_pi_iff.mpr hW.measurable)) hset).symm
    _ = (P'.map (fun ω => F (fun f => V f ω))) {r | ENNReal.ofReal x ≤ r} := by rw [hFmap]
    _ = P' {ω | ENNReal.ofReal x ≤ F (fun f => V f ω)} :=
      Measure.map_apply (hF.comp (measurable_pi_iff.mpr hV.measurable)) hset
    _ = P' _ := measure_congr hEventV.symm

end SupercriticalLQGUniqueness.B2.DG20Conc
