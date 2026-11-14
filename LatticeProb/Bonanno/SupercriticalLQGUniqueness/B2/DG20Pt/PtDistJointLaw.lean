/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistJointLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law

 






set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private lemma hasLaw_dual_ker_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (k : Sum ℂ ℂ → WNSpace)
    (I : Finset (Sum ℂ ℂ)) (L : StrongDual ℝ (I → ℝ))
    {Y : Sum ℂ ℂ → Ω → ℝ}
    (hY : ∀ x, Y x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (k x) ω) :
    HasLaw (fun ω => L (fun i : I => Y i ω))
      (gaussianReal 0
        (‖∑ i : I, (Real.sqrt Real.pi * L (Pitt.unitVec i)) • k i‖ ^ 2).toNNReal) P := by
  classical
  refine (hW.hasLaw (fun i : I => k i)
    (fun i => Real.sqrt Real.pi * L (Pitt.unitVec i))).congr ?_
  have hall : ∀ᵐ ω ∂P, ∀ i : I,
      Y i ω = Real.sqrt Real.pi * W (k i) ω :=
    ae_all_iff.2 fun i => hY i
  filter_upwards [hall] with ω hω
  rw [Pitt.dual_apply_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hω i]
  ring

private lemma map_restrict_ker_sum_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (k : Sum ℂ ℂ → WNSpace)
    (T : WNSpace →ₗᵢ[ℝ] WNSpace)
    {Y Y₂ : Sum ℂ ℂ → Ω → ℝ}
    (hYm : ∀ x, Measurable (Y x)) (hY₂m : ∀ x, Measurable (Y₂ x))
    (hY : ∀ x, Y x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (k x) ω)
    (hY₂ : ∀ x, Y₂ x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (T (k x)) ω)
    (I : Finset (Sum ℂ ℂ)) :
    P.map (fun ω => I.restrict (Y · ω)) =
      P.map (fun ω => I.restrict (Y₂ · ω)) := by
  have := hW.isProbabilityMeasure
  have hm : Measurable (fun ω => I.restrict (Y · ω)) :=
    measurable_pi_iff.2 fun i => hYm i
  have hm₂ : Measurable (fun ω => I.restrict (Y₂ · ω)) :=
    measurable_pi_iff.2 fun i => hY₂m i
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map L.continuous.measurable hm,
    Measure.map_map L.continuous.measurable hm₂]
  congr 1
  have h1 := (hasLaw_dual_ker_sum hW k I L hY).map_eq
  have h2 := (hasLaw_dual_ker_sum hW (fun x => T (k x)) I L hY₂).map_eq
  have e : ∑ i : I, (Real.sqrt Real.pi * L (Pitt.unitVec i)) • T (k i) =
      T (∑ i : I, (Real.sqrt Real.pi * L (Pitt.unitVec i)) • k i) := by
    simp [map_sum, map_smul]
  rw [e, T.norm_map] at h2
  exact h1.trans h2.symm

 


theorem map_ker_sum_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (k : Sum ℂ ℂ → WNSpace)
    (T : WNSpace →ₗᵢ[ℝ] WNSpace)
    {Y Y₂ : Sum ℂ ℂ → Ω → ℝ}
    (hYm : ∀ x, Measurable (Y x)) (hY₂m : ∀ x, Measurable (Y₂ x))
    (hY : ∀ x, Y x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (k x) ω)
    (hY₂ : ∀ x, Y₂ x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (T (k x)) ω) :
    P.map (fun ω => (Y · ω)) = P.map (fun ω => (Y₂ · ω)) := by
  have := hW.isProbabilityMeasure
  have h1 := isProjectiveLimit_map (P := P) (X := Y)
    (measurable_pi_iff.2 hYm).aemeasurable
  have h2 := isProjectiveLimit_map (P := P) (X := Y₂)
    (measurable_pi_iff.2 hY₂m).aemeasurable
  have e : (fun I : Finset (Sum ℂ ℂ) =>
      P.map (fun ω => I.restrict (Y · ω))) =
      fun I => P.map (fun ω => I.restrict (Y₂ · ω)) :=
    funext fun I => map_restrict_ker_sum_eq hW k T hYm hY₂m hY hY₂ I
  rw [e] at h1
  exact h1.unique h2

 




theorem map_phiMN_pair_motion {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (n k : ℕ) (_hkn : k ≤ n)
    (u : Circle) (c : ℂ) :
    P.map (fun ω => (fun i : Sum ℂ ℂ =>
      match i with
      | .inl x => phiMN W P 0 n ((u : ℂ) * x + c) ω
      | .inr x => phiMN W P 0 k ((u : ℂ) * x + c) ω)) =
    P.map (fun ω => (fun i : Sum ℂ ℂ =>
      match i with
      | .inl x => phiMN W P 0 n x ω
      | .inr x => phiMN W P 0 k x ω)) := by
  let K : Sum ℂ ℂ → WNSpace := fun i =>
    match i with
    | .inl x => phiKernelL2 (((2 : ℝ)⁻¹) ^ n) (((2 : ℝ)⁻¹) ^ 0) x
    | .inr x => phiKernelL2 (((2 : ℝ)⁻¹) ^ k) (((2 : ℝ)⁻¹) ^ 0) x
  let Y : Sum ℂ ℂ → Ω → ℝ := fun i =>
    match i with
    | .inl x => phiMN W P 0 n x
    | .inr x => phiMN W P 0 k x
  let Y₂ : Sum ℂ ℂ → Ω → ℝ := fun i =>
    match i with
    | .inl x => phiMN W P 0 n ((u : ℂ) * x + c)
    | .inr x => phiMN W P 0 k ((u : ℂ) * x + c)
  have hn := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hk := isPhiVersion_phiMN hW (Nat.zero_le k)
  have hYm : ∀ i, Measurable (Y i) := by
    intro i
    cases i with
    | inl x => exact hn.meas x
    | inr x => exact hk.meas x
  have hY₂m : ∀ i, Measurable (Y₂ i) := by
    intro i
    cases i with
    | inl x => exact hn.meas _
    | inr x => exact hk.meas _
  have hY : ∀ i, Y i =ᵐ[P] fun ω => Real.sqrt Real.pi * W (K i) ω := by
    intro i
    cases i with
    | inl x =>
      change (fun ω => phiMN W P 0 n x ω) =ᵐ[P]
        phi W (((2 : ℝ)⁻¹) ^ n) (((2 : ℝ)⁻¹) ^ 0) x
      exact hn.ae_eq x
    | inr x =>
      change (fun ω => phiMN W P 0 k x ω) =ᵐ[P]
        phi W (((2 : ℝ)⁻¹) ^ k) (((2 : ℝ)⁻¹) ^ 0) x
      exact hk.ae_eq x
  have hY₂ : ∀ i, Y₂ i =ᵐ[P]
      fun ω => Real.sqrt Real.pi * W (motionL2 u c (K i)) ω := by
    intro i
    cases i with
    | inl x =>
      have ha : (0 : ℝ) < (((2 : ℝ)⁻¹) ^ n) := by positivity
      refine (hn.ae_eq ((u : ℂ) * x + c)).trans
        (Filter.Eventually.of_forall fun ω => ?_)
      simp only [K, phi, phiKernelL2_motion ha]
    | inr x =>
      have ha : (0 : ℝ) < (((2 : ℝ)⁻¹) ^ k) := by positivity
      refine (hk.ae_eq ((u : ℂ) * x + c)).trans
        (Filter.Eventually.of_forall fun ω => ?_)
      simp only [K, phi, phiKernelL2_motion ha]
  convert (map_ker_sum_eq hW K (motionL2 u c) hYm hY₂m hY hY₂).symm using 1
  · congr 1
    funext ω i
    cases i <;> rfl
  · congr 1
    funext ω i
    cases i <;> rfl

 

end SupercriticalLQGUniqueness.B2.DG20Pt
