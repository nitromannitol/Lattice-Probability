/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.MartingaleOccupationPairing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompensatedPotentialL2
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pairing a martingale with an adapted occupation density

This file proves the deterministic finite-horizon identity obtained by first
conditioning at each occupation time and then applying Fubini.  Adaptedness is
required only for the individual time sections of the density; the time
integral itself need not be adapted.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

/-- On an event known at time `s`, a martingale at a later time `t` can be
replaced by its value at an intermediate time `r` when multiplied by an
`F r`-measurable integrable factor. -/
theorem martingale_setIntegral_mul_eq_intermediate
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    {b : Ω → ℝ} {s r t : ι} (hsr : s ≤ r) (hrt : r ≤ t)
    (hbmeas : AEStronglyMeasurable[F r] b P)
    (hbt : Integrable (b * M t) P)
    {E : Set Ω} (hE : MeasurableSet[F s] E) :
    (∫ ω in E, M t ω * b ω ∂P) = ∫ ω in E, M r ω * b ω ∂P := by
  have hEr : MeasurableSet[F r] E := F.mono hsr E hE
  calc
    (∫ ω in E, M t ω * b ω ∂P) = ∫ ω in E, b ω * M t ω ∂P := by
      apply setIntegral_congr_fun (F.le s E hE)
      intro ω _
      exact mul_comm _ _
    _ = ∫ ω in E, P[b * M t | F r] ω ∂P :=
      (setIntegral_condExp (F.le r) hbt hEr).symm
    _ = ∫ ω in E, b ω * P[M t | F r] ω ∂P :=
      setIntegral_congr_ae (F.le r E hEr)
        ((condExp_mul_of_aestronglyMeasurable_left hbmeas hbt (hM.integrable t)).mono
          fun _ hω _ ↦ hω)
    _ = ∫ ω in E, b ω * M r ω ∂P := by
      apply setIntegral_congr_ae (F.le r E hEr)
      filter_upwards [hM.condExp_ae_eq hrt] with ω hω _
      rw [hω]
    _ = ∫ ω in E, M r ω * b ω ∂P := by
      apply setIntegral_congr_fun (F.le r E hEr)
      intro ω _
      exact mul_comm _ _

/-- Conditional Fubini identity for a real martingale and a time-dependent
adapted density on a finite `NNReal` time interval.  The explicit product
integrability assumptions are precisely those used by the two Fubini swaps.
-/
theorem martingale_setIntegral_mul_setIntegral_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    {b : ℝ → Ω → ℝ} {s t : ℝ≥0} (_hst : s ≤ t) {E : Set Ω}
    (hbmeas : ∀ r ∈ Icc (s : ℝ) (t : ℝ),
      AEStronglyMeasurable[F r.toNNReal] (b r) P)
    (hbt : ∀ r ∈ Icc (s : ℝ) (t : ℝ), Integrable (b r * M t) P)
    (hbtJoint : Integrable (Function.uncurry fun r ω ↦ M t ω * b r ω)
      ((volume.restrict (Icc (s : ℝ) (t : ℝ))).prod (P.restrict E)))
    (hbrJoint : Integrable (Function.uncurry fun r ω ↦ M r.toNNReal ω * b r ω)
      ((volume.restrict (Icc (s : ℝ) (t : ℝ))).prod (P.restrict E)))
    (hE : MeasurableSet[F s] E) :
    (∫ ω in E, M t ω *
        (∫ r : ℝ in Icc (s : ℝ) (t : ℝ), b r ω ∂volume) ∂P) =
      ∫ ω in E, (∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        M r.toNNReal ω * b r ω ∂volume) ∂P := by
  calc
    (∫ ω in E, M t ω *
        (∫ r : ℝ in Icc (s : ℝ) (t : ℝ), b r ω ∂volume) ∂P) =
        ∫ ω in E, (∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
          M t ω * b r ω ∂volume) ∂P := by
      apply setIntegral_congr_fun (F.le s E hE)
      intro ω _
      change M t ω * (∫ r : ℝ, b r ω ∂volume.restrict (Icc (s : ℝ) (t : ℝ))) =
        ∫ r : ℝ, M t ω * b r ω ∂volume.restrict (Icc (s : ℝ) (t : ℝ))
      rw [integral_const_mul]
    _ = ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        (∫ ω in E, M t ω * b r ω ∂P) ∂volume :=
      (integral_integral_swap hbtJoint).symm
    _ = ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        (∫ ω in E, M r.toNNReal ω * b r ω ∂P) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      have hrnonneg : 0 ≤ r := (NNReal.zero_le_coe.trans hr.1)
      have hsr : s ≤ r.toNNReal := by
        apply NNReal.coe_le_coe.mp
        simpa [Real.coe_toNNReal r hrnonneg] using hr.1
      have hrt : r.toNNReal ≤ t := by
        apply NNReal.coe_le_coe.mp
        simpa [Real.coe_toNNReal r hrnonneg] using hr.2
      exact martingale_setIntegral_mul_eq_intermediate hM hsr hrt
        (hbmeas r hr) (by simpa [mul_comm] using hbt r hr) hE
    _ = ∫ ω in E, (∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        M r.toNNReal ω * b r ω ∂volume) ∂P :=
      integral_integral_swap hbrJoint

/-- Bounded finite-horizon form of
`martingale_setIntegral_mul_setIntegral_eq`.  Joint measurability and uniform
bounds of the two product integrands supply exactly the product integrability
needed for Fubini. -/
theorem martingale_setIntegral_mul_setIntegral_eq_of_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    {b : ℝ → Ω → ℝ} {s t : ℝ≥0} (hst : s ≤ t) {E : Set Ω}
    (hbmeas : ∀ r ∈ Icc (s : ℝ) (t : ℝ),
      AEStronglyMeasurable[F r.toNNReal] (b r) P)
    (hbtJointMeas : AEStronglyMeasurable
      (Function.uncurry fun r ω ↦ M t ω * b r ω)
      ((volume.restrict (Icc (s : ℝ) (t : ℝ))).prod (P.restrict E)))
    (hbrJointMeas : AEStronglyMeasurable
      (Function.uncurry fun r ω ↦ M r.toNNReal ω * b r ω)
      ((volume.restrict (Icc (s : ℝ) (t : ℝ))).prod (P.restrict E)))
    {Ct Cr : ℝ}
    (hbtSectionBound : ∀ r ∈ Icc (s : ℝ) (t : ℝ),
      ∀ᵐ ω ∂P, ‖b r ω * M t ω‖ ≤ Ct)
    (hbtBound : ∀ᵐ z ∂((volume.restrict (Icc (s : ℝ) (t : ℝ))).prod
      (P.restrict E)), ‖M t z.2 * b z.1 z.2‖ ≤ Ct)
    (hbrBound : ∀ᵐ z ∂((volume.restrict (Icc (s : ℝ) (t : ℝ))).prod
      (P.restrict E)), ‖M z.1.toNNReal z.2 * b z.1 z.2‖ ≤ Cr)
    (hE : MeasurableSet[F s] E) :
    (∫ ω in E, M t ω *
        (∫ r : ℝ in Icc (s : ℝ) (t : ℝ), b r ω ∂volume) ∂P) =
      ∫ ω in E, (∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        M r.toNNReal ω * b r ω ∂volume) ∂P := by
  have hbt : ∀ r ∈ Icc (s : ℝ) (t : ℝ), Integrable (b r * M t) P := by
    intro r hr
    apply Integrable.of_bound
      (((hbmeas r hr).mono (F.le r.toNNReal)).mul
        ((hM.stronglyMeasurable t).mono (F.le t)).aestronglyMeasurable)
      Ct (hbtSectionBound r hr)
  apply martingale_setIntegral_mul_setIntegral_eq hM hst hbmeas hbt
    (Integrable.of_bound hbtJointMeas Ct hbtBound)
    (Integrable.of_bound hbrJointMeas Cr hbrBound) hE

end ReflectedGMS
