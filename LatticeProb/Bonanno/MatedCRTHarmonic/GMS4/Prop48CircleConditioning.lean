/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CircleConditioning at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48ExteriorLocal
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_19CI

/-!
# Conditional expectations under equivalent circle-average observations

The affine version of Appendix A.3 conditions on a `Fin 2` family of circle
averages; the source conditions on an ordinary pair. Their observations agree
almost surely and generate the same completed sigma algebra.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter LQGMetric LQGMetric.GM.Bilip

namespace MatedCRTHarmonic.GMS4

/-- Conditional expectations agree almost surely if their Borel observations
agree almost surely, even though their raw comap sigma algebras need not be
equal on null sets. -/
theorem prop48_condExp_comap_ae_eq
    {Ω : Type} {β : Type*} [m₀ : MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {A B : Ω → β} (hA : Measurable A) (hB : Measurable B)
    (hAB : A =ᵐ[P] B) {Y : Ω → ℝ} (hY : Integrable Y P) :
    P[Y | MeasurableSpace.comap A inferInstance] =ᵐ[P]
      P[Y | MeasurableSpace.comap B inferInstance] := by
  have hmA : MeasurableSpace.comap A inferInstance ≤ m₀ := hA.comap_le
  have hmB : MeasurableSpace.comap B inferInstance ≤ m₀ := hB.comap_le
  have hABle : MeasurableSpace.comap A inferInstance ≤
      aeClosure P (MeasurableSpace.comap B inferInstance) :=
    LQGMetric.DFGPS.L219.comap_le_aeClosure_of_ae_eq (comap_measurable B) hAB
  have hBAle : MeasurableSpace.comap B inferInstance ≤
      aeClosure P (MeasurableSpace.comap A inferInstance) :=
    LQGMetric.DFGPS.L219.comap_le_aeClosure_of_ae_eq (comap_measurable A) hAB.symm
  have hJA : P[Y | MeasurableSpace.comap A inferInstance ⊔
      MeasurableSpace.comap B inferInstance] =ᵐ[P]
      P[Y | MeasurableSpace.comap A inferInstance] :=
    LQGMetric.DFGPS.L219.condExp_sandwich le_sup_left (sup_le hmA hmB) hmA
      (sup_le (le_aeClosure _) hBAle) hY EventuallyEq.rfl
  have hJB : P[Y | MeasurableSpace.comap A inferInstance ⊔
      MeasurableSpace.comap B inferInstance] =ᵐ[P]
      P[Y | MeasurableSpace.comap B inferInstance] :=
    LQGMetric.DFGPS.L219.condExp_sandwich le_sup_right (sup_le hmA hmB) hmB
      (sup_le hABle (le_aeClosure _)) hY EventuallyEq.rfl
  exact hJA.symm.trans hJB

/-- The ordinary pair and the `Fin 2` tuple of two real observations generate
The same sigma algebra. -/
theorem prop48_pairSigma_eq_fin2Sigma
    {Ω : Type*} [MeasurableSpace Ω] (a b : Ω → ℝ) :
    MeasurableSpace.comap (fun ω => (a ω, b ω)) inferInstance =
      MeasurableSpace.comap (fun ω => (fun i : Fin 2 => if i = 0 then a ω else b ω))
        inferInstance := by
  apply le_antisymm
  · have hf : Measurable (fun x : Fin 2 → ℝ => (x 0, x 1)) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    have htuple : Measurable[MeasurableSpace.comap
        (fun ω => (fun i : Fin 2 => if i = 0 then a ω else b ω)) inferInstance]
        (fun ω => (a ω, b ω)) := by
      simpa only [Function.comp_def, ite_true,
        show (1 : Fin 2) ≠ 0 by decide, ite_false] using
        hf.comp (comap_measurable
          (fun ω => (fun i : Fin 2 => if i = 0 then a ω else b ω)))
    exact htuple.comap_le
  · have hg : Measurable (fun x : ℝ × ℝ => (fun i : Fin 2 =>
        if i = 0 then x.1 else x.2)) := by
      refine measurable_pi_iff.2 fun i => ?_
      fin_cases i
      · exact measurable_fst
      · simpa using (measurable_snd : Measurable (fun x : ℝ × ℝ => x.2))
    have hpair : Measurable[MeasurableSpace.comap (fun ω => (a ω, b ω)) inferInstance]
        (fun ω => (fun i : Fin 2 => if i = 0 then a ω else b ω)) := by
      simpa only [Function.comp_def] using
        hg.comp (comap_measurable (fun ω => (a ω, b ω)))
    exact hpair.comap_le

/-- The translated A.3 conditional mean and the source circle-average
conditional mean coincide almost surely. -/
theorem prop48_affine_condExp_eq_source_circle_condExp
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hIG : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (hhIG : IsNormalizedWPGFF hIG P)
    {r : ℝ} (hr : 0 < r) (z : ℂ)
    {Y : Ω → ℝ} (hY : Integrable Y P) :
    P[Y | GMSAppA.cSigmaN (prop48AffineFieldFamily h hIG r z)] =ᵐ[P]
      P[Y | MeasurableSpace.comap
        (prop48CircleAverageObservation h hIG r z) inferInstance] := by
  let A : Ω → Fin 2 → ℝ := fun ω i =>
    circleAvg (prop48AffineFieldFamily h hIG r z i ω) 1 0
  let B : Ω → Fin 2 → ℝ := fun ω i =>
    if i = 0 then circleAvg (h ω) r z else circleAvg (hIG ω) r z
  have hA : Measurable A := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · change Measurable (fun ω => circleAvg (affineComp r z (h ω)) 1 0)
      exact (measurable_circleAvg_left 1 0).comp
        ((measurable_affineComp r z).comp hh.1.measurable)
    · change Measurable (fun ω => circleAvg (affineComp r z (hIG ω)) 1 0)
      exact (measurable_circleAvg_left 1 0).comp
        ((measurable_affineComp r z).comp hhIG.1.measurable)
  have hB : Measurable B := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact (measurable_circleAvg_left r z).comp hh.1.measurable
    · change Measurable (fun ω => circleAvg (hIG ω) r z)
      exact (measurable_circleAvg_left r z).comp hhIG.1.measurable
  have hAB : A =ᵐ[P] B := prop48_affine_circleAverages_ae hh hhIG hr z
  have hCE := prop48_condExp_comap_ae_eq hA hB hAB hY
  change P[Y | GMSAppA.cSigmaN (prop48AffineFieldFamily h hIG r z)] =ᵐ[P]
    P[Y | MeasurableSpace.comap B inferInstance] at hCE
  rwa [show MeasurableSpace.comap B inferInstance =
      MeasurableSpace.comap (prop48CircleAverageObservation h hIG r z) inferInstance
      from (prop48_pairSigma_eq_fin2Sigma
        (fun ω => circleAvg (h ω) r z)
        (fun ω => circleAvg (hIG ω) r z)).symm] at hCE

end MatedCRTHarmonic.GMS4

