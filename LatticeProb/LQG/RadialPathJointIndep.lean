import LatticeProb.LQG.RadialPairingsJointIndep
import LatticeProb.LQG.RadialPairingCircleLimit
import LatticeProb.LQG.RadialVersionIntegrability

/-! # Joint independence of the radial path and lateral field -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.GMCFacts
  MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- A field-measurable continuous centered radial version is independent of the
lateral field jointly with any random element independent of the whole field. -/
theorem IsWholePlaneGFF.indepFun_radialPath_lateralPart_prodMk
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {δ : Type*} [MeasurableSpace δ] {Z : Ω → δ} (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) :
    IndepFun (fun ω => R (X ω)) (fun ω => (lateralPartC (X ω), Z ω)) P := by
  have := hX.gaussian.isProbabilityMeasure
  let ψ : ℝ × ℕ → TestC0 := fun p => circDiff p.2 0 (Real.exp (-p.1)) p.2 0 1
  let A : Ω → (ℝ × ℕ → ℝ) := fun ω p => pairW (symmTest (ψ p).1) (R (X ω))
  let F : (ℝ × ℕ → ℝ) → ℝ → ℝ := fun a t => limUnder atTop (fun n => a (t, n))
  have hFm : Measurable F := by
    refine measurable_pi_iff.2 fun t => ?_
    exact (StronglyMeasurable.limUnder (fun n =>
      (measurable_pi_apply (t, n)).stronglyMeasurable)).measurable
  have hA : IndepFun A (fun ω => (lateralPartC (X ω), Z ω)) P :=
    IsWholePlaneGFF.indepFun_radialPairings_lateralPart_prodMk hX hRm hR ψ hZ hXZ
  have hlim : IndepFun (fun ω => F (A ω))
      (fun ω => (lateralPartC (X ω), Z ω)) P := hA.comp hFm measurable_id
  have hpath : Measurable (fun ω => (⇑(R (X ω)) : ℝ → ℝ)) :=
    measurable_pi_iff.2 fun t => (ContinuousMap.measurable_eval t).comp (hRm.comp hX.measurable)
  have hpair : Measurable (fun ω => (lateralPartC (X ω), Z ω)) :=
    (MatedCRTHarmonic.ConeScaling.measurable_lateralPart.comp hX.measurable).prodMk hZ
  have hzero : ∀ᵐ ω ∂P, R (X ω) 0 = 0 := by
    filter_upwards [hR 0] with ω hω
    simpa only [neg_zero, Real.exp_zero, sub_self] using hω
  have hind : IndepFun (fun ω => (lateralPartC (X ω), Z ω))
      (fun ω => (⇑(R (X ω)) : ℝ → ℝ)) P := by
    apply indepFun_of_forall_ae_eq_apply hpair hpath hlim.symm
    intro t
    filter_upwards [IsWholePlaneGFF.ae_locallyIntegrable_radialW hX (hRm.comp hX.measurable) hR, hzero] with ω hloc h0
    have ht := tendsto_pairW_circleDiff (R (X ω)) hloc t
    change R (X ω) t = limUnder atTop (fun n => pairW (symmTest (ψ (t, n)).1) (R (X ω)))
    simpa only [h0, sub_zero] using ht.limUnder_eq.symm
  have hσ : MeasurableSpace.comap (fun ω => R (X ω))
      (inferInstance : MeasurableSpace C(ℝ, ℝ)) = MeasurableSpace.comap
        (fun ω => (⇑(R (X ω)) : ℝ → ℝ)) MeasurableSpace.pi := by
    rw [continuousMap_measurableSpace_eq, MeasurableSpace.comap_comp]
    rfl
  rw [IndepFun_iff_Indep, hσ]
  exact (IndepFun_iff_Indep _ _ _).1 hind.symm

end LatticeProb.LQG
