/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.MarkovComparison at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.RandomShiftComparison
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.IG.GFF.AbsContMarkov

/-!
# Local whole-plane GFF comparison with a random circle normalization

The random normalization scalar and the exterior harmonic field are mixed
together; the common zero-boundary part is shifted by a smooth test function.
The resulting local density has a finite moment above one in both directions.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric
open LQGMetric LQGMetric.GM LQGMetric.MarkovZB LQGMetric.CircleAvg
open MatedCRTHarmonic.MoTPort MatedCRTHarmonic.MoTPort.GFFBdry
open MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCM

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- The Markov product law and the Gaussian square moment produce local
`L^p` absolute continuity after a random finite-energy shift. The reference
law is the shifted field, the orientation used by [18] (4.16). -/
theorem LocalMarkov.randomShift_local_reverse
    {V W : Opens ℂ} (M : LocalMarkov V P h)
    (hh : IsNormalizedWPGFF h P) (hWV : W ≤ V)
    (hadm : ZBAdmissible V) (hne : (V : Set ℂ).Nonempty)
    (R : ℝ) (z₀ : ℂ) (hR : 0 < R)
    (hV₁ : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1))
    (hVR : Disjoint (V : Set ℂ) (sphere z₀ R))
    (f₀ f₁ : zsSub (V : Set ℂ)) :
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧ ∃ D : DistOn W → ℝ≥0∞,
      Measurable D ∧
      P.map (fun ω => restrictTo W (h ω)) =
        (P.map (fun ω => resOn W V
          (restrictTo V (h ω) + ofFunOn V
            (f₀ + cInc h R z₀ 1 0 ω • f₁).1))).withDensity D ∧
      ∫⁻ y, D y ^ p ∂(P.map (fun ω => resOn W V
        (restrictTo V (h ω) + ofFunOn V
          (f₀ + cInc h R z₀ 1 0 ω • f₁).1))) < ⊤ := by
  let : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  let A : Ω → DistC × ℝ := fun ω => (M.G ω, cInc h R z₀ 1 0 ω)
  let Z : Ω → DistOn V := fun ω => restrictTo V (M.Z ω)
  let κ : Measure (DistC × ℝ) := P.map A
  have hA : Measurable A :=
    (M.G_meas.mono (GM.Bilip.fieldSigmaClosed_le hh.1.measurable _) le_rfl).prodMk
      (measurable_cInc hh.1 R z₀ 1 0)
  let : IsProbabilityMeasure κ :=
    (Measure.isProbabilityMeasure_map_iff hA.aemeasurable).2 inferInstance
  obtain ⟨t, ht, hct⟩ := exists_normalization_increment_exp_sq hh.1 hR z₀
  have hctκ : Integrable (fun a : DistC × ℝ => Real.exp (t * a.2 ^ 2)) κ := by
    exact (integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun a : DistC × ℝ => Real.exp (t * a.2 ^ 2)) κ)
      hA.aemeasurable).2 (by simpa only [Function.comp_def] using hct)
  let obs : (DistC × ℝ) × DistOn V → DistOn W :=
    fun x => resOn W V (restrictTo V x.1.1 + x.2)
  have hobs : Measurable obs := by
    exact (measurable_resOn W V).comp
      ((measurable_add_distOn V).comp
        (((measurable_restrictTo V).comp (measurable_fst.comp measurable_fst)).prodMk
          measurable_snd))
  obtain ⟨p, hp, hp2, D, hDm, hLaw, hMom⟩ :=
    randomZB_observation_comparison_reverse M.zeroBoundary hadm hne
      f₀ f₁ Prod.snd measurable_snd ht hctκ obs hobs
  have hJoint := M.joint_exterior_zeroBoundary hh R z₀ hR hV₁ hVR
  have hbase : (κ.prod (P.map Z)).map obs =
      P.map (fun ω => restrictTo W (h ω)) := by
    rw [← hJoint, Measure.map_map hobs (hA.prodMk M.zeroBoundary.measurable)]
    refine Measure.map_congr (M.dec.mono fun ω hω => ?_)
    simp only [Function.comp_apply, obs, A]
    rw [hω, restrictTo_add, resOn_add W V, resOn_restrictTo hWV, resOn_restrictTo hWV]
  have hshift : (κ.prod (P.map Z)).map (fun x =>
      obs (x.1, randomZBShift f₀ f₁ x.1.2 x.2)) =
      P.map (fun ω => resOn W V
        (restrictTo V (h ω) + ofFunOn V
          (f₀ + cInc h R z₀ 1 0 ω • f₁).1)) := by
    have hobsShift : Measurable (fun x : (DistC × ℝ) × DistOn V =>
        obs (x.1, randomZBShift f₀ f₁ x.1.2 x.2)) := by
      exact hobs.comp (measurable_fst.prodMk
        ((measurable_randomZBShift f₀ f₁).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    rw [← hJoint, Measure.map_map hobsShift (hA.prodMk M.zeroBoundary.measurable)]
    refine Measure.map_congr (M.dec.mono fun ω hω => ?_)
    simp only [Function.comp_apply, obs, A, randomZBShift]
    rw [ofFunOn_add_smul_zsSub, hω, restrictTo_add]
    congr 1
    abel
  exact ⟨p, hp, hp2, D, hDm, by rw [← hbase, ← hshift]; exact hLaw,
    by rw [← hshift]; exact hMom⟩

end MatedCRTHarmonic.GMSCM
