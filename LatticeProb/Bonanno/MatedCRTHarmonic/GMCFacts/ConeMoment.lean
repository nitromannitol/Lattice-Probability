/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.ConeMoment at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82; imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.AreaBallMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.WeightedDiscMoment

/-!
# `AreaBallMoment`: moments of the cone's unit-disc area

**Target** (`CellScaling.AreaBallMoment D`, [16, Lemma A.3] with `α = γ`): for the cone
realization `D`, `ω ↦ μ_h(B_1(0))` is a.e.-measurable and `E[μ_h(B_1(0))^p] < ∞` for `0 < p < 4/γ² − 1`.

**Proof.** With the decomposition `h = X̃ + g` of `ConeCompare.lean` (`X̃` a whole-plane GFF normalized by
`X̃_1(0) = 0`, `g = γ(−log|·|)` on `𝔻`), the cone area is `μ_h = e^{γ g} μ_{X̃}` off `0` and has no atom at `0`
(`ae_lqgArea_cone_eq`: the vague limit built in `coneAreaExists_holds` is the punctured one, and vague limits are
unique). Hence `μ_h(B_1(0)) = ∫_{B_1(0)} |z|^{−γ²} dμ_{X̃}(z)` a.s. (`ae_lqgArea_cone_ball_eq`), whose measurability and
moments are `WeightedMoment.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMCFacts

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.MoTPort MatedCRTHarmonic.CellScaling

/-- **The cone area is `e^{γ g} μ_{X̃}` on `ℂ ∖ {0}` and has no atom at `0`.** -/
theorem ae_lqgArea_cone_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} (hX : IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) :
    ∃ Xt : Ω → DistC, IsNormalizedWPGFF Xt P ∧ ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ,
      (∀ z : ℂ, ‖z‖ ≤ 1 → g z = γ * (-Real.log ‖z‖)) ∧
      lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)) =
        ((qAreaC γ (Xt ω)).restrict (univ \ {0})).withDensity
          fun z => ENNReal.ofReal (Real.exp (γ * g z)) := by
  have hP : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  obtain ⟨Xt, hXt, hdec⟩ := exists_cone_decomposition hγ hX hB hB' hind hγ2
  refine ⟨Xt, hXt, ?_⟩
  have hcQ : γ < QuantumZipper.Qc γ := by
    unfold QuantumZipper.Qc
    have : γ / 2 < 2 / γ := by rw [div_lt_div_iff₀ two_pos hγ]; nlinarith
    linarith
  filter_upwards [hdec, ConeArea3.ae_hasCircleAvgs hXt.1, ConeArea4.ae_areaGood_univ hXt.1 hγ hγ2,
    ConeArea6.ae_tight_logFactor' hγ hγ2 hcQ hXt.1] with ω ⟨g, hd, hgm, hgli, hgc, hg1⟩ hω_circ
    hω_good hω_tight
  refine ⟨g, hg1, ?_⟩
  have hgc' : ContinuousOn g (univ \ {0}) := hgc.mono fun z hz => hz.2
  have hU : IsOpen (univ \ {(0 : ℂ)}) := isOpen_univ.sdiff isClosed_singleton
  have hXtU : QuantumZipper.IsVagueLimitOn (univ \ {0}) (areaApproxC γ (Xt ω))
      ((qAreaC γ (Xt ω)).restrict (univ \ {0})) :=
    isVagueLimitOn_restrict hU (fun K hK => ConeArea.qAreaC_compact_lt_top γ _ hK)
      (fun f hf hfs => (ConeArea.isVagueLimitOn_qAreaC hω_good.1).2.2 f hf hfs (subset_univ _))
  have hb1 := ConeArea3.isVagueLimitOn_areaApproxC_add_ofFunC hU hXtU hω_circ hgm hgli hgc'
  have hb3 := ConeArea5.tight_add_ofFunC (c := γ) (C := 0) hγ one_pos hω_circ hgli hgc'
    (fun w _ hw => by rw [hg1 w hw.le, add_zero]) hω_tight
  have hb2 : ∀ K, IsCompact K → ∀ᶠ k in atTop, areaApproxC γ (Xt ω + MoTPort.ofFunC g) k K < ⊤ :=
    fun K hK => ConeArea4.fin_of_away_of_tight
      (fun K' hK' h0 => ConeArea4.eventually_lt_top_add_ofFunC hω_circ hgli hgc'
        (fun K hK => hω_good.2 K hK (subset_univ K)) hK' h0)
      hb3 hK
  have hlim := ConeArea2.isVagueLimitOn_univ_of_punctured hb1 hb2 hb3
  -- `lqgArea` is the (unique) vague limit
  have hex : ∃ μ, IsVagueLimitC
      (lqgAreaApprox γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) μ := by
    refine ⟨_, fun K hK => hlim.2.1 K hK (subset_univ K), fun f hf hfs => ?_⟩
    rw [hd]
    simpa only [lqgAreaApprox_eq_areaApproxC] using hlim.2.2 f hf hfs (subset_univ _)
  have hμh : IsVagueLimitC (lqgAreaApprox γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)))
      (lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) := by
    rw [lqgArea, dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec
  have hcone : QuantumZipper.IsVagueLimitOn univ (areaApproxC γ (Xt ω + MoTPort.ofFunC g))
      ((lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))).restrict univ) := by
    rw [← hd]
    refine isVagueLimitOn_restrict isOpen_univ hμh.1 fun f hf hfs => ?_
    simpa only [lqgAreaApprox_eq_areaApproxC] using hμh.2 f hf hfs
  have huniq := QuantumZipper.isVagueLimitOn_unique isOpen_univ hcone hlim
  rwa [Measure.restrict_univ] at huniq

set_option linter.deprecated false in
/-- **The cone area of the unit disc is the weighted mass of the whole-plane GFF's area**:
`μ_h(B_1(0)) = ∫_{B_1(0)} |z|^{−γ²} dμ_{X̃}(z)` a.s. -/
theorem ae_lqgArea_cone_ball_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} (hX : IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) :
    ∃ Xt : Ω → DistC, IsNormalizedWPGFF Xt P ∧ ∀ᵐ ω ∂P,
      lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)) (ball 0 1) =
        wDiscMass γ (qAreaC γ (Xt ω)) := by
  obtain ⟨Xt, hXt, hae⟩ := ae_lqgArea_cone_eq hγ hγ2 hX hB hB' hind
  refine ⟨Xt, hXt, ?_⟩
  filter_upwards [hae] with ω ⟨g, hg1, heq⟩
  set μt := qAreaC γ (Xt ω)
  set F : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (-γ ^ 2))
  have hγ2' : -γ ^ 2 ≠ 0 := by have := pow_pos hγ 2; linarith
  have hS : MeasurableSet (univ \ {(0 : ℂ)}) := MeasurableSet.univ.diff (measurableSet_singleton 0)
  rw [heq, withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball]
  have h1 : ∫⁻ z in ball 0 1 ∩ (univ \ {0}), ENNReal.ofReal (Real.exp (γ * g z)) ∂μt =
      ∫⁻ z in ball 0 1 ∩ (univ \ {0}), F z ∂μt := by
    refine setLIntegral_congr_fun (measurableSet_ball.inter hS) fun z hz => ?_
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz.2.2
    simp only [F]
    rw [hg1 z (mem_ball_zero_iff.1 hz.1).le, Real.rpow_def_of_pos hz0]
    congr 2
    ring
  have h2 : ∫⁻ z in ball 0 1 \ (univ \ {0}), F z ∂μt = 0 := by
    have hsub : ball 0 1 \ (univ \ {0}) ⊆ ({0} : Set ℂ) := fun z hz => by
      by_contra h
      exact hz.2 ⟨mem_univ z, h⟩
    refine le_antisymm ((lintegral_mono_set hsub).trans (le_of_eq ?_)) zero_le
    rw [lintegral_singleton]
    simp only [F, norm_zero, Real.zero_rpow hγ2', ENNReal.ofReal_zero, zero_mul]
  rw [h1, wDiscMass, ← lintegral_inter_add_diff _ (ball 0 1) hS, h2, add_zero]

/-- **`AreaBallMoment`** ([16, Lemma A.3]) for every cone realization: a.e.
measurability of `μ_h(B_1(0))` and `E[μ_h(B_1(0))^p] < ∞` for `0 < p < 4/γ² − 1`. -/
theorem areaBallMoment_holds {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) :
    AreaBallMoment D := by
  obtain ⟨hγ, hγ2⟩ := M.hγ
  obtain ⟨Xt, hXt, hball⟩ := ae_lqgArea_cone_ball_eq hγ hγ2 D.gff D.brownian D.brownian' D.indep
  obtain ⟨H, hH, hHm, -, hμ⟩ := exists_isLQGAreaOf hXt hγ hγ2
  have heq : (fun ω => D.area ω (ball 0 1)) =ᵐ[M.coupled.family.P]
      fun ω => wDiscMass γ (qAreaC γ (Xt ω)) := hball
  refine ⟨(aemeasurable_wDiscMass hH hHm hγ hμ).congr heq.symm, fun p hp0 hp => ?_⟩
  rw [lintegral_congr_ae (heq.mono fun ω (h : D.area ω (ball 0 1) = _) => by
    show D.area ω (ball 0 1) ^ p = wDiscMass γ (qAreaC γ (Xt ω)) ^ p
    rw [h])]
  exact lintegral_wDiscMass_rpow_lt_top hH hHm hγ hμ hp0 hp

/-- `AreaDominatesWholePlaneGFF` for the cone realization, with `γ ∈ (0, 2)` taken from the model. -/
theorem areaDominates_toCellModel_holds {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M)
    (hpar : AreaParametrization D) : GMSLemma27.AreaDominatesWholePlaneGFF (D.toCellModel hpar) :=
  areaDominates_toCellModel D hpar M.hγ.1 M.hγ.2

end MatedCRTHarmonic.GMCFacts
