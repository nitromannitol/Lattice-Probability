/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.IGRecentrePhase at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.IGRecentre

/-!
# The phase-aware IG recentring of [18] Lemma 4.9

Same setting as `GMS4cO/IGRecentre.lean`, but keeping the IG phase `U` among the conditioning variables (the
frozen IG field is `hIG₀ + U`). With `a = hIG₀,r(z)`, `R = 2πχ`, `h'' = hIG₀(z + r ·) − a` and
`U' = (a + U) mod R`, `L43O.igRecentre_phase` gives one continuous-valued S7 factor `F` such that

* `E_V(η_L) = F(hIG₀|_{V^δ}, U)` almost surely;
* `law((a, U), E_V(affineReroot z r 0 η_L)) = law((a, U), F(h''|_{V^δ}, U'))`;
* `(a, U) ⟂ h''|_{V^δ}` and `law(h''|_{V^δ}) = law(hIG₀|_{V^δ})`.

So, given `(a, U)`, the recentred excursion data is `F(·, U')` applied to an independent copy of the local IG field:
The phase enters only through `U'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRTHarmonic.L43O

attribute [local instance] Classical.propDecidable

section IGPhase

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The IG period `2πχ` is positive for `γ ∈ (0, 2)`. -/
theorem igPeriod_pos {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) : 0 < 2 * Real.pi * igChi γ := by
  have h1 : 0 < igChi γ := by
    unfold igChi
    have h2 : γ / 2 < 2 / γ := by
      rw [div_lt_div_iff₀ (by norm_num) hγ.1]
      nlinarith [hγ.1, hγ.2]
    linarith
  positivity

theorem igRecentre_phase
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ)) {δ : ℝ} (hδ : 0 < δ)
    (hVδ : ((GMS4c.thickOpen V δ : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆ ball (0 : ℂ) 1)
    [Fact (0 < 2 * Real.pi * igChi γ)]
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ closedBall (0 : ℂ) 1) :
    ∃ F : DistOn (GMS4c.thickOpen V δ) × ℝ → (ℚ × ℚ → ℝ → ℂ), Measurable F ∧
      (∀ x q, Continuous (F x q)) ∧
      (∀ᵐ ω ∂P, excursionData V (ηL ω) = F (restrictTo (GMS4c.thickOpen V δ) (hIG₀ ω), U ω)) ∧
      P.map (fun ω => ((circleAvg (hIG₀ ω) r z, U ω),
          excursionData V (affineReroot z r 0 (ηL ω)))) =
        P.map (fun ω => ((circleAvg (hIG₀ ω) r z, U ω),
          F (restrictTo (GMS4c.thickOpen V δ) (IGLaw.affField r 0 z (hIG₀ ω)),
            IGLaw.modRep (2 * Real.pi * igChi γ) (circleAvg (hIG₀ ω) r z + U ω)))) ∧
      IndepFun (fun ω => (circleAvg (hIG₀ ω) r z, U ω))
        (fun ω => restrictTo (GMS4c.thickOpen V δ) (IGLaw.affField r 0 z (hIG₀ ω))) P ∧
      P.map (fun ω => restrictTo (GMS4c.thickOpen V δ) (IGLaw.affField r 0 z (hIG₀ ω))) =
        P.map (fun ω => restrictTo (GMS4c.thickOpen V δ) (hIG₀ ω)) := by
  have := D.isProbabilityMeasure
  set W := GMS4c.thickOpen V δ with hWdef
  have hVW : (V : Set ℂ) ⊆ (W : Set ℂ) := self_subset_thickening hδ _
  have hVc : ((V : Set ℂ)ᶜ).Nonempty := compl_nonempty_of_subset_ball (hVW.trans hVδ)
  obtain ⟨Φ, hΦ, hign, hroot, hcc, -⟩ := D.igMap
  set R : ℝ := 2 * Real.pi * igChi γ with hRdef
  have hRpos : 0 < R := IGLaw.period_pos_of_uniform D.igField.2.1
  have hh : IsNormalizedWPGFF hIG₀ P := D.igField.1
  have hUlaw := D.igField.2.1
  have hind : IndepFun hIG₀ U P := D.igField.2.2
  have hUm : AEMeasurable U P := MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif hRpos hUlaw
  have hhm : Measurable hIG₀ := hh.1.measurable
  obtain ⟨F, hFm, hFc, hFae⟩ := exists_excursionData_factor D V hVb hδ
  have hΦpos : ∀ K, Φ (IGLaw.posIn K) = Φ K := fun K => hign _ _ (IGLaw.posIn_eq_on_pos K)
  -- the positive-radius form of the two `igMap` clauses, for the same `Φ`
  have hroot' : ∀ᵐ ω ∂P, ηL ω = Φ (IGLaw.posIn (IGLaw.igCircleAvgInput (hIG₀ ω, U ω))) := by
    filter_upwards [hroot] with ω hω
    rw [hΦpos]
    exact hω
  have hcc' : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (IGLaw.posIn (igPullback γ z₀ s φ (IGLaw.igCircleAvgInput (hIG₀ ω, U ω)))) =
        affineReroot z₀ s φ (ηL ω) := by
    intro z₀ s φ hs
    filter_upwards [hcc z₀ s φ hs] with ω hω
    rw [hΦpos]
    exact hω
  have htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) := by
    filter_upwards [D.spaceFilling] with ω hω
    exact hω.2.1
  have hτ := IGLaw.ae_firstHit_zero_of_ccPos hroot' hcc' htr
  have hper := IGLaw.ae_periodic_of_ccPos hroot' hcc' hτ
  -- the curve read at positive radii, and the base agreement set
  set Ψ : Field × ℝ → C(ℝ, ℂ) := fun x => Φ (IGLaw.posIn (IGLaw.igCircleAvgInput x)) with hΨdef
  have hΨm : Measurable Ψ :=
    hΦ.comp (IGLaw.measurable_posIn.comp IGLaw.measurable_igCircleAvgInput)
  have hFin : Measurable fun x : Field × ℝ => F (restrictTo W x.1, x.2) :=
    hFm.comp (((measurable_restrictTo W).comp measurable_fst).prodMk measurable_snd)
  set T : Set (Field × ℝ) :=
    {x | AgreeRat (excursionData V (Ψ x)) (F (restrictTo W x.1, x.2))} with hTdef
  have hTm : MeasurableSet T :=
    measurableSet_agreeRat ((measurable_excursionData V hVc).comp hΨm) hFin
  have hT : ∀ᵐ ω ∂P, (hIG₀ ω, U ω) ∈ T := by
    filter_upwards [hroot', hFae] with ω hr hF
    intro q t
    change excursionData V (Ψ (hIG₀ ω, U ω)) q t = F (restrictTo W (hIG₀ ω), U ω) q t
    rw [show Ψ (hIG₀ ω, U ω) = ηL ω from hr.symm, hF]
  -- the model field and phase
  set a : Ω → ℝ := fun ω => circleAvg (hIG₀ ω) r z with hadef
  have ham : Measurable a := (measurable_circleAvg_left r z).comp hhm
  set h'' : Ω → Field := fun ω => IGLaw.affField r 0 z (hIG₀ ω) with hh''def
  set U' : Ω → ℝ := fun ω => IGLaw.modRep R (a ω + U ω) with hU'def
  have hU'm : AEMeasurable U' P :=
    (IGLaw.measurable_modRep R).comp_aemeasurable (ham.aemeasurable.add hUm)
  have hh'gff : IsWholePlaneGFF (fun ω => MoTPort.rotateField 0 (affineComp r z (hIG₀ ω))) P :=
    IGLaw.IsWholePlaneGFF.rotateField (hh.1.affineComp hr z) 0
  have hh''gff : IsWholePlaneGFF h'' P := hh'gff.addConst ham.neg
  have hcov : ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      circleAvg (MoTPort.rotateField 0 (affineComp r z (hIG₀ ω))) ρ w =
        circleAvg (hIG₀ ω) (r * ρ) ((r : ℂ) * Complex.exp ((0 : ℝ) * Complex.I) * w + z) :=
    IGLaw.ae_circleAvg_affineRotate_all hh.1 0 hr z
  have hadd : ∀ w : ℂ, ∀ ρ : ℝ, 0 < ρ → ∀ᵐ ω ∂P, ∀ c : ℝ,
      circleAvg (addConst (MoTPort.rotateField 0 (affineComp r z (hIG₀ ω))) c) ρ w =
        circleAvg (MoTPort.rotateField 0 (affineComp r z (hIG₀ ω))) ρ w + c :=
    fun w ρ hρ => CircleAvg.ae_circleAvg_addConst hh'gff w hρ
  have hh''norm : IsNormalizedWPGFF h'' P := by
    refine ⟨hh''gff, ?_⟩
    filter_upwards [hcov, hadd 0 1 one_pos] with ω hω hadd1
    show circleAvg (addConst (MoTPort.rotateField 0 (affineComp r z (hIG₀ ω)))
      (-(circleAvg (hIG₀ ω) r z))) 1 0 = 0
    rw [hadd1, hω 1 one_pos 0]
    simp
  -- the law of `(h'', U')`
  have hpairU' : P.map (fun ω => (hIG₀ ω, U' ω)) = P.map (fun ω => (hIG₀ ω, U ω)) :=
    IGLaw.map_pair_shift_mod hhm hUlaw hind (V := fun x => circleAvg x r z)
      (measurable_circleAvg_left r z)
  have hp : AEMeasurable (fun ω => (hIG₀ ω, U ω)) P := hhm.aemeasurable.prodMk hUm
  have hp' : AEMeasurable (fun ω => (hIG₀ ω, U' ω)) P := hhm.aemeasurable.prodMk hU'm
  have hp'' : AEMeasurable (fun ω => (h'' ω, U' ω)) P :=
    hh''gff.measurable.aemeasurable.prodMk hU'm
  have hGm : Measurable fun p : Field × ℝ => (IGLaw.affField r 0 z p.1, p.2) :=
    ((IGLaw.measurable_affField r 0 z).comp measurable_fst).prodMk measurable_snd
  have hlaw'' : P.map (fun ω => (h'' ω, U' ω)) = P.map (fun ω => (hIG₀ ω, U ω)) := by
    have e1 : P.map (fun ω => (h'' ω, U' ω)) = P.map (fun ω => (h'' ω, U ω)) := by
      calc P.map (fun ω => (h'' ω, U' ω)) =
          (P.map (fun ω => (hIG₀ ω, U' ω))).map fun p => (IGLaw.affField r 0 z p.1, p.2) :=
            (AEMeasurable.map_map_of_aemeasurable hGm.aemeasurable hp').symm
        _ = (P.map (fun ω => (hIG₀ ω, U ω))).map fun p => (IGLaw.affField r 0 z p.1, p.2) := by
            rw [hpairU']
        _ = P.map (fun ω => (h'' ω, U ω)) :=
            AEMeasurable.map_map_of_aemeasurable hGm.aemeasurable hp
    have hind'' : IndepFun h'' U P := hind.comp (IGLaw.measurable_affField r 0 z) measurable_id
    rw [e1, (indepFun_iff_map_prod_eq_prod_map_map hh''gff.measurable.aemeasurable hUm).1 hind'',
      (indepFun_iff_map_prod_eq_prod_map_map hhm.aemeasurable hUm).1 hind,
      CircleAvg.map_eq_of_isNormalizedWPGFF hh''norm hh]
  -- the agreement and periodicity transferred to the model
  have hT'' : ∀ᵐ ω ∂P, (h'' ω, U' ω) ∈ T := IGLaw.ae_of_map_eq hp hp'' hlaw''.symm hTm hT
  have hper' : ∀ᵐ ω ∂P, (h'' ω, U' ω) ∈ {x : Field × ℝ | ∀ k : ℤ,
      Φ (IGLaw.posIn (IGLaw.addIn (R * k) (IGLaw.igCircleAvgInput x))) =
        Φ (IGLaw.posIn (IGLaw.igCircleAvgInput x))} :=
    IGLaw.ae_of_map_eq hp hp'' hlaw''.symm (IGLaw.measurableSet_periodicPos hΦ R) hper
  -- the transformed input agrees coordinatewise with the model process
  set Kp : Ω → ℝ → ℂ → ℝ := fun ω =>
    IGLaw.posIn (igPullback γ z r 0 (IGLaw.igCircleAvgInput (hIG₀ ω, U ω))) with hKpdef
  set M : Ω → ℝ → ℂ → ℝ := fun ω =>
    IGLaw.posIn (IGLaw.igCircleAvgInput (h'' ω, a ω + U ω)) with hMdef
  have hKpm : AEMeasurable Kp P :=
    (IGLaw.measurable_posIn.comp (IGLaw.measurable_igPullback γ z r 0)).comp_aemeasurable
      (IGLaw.measurable_igCircleAvgInput.comp_aemeasurable hp)
  have hMm : AEMeasurable M P :=
    (IGLaw.measurable_posIn.comp IGLaw.measurable_igCircleAvgInput).comp_aemeasurable
      (hh''gff.measurable.aemeasurable.prodMk (ham.aemeasurable.add hUm))
  have hKM : ∀ ρ w, (fun ω => Kp ω ρ w) =ᵐ[P] fun ω => M ω ρ w := by
    intro ρ w
    rcases le_or_gt ρ 0 with hρ | hρ
    · refine Eventually.of_forall fun ω => ?_
      change IGLaw.posIn _ ρ w = IGLaw.posIn _ ρ w
      rw [IGLaw.posIn_apply_of_nonpos hρ, IGLaw.posIn_apply_of_nonpos hρ]
    · filter_upwards [hcov, hadd w ρ hρ] with ω hω haddω
      change IGLaw.posIn _ ρ w = IGLaw.posIn _ ρ w
      rw [IGLaw.posIn_apply_of_pos hρ, IGLaw.posIn_apply_of_pos hρ]
      change circleAvg (hIG₀ ω) (r * ρ) (z + (r : ℂ) * Complex.exp ((0 : ℝ) * Complex.I) * w) +
          U ω - igChi γ * 0 =
        circleAvg (addConst (MoTPort.rotateField 0 (affineComp r z (hIG₀ ω)))
          (-(circleAvg (hIG₀ ω) r z))) ρ w + (circleAvg (hIG₀ ω) r z + U ω)
      rw [haddω, hω ρ hρ w, add_comm z]
      ring
  have hjoint : P.map (fun ω => (a ω, Kp ω)) = P.map (fun ω => (a ω, M ω)) :=
    map_prod_eq_of_forall_ae_eq ham.aemeasurable hKpm hMm hKM
  -- the read-out map
  set G : ℝ × (ℝ → ℂ → ℝ) → ℝ × (ℚ × ℚ → ℝ → ℂ) := fun x => (x.1, excursionData V (Φ x.2))
    with hGdef
  have hGm' : Measurable G :=
    measurable_fst.prodMk ((measurable_excursionData V hVc).comp (hΦ.comp measurable_snd))
  -- independence of `(a, U)` from the model's local field
  set Y : Ω → DistOn (ballO z r) := fun ω => restrictTo (ballO z r) (addConst (hIG₀ ω) (-a ω))
    with hYdef
  have hYm : Measurable Y :=
    (measurable_restrictTo _).comp (hh.1.addConst ham.neg).measurable
  have haY : IndepFun a Y P := GMSAppA.lemmaA2_indepFun hh hr hzr
  have hfun : Measurable fun x : Field =>
      (restrictTo (ballO z r) (addConst x (-(circleAvg x r z))), circleAvg x r z) := by
    refine Measurable.prodMk ?_ (measurable_circleAvg_left r z)
    exact CONF.measurable_restrictTo_addConst' (ballO z r) (Ψ := id)
      (x := fun x : Field => -circleAvg x r z) (measurable_restrictTo _)
      (measurable_circleAvg_left r z).neg
  have hYaU : IndepFun (fun ω => (Y ω, a ω)) U P := hind.comp hfun measurable_id
  have hY_aU : IndepFun Y (fun ω => (a ω, U ω)) P :=
    indepFun_prod_of_indep hYm.aemeasurable ham.aemeasurable hUm hYaU haY.symm
  set Θ : DistOn (ballO z r) → DistOn W := fun y =>
    distAffine r z hr.ne' (resDist (affOpens r z W) (ballO z r) y) with hΘdef
  have hΘm : Measurable Θ := measurable_restrictTo_affField_factor hr z
  have hloc : ∀ ω, restrictTo W (h'' ω) = Θ (Y ω) := fun ω =>
    restrictTo_affField_eq hVδ hr z (hIG₀ ω)
  have hind_aU : IndepFun (fun ω => (a ω, U ω)) (fun ω => restrictTo W (h'' ω)) P := by
    refine (hY_aU.symm.comp measurable_id hΘm).congr (ae_of_all _ fun _ => rfl)
      (ae_of_all _ fun ω => ?_)
    simp only [Function.comp, hloc ω]
  have hlawR : P.map (fun ω => restrictTo W (h'' ω)) = P.map (fun ω => restrictTo W (hIG₀ ω)) := by
    have hlaw := CircleAvg.map_eq_of_isNormalizedWPGFF hh''norm hh
    calc P.map (fun ω => restrictTo W (h'' ω))
        = (P.map h'').map (restrictTo W) :=
          (Measure.map_map (f := h'') (measurable_restrictTo W) hh''gff.measurable).symm
      _ = (P.map hIG₀).map (restrictTo W) := by rw [hlaw]
      _ = P.map (fun ω => restrictTo W (hIG₀ ω)) := Measure.map_map (measurable_restrictTo W) hhm
  -- the joint law with the pair `(a, U)`
  have hjoint2 : P.map (fun ω => ((a ω, U ω), Kp ω)) = P.map (fun ω => ((a ω, U ω), M ω)) :=
    map_prod2_eq_of_forall_ae_eq (ham.aemeasurable.prodMk hUm) hKpm hMm hKM
  set G2 : (ℝ × ℝ) × (ℝ → ℂ → ℝ) → (ℝ × ℝ) × (ℚ × ℚ → ℝ → ℂ) :=
    fun x => (x.1, excursionData V (Φ x.2)) with hG2def
  have hG2m : Measurable G2 :=
    measurable_fst.prodMk ((measurable_excursionData V hVc).comp (hΦ.comp measurable_snd))
  refine ⟨F, hFm, hFc, hFae, ?_, hind_aU, hlawR⟩
  calc P.map (fun ω => ((a ω, U ω), excursionData V (affineReroot z r 0 (ηL ω))))
      = P.map (fun ω => G2 ((a ω, U ω), Kp ω)) := by
        refine Measure.map_congr ?_
        filter_upwards [hcc' z r 0 hr] with ω hω
        simp only [hG2def]
        rw [hω]
    _ = (P.map fun ω => ((a ω, U ω), Kp ω)).map G2 :=
        (AEMeasurable.map_map_of_aemeasurable hG2m.aemeasurable
          ((ham.aemeasurable.prodMk hUm).prodMk hKpm)).symm
    _ = (P.map fun ω => ((a ω, U ω), M ω)).map G2 := by rw [hjoint2]
    _ = P.map (fun ω => G2 ((a ω, U ω), M ω)) :=
        AEMeasurable.map_map_of_aemeasurable hG2m.aemeasurable
          ((ham.aemeasurable.prodMk hUm).prodMk hMm)
    _ = P.map (fun ω => ((a ω, U ω), F (restrictTo W (h'' ω), U' ω))) := by
        refine Measure.map_congr ?_
        filter_upwards [hper', hT''] with ω hpω hTω
        simp only [hG2def]
        obtain ⟨k, hk⟩ := IGLaw.exists_int_eq_modRep_add R (a ω + U ω)
        have e : M ω = IGLaw.posIn (IGLaw.addIn (R * k) (IGLaw.igCircleAvgInput (h'' ω, U' ω))) := by
          have hk' : a ω + U ω = U' ω + R * k := hk
          show IGLaw.posIn (IGLaw.igCircleAvgInput (h'' ω, a ω + U ω)) = _
          rw [hk', IGLaw.igCircleAvgInput_add]
        rw [e, hpω k]
        refine Prod.ext rfl ?_
        exact eq_of_agreeRat (continuous_excursionData V _) (hFc _) hTω

end IGPhase

end MatedCRTHarmonic.L43O
