/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.IGRecentre at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaApprox
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ContVersion

/-!
# The imaginary-geometry side of the recentring in [18] Lemma 4.9

Source: [18, Lemma 4.9]. In the proof of Lemma 4.9 the pair `(h, h^IG)` is
conditioned on its circle averages over `∂B_r(z)`, `r = ε^{q−4ζ}`, and recentred by the affine map
`w ↦ z + r w`. On the imaginary-geometry side the frozen bundle's field is `hIG₀ + U`: the recentred
normalized field `h'' = hIG₀(z + r ·) − hIG₀_r(z)` is again a normalized whole-plane GFF, and the additive constant
`hIG₀_r(z) + U` is reduced modulo `2πχ` to a uniform phase `U'` independent of `hIG₀` (IGCO's `OAffinePos` core,
replicated here because its intermediate facts are local to that proof).

Main result (`L43O.map_circleAvg_excursionData_affineReroot`): for `V` bounded open with `δ`-thickening inside the
unit disk and `B̄_r(z) ⊆ B̄_1(0)`, the circle average `hIG₀_r(z)` is **independent** of the rational-point excursion
data in `V` of the recentred Lebesgue-time curve `affineReroot z r 0 ηL = r⁻¹(ηL(τ + r² ·) − z)`, and that
excursion data has the law of the excursion data of `ηL` itself:

`law(hIG₀_r(z), E_V(affineReroot z r 0 ηL)) = law(hIG₀_r(z)) ⊗ law(E_V(ηL))`.

Ingredients: the frozen `igMap` (coordinate change, positive-radius reading, S7 locality), [18] Lemma A.2 in its
exact-independence form (`GMSAppA.lemmaA2_indepFun`), CAROT's simultaneous circle-average covariance, and IGCO's
`map_pair_shift_mod` / integer-period invariance.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRTHarmonic.L43O

attribute [local instance] Classical.propDecidable

section IG

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **S7 with a continuous-valued witness.** The excursion data of `ηL` in `V` is almost surely a measurable
function of `(hIG₀|_{V^δ}, U)` whose values are continuous curves. -/
theorem exists_excursionData_factor
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : DistOn (GMS4c.thickOpen V δ) × ℝ → (ℚ × ℚ → ℝ → ℂ), Measurable F ∧
      (∀ x q, Continuous (F x q)) ∧
      ∀ᵐ ω ∂P, excursionData V (ηL ω) = F (restrictTo (GMS4c.thickOpen V δ) (hIG₀ ω), U ω) := by
  obtain ⟨F₀, hF₀, hae⟩ := GMS4c.ae_bundle_excursions_from_localIG D V hVb δ hδ
  refine ⟨fun x q => if GMS4c.ratPt q ∈ V then (GMS4c.contVersion (F₀ x q) : ℝ → ℂ) else 0,
    ?_, ?_, ?_⟩
  · refine measurable_pi_iff.mpr fun q => ?_
    by_cases hq : GMS4c.ratPt q ∈ V
    · simp only [hq, ↓reduceIte]
      refine measurable_pi_iff.mpr fun t => ?_
      exact ((continuous_eval_const t).measurable.comp GMS4c.measurable_contVersion).comp
        ((measurable_pi_apply q).comp hF₀)
    · simp only [hq, ↓reduceIte]
      exact measurable_const
  · intro x q
    dsimp only
    split_ifs
    · exact (GMS4c.contVersion _).continuous
    · exact continuous_const
  · filter_upwards [hae] with ω hω
    funext q
    unfold excursionData
    by_cases hq : GMS4c.ratPt q ∈ V
    · simp only [hq, ↓reduceIte]
      have h1 := hω q hq
      exact ((congrArg (fun f => (GMS4c.contVersion f : ℝ → ℂ)) h1.symm).trans
        (GMS4c.contVersion_coe (continuous_excursionSegment _ _ _))).symm
    · simp only [hq, ↓reduceIte]

/-- A bounded open subset of the unit disk has nonempty complement. -/
theorem compl_nonempty_of_subset_ball {V : Set ℂ} (hV : V ⊆ ball (0 : ℂ) 1) : (Vᶜ).Nonempty :=
  ⟨2, fun h => by
    have := hV h
    rw [mem_ball, dist_zero_right] at this
    norm_num at this⟩

/-- The affine preimage of a subset of the unit disk lies in `B_r(z)`. -/
theorem affOpens_le_ballO {W : TopologicalSpace.Opens ℂ} (hW : (W : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {r : ℝ} (hr : 0 < r) (z : ℂ) : affOpens r z W ≤ ballO z r := by
  intro x hx
  have h1 : affMap r z x ∈ (W : Set ℂ) := hx
  have h2 := hW h1
  rw [mem_ball, dist_zero_right] at h2
  change x ∈ ball z r
  rw [mem_ball, dist_eq_norm]
  have hx' : affMap r z x = (r : ℂ)⁻¹ * (x - z) := by
    simp only [affMap, Complex.real_smul, Complex.ofReal_inv]
    ring
  rw [hx', norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h2
  rwa [inv_mul_lt_iff₀ hr, mul_one] at h2

/-- The restriction of the recentred field `hIG₀(z + r ·) − hIG₀_r(z)` to `W ⊆ 𝔻` is a measurable function of the
restriction of `hIG₀ − hIG₀_r(z)` to `B_r(z)`. -/
theorem restrictTo_affField_eq {W : TopologicalSpace.Opens ℂ} (hW : (W : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (x : DistC) :
    restrictTo W (IGLaw.affField r 0 z x) =
      distAffine r z hr.ne' (resDist (affOpens r z W) (ballO z r)
        (restrictTo (ballO z r) (addConst x (-(circleAvg x r z))))) := by
  rw [IGLaw.affField, rotateField_zero, ← GM.affineComp_addConst hr,
    CONF.hlz_restrict_affine hr, restrictTo_eq_resDist (affOpens_le_ballO hW hr z)]

theorem measurable_restrictTo_affField_factor {W : TopologicalSpace.Opens ℂ}
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Measurable fun y : DistOn (ballO z r) =>
      (distAffine r z hr.ne' (resDist (affOpens r z W) (ballO z r) y) : DistOn W) := by
  refine measurable_distOn_iff.2 fun φ => ?_
  exact ((measurable_distOn_apply (zbPull r z hr.ne' φ)).comp (measurable_resDist _ _)).const_mul _

/-- **The IG side of the Lemma 4.9 recentring.** The circle average `hIG₀_r(z)` is independent of the excursion
data in `V` of the recentred Lebesgue-time curve, which has the law of the excursion data of `ηL`. -/
theorem map_circleAvg_excursionData_affineReroot
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ)) {δ : ℝ} (hδ : 0 < δ)
    (hVδ : ((GMS4c.thickOpen V δ : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ closedBall (0 : ℂ) 1) :
    P.map (fun ω => (circleAvg (hIG₀ ω) r z, excursionData V (affineReroot z r 0 (ηL ω)))) =
      (P.map fun ω => circleAvg (hIG₀ ω) r z).prod
        (P.map fun ω => excursionData V (ηL ω)) := by
  have := D.isProbabilityMeasure
  set W := GMS4c.thickOpen V δ with hWdef
  have hVW : (V : Set ℂ) ⊆ (W : Set ℂ) := self_subset_thickening hδ _
  have hVc : ((V : Set ℂ)ᶜ).Nonempty := compl_nonempty_of_subset_ball (hVW.trans hVδ)
  obtain ⟨Φ, hΦ, hign, hroot, hcc, -⟩ := D.igMap
  set R : ℝ := 2 * Real.pi * igChi γ with hRdef
  have hRpos : 0 < R := IGLaw.period_pos_of_uniform D.igField.2.1
  have : Fact (0 < R) := ⟨hRpos⟩
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
  -- independence of `a` from the model's local data
  set Y : Ω → DistOn (ballO z r) := fun ω => restrictTo (ballO z r) (addConst (hIG₀ ω) (-a ω))
    with hYdef
  have hYm : Measurable Y :=
    (measurable_restrictTo _).comp (hh.1.addConst ham.neg).measurable
  have haY : IndepFun a Y P := GMSAppA.lemmaA2_indepFun hh hr hzr
  have hU'ind : IndepFun hIG₀ U' P := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hhm.aemeasurable hU'm, hpairU',
      (indepFun_iff_map_prod_eq_prod_map_map hhm.aemeasurable hUm).1 hind]
    congr 1
    have h2 := congrArg (fun μ : Measure (Field × ℝ) => μ.map Prod.snd) hpairU'
    rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hp',
      AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hp] at h2
    exact h2.symm
  have haYU : IndepFun (fun ω => (a ω, Y ω)) U' P := by
    have hfun : Measurable fun x : Field =>
        (circleAvg x r z, restrictTo (ballO z r) (addConst x (-(circleAvg x r z)))) := by
      refine (measurable_circleAvg_left r z).prodMk ?_
      exact CONF.measurable_restrictTo_addConst' (ballO z r) (Ψ := id)
        (x := fun x : Field => -circleAvg x r z) (measurable_restrictTo _)
        (measurable_circleAvg_left r z).neg
    exact hU'ind.comp hfun measurable_id
  have ha_YU : IndepFun a (fun ω => (Y ω, U' ω)) P :=
    indepFun_prod_of_indep ham.aemeasurable hYm.aemeasurable hU'm haYU haY
  set Θ : DistOn (ballO z r) → DistOn W := fun y =>
    distAffine r z hr.ne' (resDist (affOpens r z W) (ballO z r) y) with hΘdef
  have hΘm : Measurable Θ := measurable_restrictTo_affField_factor hr z
  have hloc : ∀ ω, restrictTo W (h'' ω) = Θ (Y ω) := fun ω =>
    restrictTo_affField_eq hVδ hr z (hIG₀ ω)
  have hFloc : Measurable fun x : DistOn (ballO z r) × ℝ => F (Θ x.1, x.2) :=
    hFm.comp ((hΘm.comp measurable_fst).prodMk measurable_snd)
  have ha_F : IndepFun a (fun ω => F (restrictTo W (h'' ω), U' ω)) P := by
    have := ha_YU.comp measurable_id hFloc
    refine this.congr (ae_of_all _ fun _ => rfl) (ae_of_all _ fun ω => ?_)
    simp only [Function.comp, hloc ω]
  have hFlocm : AEMeasurable (fun ω => F (restrictTo W (h'' ω), U' ω)) P :=
    hFin.comp_aemeasurable hp''
  -- assemble
  calc P.map (fun ω => (a ω, excursionData V (affineReroot z r 0 (ηL ω))))
      = P.map (fun ω => G (a ω, Kp ω)) := by
        refine Measure.map_congr ?_
        filter_upwards [hcc' z r 0 hr] with ω hω
        simp only [hGdef]
        rw [hω]
    _ = (P.map fun ω => (a ω, Kp ω)).map G :=
        (AEMeasurable.map_map_of_aemeasurable hGm'.aemeasurable
          (ham.aemeasurable.prodMk hKpm)).symm
    _ = (P.map fun ω => (a ω, M ω)).map G := by rw [hjoint]
    _ = P.map (fun ω => G (a ω, M ω)) :=
        AEMeasurable.map_map_of_aemeasurable hGm'.aemeasurable (ham.aemeasurable.prodMk hMm)
    _ = P.map (fun ω => (a ω, F (restrictTo W (h'' ω), U' ω))) := by
        refine Measure.map_congr ?_
        filter_upwards [hper', hT''] with ω hpω hTω
        simp only [hGdef]
        obtain ⟨k, hk⟩ := IGLaw.exists_int_eq_modRep_add R (a ω + U ω)
        have e : M ω = IGLaw.posIn (IGLaw.addIn (R * k) (IGLaw.igCircleAvgInput (h'' ω, U' ω))) := by
          have hk' : a ω + U ω = U' ω + R * k := hk
          show IGLaw.posIn (IGLaw.igCircleAvgInput (h'' ω, a ω + U ω)) = _
          rw [hk', IGLaw.igCircleAvgInput_add]
        rw [e, hpω k]
        refine Prod.ext rfl ?_
        exact eq_of_agreeRat (continuous_excursionData V _) (hFc _) hTω
    _ = (P.map a).prod (P.map fun ω => F (restrictTo W (h'' ω), U' ω)) :=
        (indepFun_iff_map_prod_eq_prod_map_map ham.aemeasurable hFlocm).1 ha_F
    _ = (P.map a).prod (P.map fun ω => excursionData V (ηL ω)) := by
        congr 1
        calc P.map (fun ω => F (restrictTo W (h'' ω), U' ω))
            = (P.map fun ω => (h'' ω, U' ω)).map fun x => F (restrictTo W x.1, x.2) :=
              (AEMeasurable.map_map_of_aemeasurable hFin.aemeasurable hp'').symm
          _ = (P.map fun ω => (hIG₀ ω, U ω)).map fun x => F (restrictTo W x.1, x.2) := by
              rw [hlaw'']
          _ = P.map (fun ω => F (restrictTo W (hIG₀ ω), U ω)) :=
              AEMeasurable.map_map_of_aemeasurable hFin.aemeasurable hp
          _ = P.map (fun ω => excursionData V (ηL ω)) :=
              Measure.map_congr (hFae.mono fun ω hω => hω.symm)

end IG

end MatedCRTHarmonic.L43O
