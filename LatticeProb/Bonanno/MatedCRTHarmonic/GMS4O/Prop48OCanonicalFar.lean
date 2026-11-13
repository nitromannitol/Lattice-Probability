/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OCanonicalFar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalH3
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48ZeroIG
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cS.WholePlaneFunctional
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalCircleProcess
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OFarPair
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OTripleMean

/-!
# The canonical far-pair covariance

On the frozen zero-cone coupling, [18] (4.35)–(4.37) with the triple conditional mean:

* `p48o_localFactor_A3`: the proved H3 (`Canonical.prop48_primedBorelLocalFactor_holds`, from the
  thickened GMC readers H2) gives the all-visit masked density as a nonnegative Borel function of
  the A.3 local observation (restrictions to `B_ℓ(z)` and the two circle averages) and the phase;
* the zero-cone covariance equals the covariance in the whole-plane model
  `(normalized X₀, hIG₀, U)` (`prop48_zeroCone_disk_IGdata_law_eq_wholePlaneGFF`), because `m³` is an
  explicit Borel function of the triple;
* `p48o_far_pair_frozen_A3` then bounds it by unconditional moments, which Lemma 4.9 controls.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter LQGMetric LQGMetric.Blueprint
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4O

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4.Canonical

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The literal zero-cone field. -/
abbrev p48oZeroField (γ : ℝ) (X₀ : Ω → MatedCRT.Field) (B₀ B₀' : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    MatedCRT.Field :=
  coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))

lemma p48o_thickWindow_le_ballO {ε q : ℝ} (z : ℂ) {ℓ : ℝ} (hℓ : 5 * ε ^ q ≤ ℓ) :
    GMS4c.thickOpen (ballO z (4 * ε ^ q)) (ε ^ q) ≤ ballO z ℓ := by
  intro x hx
  have h := Metric.thickening_ball z (ε ^ q) (4 * ε ^ q) hx
  change x ∈ Metric.ball z ℓ
  refine Metric.ball_subset_ball ?_ h
  linarith

/-- **The A.3-form local factor** of the all-visit masked density: a nonnegative Borel function of
The restrictions of `(h₀, hIG₀)` to `B_ℓ(z)`, their circle averages at `r = ε^(q−4ζ)` and the phase.
From the H3, which is proved from the thickened GMC readers. -/
theorem p48o_localFactor_A3
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (H2 : ThickGMCReaders D) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    (q ζ : ℝ) (z : ℂ) {ℓ : ℝ} (hℓ : 5 * ε ^ q ≤ ℓ) :
    ∃ f : ((DistOn (ballO z ℓ) × DistOn (ballO z ℓ)) × (ℝ × ℝ)) × ℝ → ℝ,
      Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      maskedUStarPrime D hγ ε q ζ z =ᵐ[P] fun ω => f (GMS4.prop48LocalFieldObservation
        (p48oZeroField γ X₀ B₀ B₀') hIG₀ ℓ (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ)
          z ω, U ω) := by
  have H3 := prop48_primedBorelLocalFactor_holds D hγ q ζ H2
  have hWℓ : GMS4c.thickOpen (ballO z (4 * ε ^ q)) (ε ^ q) ≤ ballO z ℓ :=
    p48o_thickWindow_le_ballO z hℓ
  obtain ⟨factor, hfac, hae⟩ := H3.factor_exists ε hε z
  have hres : Measurable (MoTPort.IG.GFFAbsCont.resOn
      (GMS4c.thickOpen (ballO z (4 * ε ^ q)) (ε ^ q)) (ballO z ℓ)) :=
    MoTPort.IG.GFFAbsCont.measurable_resOn _ _
  have hrec := (H2 (ballO z (4 * ε ^ q)) (ε ^ q) (Real.rpow_pos_of_pos hε.1 q)).measurable_reconstruct
  refine ⟨fun x => max 0 (if max |x.1.2.1| |x.1.2.2 + x.2| ≤ 2 * q * Real.log ε⁻¹ then
      factor (((H2 (ballO z (4 * ε ^ q)) (ε ^ q) (Real.rpow_pos_of_pos hε.1 q)).reconstruct
          (MoTPort.IG.GFFAbsCont.resOn (GMS4c.thickOpen (ballO z (4 * ε ^ q)) (ε ^ q))
            (ballO z ℓ) x.1.1.1),
          MoTPort.IG.GFFAbsCont.resOn (GMS4c.thickOpen (ballO z (4 * ε ^ q)) (ε ^ q))
            (ballO z ℓ) x.1.1.1),
        (MoTPort.IG.GFFAbsCont.resOn (GMS4c.thickOpen (ballO z (4 * ε ^ q)) (ε ^ q))
          (ballO z ℓ) x.1.1.2, x.2)) else 0), ?_, fun x => le_max_left _ _, ?_⟩
  · have hk : Measurable fun x : ((DistOn (ballO z ℓ) × DistOn (ballO z ℓ)) × (ℝ × ℝ)) × ℝ =>
        MoTPort.IG.GFFAbsCont.resOn (GMS4c.thickOpen (ballO z (4 * ε ^ q)) (ε ^ q))
          (ballO z ℓ) x.1.1.1 :=
      hres.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
    have hl : Measurable fun x : ((DistOn (ballO z ℓ) × DistOn (ballO z ℓ)) × (ℝ × ℝ)) × ℝ =>
        MoTPort.IG.GFFAbsCont.resOn (GMS4c.thickOpen (ballO z (4 * ε ^ q)) (ε ^ q))
          (ballO z ℓ) x.1.1.2 :=
      hres.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
    have hinner : Measurable fun x : ((DistOn (ballO z ℓ) × DistOn (ballO z ℓ)) × (ℝ × ℝ)) × ℝ =>
        factor (((H2 (ballO z (4 * ε ^ q)) (ε ^ q) (Real.rpow_pos_of_pos hε.1 q)).reconstruct
          (MoTPort.IG.GFFAbsCont.resOn (GMS4c.thickOpen (ballO z (4 * ε ^ q)) (ε ^ q))
            (ballO z ℓ) x.1.1.1),
          MoTPort.IG.GFFAbsCont.resOn (GMS4c.thickOpen (ballO z (4 * ε ^ q)) (ε ^ q))
            (ballO z ℓ) x.1.1.1),
        (MoTPort.IG.GFFAbsCont.resOn (GMS4c.thickOpen (ballO z (4 * ε ^ q)) (ε ^ q))
          (ballO z ℓ) x.1.1.2, x.2)) := by
      have h := hfac.comp (((hrec.comp hk).prodMk hk).prodMk (hl.prodMk measurable_snd))
      exact h
    have hset : MeasurableSet {x : ((DistOn (ballO z ℓ) × DistOn (ballO z ℓ)) × (ℝ × ℝ)) × ℝ |
        max |x.1.2.1| |x.1.2.2 + x.2| ≤ 2 * q * Real.log ε⁻¹} := by
      have ha : Measurable fun x : ((DistOn (ballO z ℓ) × DistOn (ballO z ℓ)) × (ℝ × ℝ)) × ℝ =>
          max |x.1.2.1| |x.1.2.2 + x.2| :=
        ((measurable_fst.comp (measurable_snd.comp measurable_fst)).abs).max
          (((measurable_snd.comp (measurable_snd.comp measurable_fst)).add measurable_snd).abs)
      exact measurableSet_le ha measurable_const
    exact measurable_const.max (Measurable.ite hset hinner measurable_const)
  · filter_upwards [hae] with ω hω
    have hnn : 0 ≤ maskedUStarPrime D hγ ε q ζ z ω := by
      simp only [maskedUStarPrime]
      refine Set.indicator_nonneg (fun ω' _ => ?_) ω
      simp only [uStarPrime]
      positivity
    rw [hω] at hnn ⊢
    dsimp only [GMS4.prop48LocalFieldObservation, GMS4.prop48CircleAverageObservation]
    rw [MoTPort.IG.GFFAbsCont.resOn_restrictTo hWℓ, MoTPort.IG.GFFAbsCont.resOn_restrictTo hWℓ]
    exact (max_eq_right hnn).symm

/-! ### The whole-plane comparison model on the same carrier -/

/-- The unit-circle-normalized whole-plane field `X₀ − (X₀)₁(0)` of the frozen coupling. -/
abbrev p48oWPField (X₀ : Ω → MatedCRT.Field) (ω : Ω) : MatedCRT.Field :=
  MatedCRTHarmonic.Canon.normalizeWholePlane (X₀ ω)

lemma p48o_wp_isNormalized
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IsNormalizedWPGFF (p48oWPField X₀) P :=
  MatedCRTHarmonic.Canon.normalizedWPGFF_of_coupling D

lemma p48o_wp_indep_IGdata
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun (p48oWPField X₀) (fun ω => (hIG₀ ω, U ω)) P :=
  GMS4cS.indepFun_normalizedWholePlane_IGdata D

lemma p48o_wp_indep_hIG
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun (p48oWPField X₀) hIG₀ P :=
  (p48o_wp_indep_IGdata D).comp measurable_id measurable_fst

/-- The phase version is independent of the pair (whole-plane field, IG field). -/
lemma p48o_wp_pair_indep_phase
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    IndepFun (fun ω => (p48oWPField X₀ ω, hIG₀ ω)) (phaseVersion D hγ) P := by
  have := D.isProbabilityMeasure
  have hU' : Measurable (phaseVersion D hγ) := measurable_phaseVersion D hγ
  have eU : U =ᵐ[P] phaseVersion D hγ := (ae_phaseVersion_eq D hγ).symm
  have hIGm : Measurable hIG₀ := D.igField.1.1.measurable
  have hWm : Measurable (p48oWPField X₀) := (p48o_wp_isNormalized D).1.measurable
  have hEC : IndepFun hIG₀ (phaseVersion D hγ) P := D.igField.2.2.congr (ae_eq_refl _) eU
  have hZEC : IndepFun (p48oWPField X₀) (fun ω => (hIG₀ ω, phaseVersion D hγ ω)) P := by
    refine (p48o_wp_indep_IGdata D).congr (ae_eq_refl _) ?_
    filter_upwards [eU] with ω hω
    rw [hω]
  have h1 : IndepFun (phaseVersion D hγ) (fun ω => (hIG₀ ω, p48oWPField X₀ ω)) P :=
    GMSAppA.indepFun_fst_prodMk_of hIGm hU' hWm hEC hZEC
  exact (h1.comp measurable_id (measurable_snd.prodMk measurable_fst)).symm

/-- The disk-restriction law: the zero-cone field and the whole-plane field have the same joint law
with the IG data on the unit disk. -/
lemma p48o_disk_law
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    P.map (fun ω => (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω), (hIG₀ ω, U ω))) =
      P.map (fun ω => (restrictTo (ballO 0 1) (p48oWPField X₀ ω), (hIG₀ ω, U ω))) :=
  GMS4.prop48_zeroCone_disk_IGdata_law_eq_wholePlaneGFF D hγ (p48o_wp_isNormalized D)
    (p48o_wp_indep_IGdata D)

/-- The local observation read from the unit-disk restriction. -/
def p48oΛ (ℓ r : ℝ) (z : ℂ) (x : DistOn (ballO (0 : ℂ) 1) × MatedCRT.Field) :
    (DistOn (ballO z ℓ) × DistOn (ballO z ℓ)) × (ℝ × ℝ) :=
  ((MoTPort.IG.GFFAbsCont.resOn (ballO z ℓ) (ballO 0 1) x.1, restrictTo (ballO z ℓ) x.2),
    (GMS4c.localCircleProcess (ballO 0 1) x.1 r z, circleAvg x.2 r z))

lemma measurable_p48oΛ (ℓ r : ℝ) (z : ℂ) : Measurable (p48oΛ ℓ r z) := by
  have h1 : Measurable fun x : DistOn (ballO (0 : ℂ) 1) × MatedCRT.Field =>
      MoTPort.IG.GFFAbsCont.resOn (ballO z ℓ) (ballO 0 1) x.1 :=
    (MoTPort.IG.GFFAbsCont.measurable_resOn _ _).comp measurable_fst
  have h2 : Measurable fun x : DistOn (ballO (0 : ℂ) 1) × MatedCRT.Field =>
      restrictTo (ballO z ℓ) x.2 := (measurable_restrictTo _).comp measurable_snd
  have h3 : Measurable fun x : DistOn (ballO (0 : ℂ) 1) × MatedCRT.Field =>
      GMS4c.localCircleProcess (ballO 0 1) x.1 r z := by
    have hfst : Measurable fun x : DistOn (ballO (0 : ℂ) 1) × MatedCRT.Field => x.1 :=
      measurable_fst
    have h := ((measurable_pi_apply z).comp (measurable_pi_apply r)).comp
      ((GMS4c.measurable_localCircleProcess (ballO 0 1)).comp hfst)
    exact h
  have h4 : Measurable fun x : DistOn (ballO (0 : ℂ) 1) × MatedCRT.Field => circleAvg x.2 r z :=
    (measurable_circleAvg_left r z).comp measurable_snd
  exact (h1.prodMk h2).prodMk (h3.prodMk h4)

/-- The A.3 local observation is read from the disk restriction when the window and the averaging
disk lie inside the unit disk. -/
lemma p48o_localObs_eq_Λ {ℓ r : ℝ} (hr : 0 < r) {z : ℂ}
    (hball : ballO z ℓ ≤ ballO (0 : ℂ) 1) (hcirc : closedBall z r ⊆ (ballO (0 : ℂ) 1 : Set ℂ))
    {Ω' : Type} [MeasurableSpace Ω'] (h g : Ω' → DistC) (ω : Ω') :
    GMS4.prop48LocalFieldObservation h g ℓ r z ω =
      p48oΛ ℓ r z (restrictTo (ballO 0 1) (h ω), g ω) := by
  simp only [GMS4.prop48LocalFieldObservation, GMS4.prop48CircleAverageObservation, p48oΛ,
    MoTPort.IG.GFFAbsCont.resOn_restrictTo hball, GMS4c.localCircleProcess_restrictTo,
    MatedCRT.restrictCircles, ite_eq_left (And.intro hr hcirc)]

/-- **Transport along the disk law**: any Borel functional of `(h|_𝔻, hIG₀, U)` has the same law
for the zero-cone field and for the whole-plane field. -/
lemma p48o_map_disk_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {β : Type*} [MeasurableSpace β]
    {Ψ : DistOn (ballO (0 : ℂ) 1) × (MatedCRT.Field × ℝ) → β} (hΨ : Measurable Ψ) :
    P.map (fun ω => Ψ (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω), (hIG₀ ω, U ω))) =
      P.map (fun ω => Ψ (restrictTo (ballO 0 1) (p48oWPField X₀ ω), (hIG₀ ω, U ω))) := by
  have := D.isProbabilityMeasure
  have hU : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif
      (IGLaw.period_pos_of_uniform D.igField.2.1) D.igField.2.1
  have hIG : AEMeasurable (fun ω => (hIG₀ ω, U ω)) P :=
    D.igField.1.1.measurable.aemeasurable.prodMk hU
  have h0 : AEMeasurable (fun ω => (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω),
      (hIG₀ ω, U ω))) P :=
    ((measurable_restrictTo _).comp_aemeasurable (GMS4.aemeasurable_prop48ZeroConeField D)).prodMk
      hIG
  have h1 : AEMeasurable (fun ω => (restrictTo (ballO 0 1) (p48oWPField X₀ ω),
      (hIG₀ ω, U ω))) P :=
    (((measurable_restrictTo _).comp (p48o_wp_isNormalized D).1.measurable).aemeasurable).prodMk
      hIG
  have e0 : (fun ω => Ψ (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω), (hIG₀ ω, U ω))) =
      Ψ ∘ fun ω => (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω), (hIG₀ ω, U ω)) := rfl
  have e1 : (fun ω => Ψ (restrictTo (ballO 0 1) (p48oWPField X₀ ω), (hIG₀ ω, U ω))) =
      Ψ ∘ fun ω => (restrictTo (ballO 0 1) (p48oWPField X₀ ω), (hIG₀ ω, U ω)) := rfl
  rw [e0, e1, ← AEMeasurable.map_map_of_aemeasurable hΨ.aemeasurable h0,
    ← AEMeasurable.map_map_of_aemeasurable hΨ.aemeasurable h1, p48o_disk_law D hγ]

lemma p48o_aemeasurable_diskData
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    AEMeasurable (fun ω => (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω),
      (hIG₀ ω, U ω))) P := by
  have := D.isProbabilityMeasure
  have hU : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif
      (IGLaw.period_pos_of_uniform D.igField.2.1) D.igField.2.1
  exact ((measurable_restrictTo _).comp_aemeasurable (GMS4.aemeasurable_prop48ZeroConeField D)).prodMk
    (D.igField.1.1.measurable.aemeasurable.prodMk hU)

lemma p48o_aemeasurable_diskDataWP
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    AEMeasurable (fun ω => (restrictTo (ballO 0 1) (p48oWPField X₀ ω), (hIG₀ ω, U ω))) P := by
  have := D.isProbabilityMeasure
  have hU : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif
      (IGLaw.period_pos_of_uniform D.igField.2.1) D.igField.2.1
  exact (((measurable_restrictTo _).comp (p48o_wp_isNormalized D).1.measurable).aemeasurable).prodMk
    (D.igField.1.1.measurable.aemeasurable.prodMk hU)

/-- Integrals of Borel functionals of the disk data agree in the two models. -/
lemma p48o_integral_disk_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {Ψ : DistOn (ballO (0 : ℂ) 1) × (MatedCRT.Field × ℝ) → ℝ} (hΨ : Measurable Ψ) :
    ∫ ω, Ψ (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω), (hIG₀ ω, U ω)) ∂P =
      ∫ ω, Ψ (restrictTo (ballO 0 1) (p48oWPField X₀ ω), (hIG₀ ω, U ω)) ∂P := by
  have h0 : AEMeasurable (fun ω => Ψ (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω),
      (hIG₀ ω, U ω))) P := hΨ.comp_aemeasurable (p48o_aemeasurable_diskData D)
  have h1 : AEMeasurable (fun ω => Ψ (restrictTo (ballO 0 1) (p48oWPField X₀ ω),
      (hIG₀ ω, U ω))) P := hΨ.comp_aemeasurable (p48o_aemeasurable_diskDataWP D)
  have e0 : ∫ ω, Ψ (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω), (hIG₀ ω, U ω)) ∂P =
      ∫ y, y ∂(P.map fun ω => Ψ (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω),
        (hIG₀ ω, U ω))) :=
    (integral_map (f := fun y : ℝ => y) h0 aestronglyMeasurable_id).symm
  have e1 : ∫ ω, Ψ (restrictTo (ballO 0 1) (p48oWPField X₀ ω), (hIG₀ ω, U ω)) ∂P =
      ∫ y, y ∂(P.map fun ω => Ψ (restrictTo (ballO 0 1) (p48oWPField X₀ ω), (hIG₀ ω, U ω))) :=
    (integral_map (f := fun y : ℝ => y) h1 aestronglyMeasurable_id).symm
  rw [e0, e1, p48o_map_disk_eq D hγ hΨ]

/-- **Single-centre transport.** The triple and the factor value have, in the whole-plane model, the
joint law of the zero-cone kernel fibre; in particular the same lower moments. -/
lemma p48o_centre_transport
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [IsProbabilityMeasure P] {ε : ℝ} (hε : 0 ≤ ε) (q ζ : ℝ) {z : ℂ}
    {ℓ : ℝ} (hr : 0 < MatedCRTHarmonic.Canon.conditioningRadius ε q ζ)
    (hball : ballO z ℓ ≤ ballO (0 : ℂ) 1)
    (hcirc : closedBall z (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) ⊆
      (ballO (0 : ℂ) 1 : Set ℂ))
    {fz : ((DistOn (ballO z ℓ) × DistOn (ballO z ℓ)) × (ℝ × ℝ)) × ℝ → ℝ} (hfz : Measurable fz)
    (hfac : maskedUStarPrime D hγ ε q ζ z =ᵐ[P] fun ω => fz (GMS4.prop48LocalFieldObservation
      (p48oZeroField γ X₀ B₀ B₀') hIG₀ ℓ (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ)
        z ω, U ω)) :
    P.map (fun ω => ((GMS4.prop48CircleAverageObservation (p48oWPField X₀) hIG₀
        (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z ω, phaseVersion D hγ ω),
      fz (GMS4.prop48LocalFieldObservation (p48oWPField X₀) hIG₀ ℓ
        (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z ω, phaseVersion D hγ ω))) =
      p48oPairKernelG P (p48oTripleObsVersion D hγ ε q ζ) (p48oMaskedVersion D hγ ε q ζ) z := by
  set r := MatedCRTHarmonic.Canon.conditioningRadius ε q ζ with hrdef
  set Ψ₁ : DistOn (ballO (0 : ℂ) 1) × (MatedCRT.Field × ℝ) → ((ℝ × ℝ) × ℝ) × ℝ := fun x =>
    (((p48oΛ ℓ r z (x.1, x.2.1)).2, x.2.2), fz (p48oΛ ℓ r z (x.1, x.2.1), x.2.2)) with hΨ₁
  have hΛ := measurable_p48oΛ ℓ r z
  have hΨ₁m : Measurable Ψ₁ := by
    have hx : Measurable fun x : DistOn (ballO (0 : ℂ) 1) × (MatedCRT.Field × ℝ) =>
        p48oΛ ℓ r z (x.1, x.2.1) := hΛ.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    exact ((measurable_snd.comp hx).prodMk (measurable_snd.comp measurable_snd)).prodMk
      (hfz.comp (hx.prodMk (measurable_snd.comp measurable_snd)))
  have hTj := measurable_p48oTripleObsVersion D hγ ε q ζ
  have hXj := measurable_p48oMaskedVersion D hγ hε q ζ
  rw [p48oPairKernelG_apply P hTj hXj z]
  have hcan : (fun ω => (p48oTripleObsVersion D hγ ε q ζ ω z, p48oMaskedVersion D hγ ε q ζ ω z))
      =ᵐ[P] fun ω => Ψ₁ (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω), (hIG₀ ω, U ω)) := by
    filter_upwards [p48o_ae_versions_eq D hγ, p48o_ae_maskedVersion_eq D hγ ε q ζ,
      ae_maskedUStarPrime_eq_masked_fixed D hγ ε q ζ z, hfac] with ω hv hm hpm hf
    simp only [hΨ₁, ← p48o_localObs_eq_Λ hr hball hcirc]
    refine Prod.ext ?_ ?_
    · simp only [p48oTripleObsVersion, hv.1, hv.2]
      rfl
    · simp only
      rw [hm z, ← hpm, hf]
  have hwp : (fun ω => ((GMS4.prop48CircleAverageObservation (p48oWPField X₀) hIG₀ r z ω,
        phaseVersion D hγ ω),
      fz (GMS4.prop48LocalFieldObservation (p48oWPField X₀) hIG₀ ℓ r z ω, phaseVersion D hγ ω)))
      =ᵐ[P] fun ω => Ψ₁ (restrictTo (ballO 0 1) (p48oWPField X₀ ω), (hIG₀ ω, U ω)) := by
    filter_upwards [ae_phaseVersion_eq D hγ] with ω hω
    simp only [hΨ₁, ← p48o_localObs_eq_Λ hr hball hcirc, hω]
    rfl
  rw [Measure.map_congr hwp, Measure.map_congr hcan]
  exact (p48o_map_disk_eq D hγ hΨ₁m).symm

/-- **Covariance transport.** The zero-cone centred covariance equals the whole-plane covariance of
The transported factors, centred by the same kernel function. -/
lemma p48o_cov_transport
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [IsProbabilityMeasure P] {ε : ℝ} (q ζ : ℝ) {z w : ℂ}
    {ℓ : ℝ} (hr : 0 < MatedCRTHarmonic.Canon.conditioningRadius ε q ζ)
    (hballz : ballO z ℓ ≤ ballO (0 : ℂ) 1)
    (hcircz : closedBall z (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) ⊆
      (ballO (0 : ℂ) 1 : Set ℂ))
    (hballw : ballO w ℓ ≤ ballO (0 : ℂ) 1)
    (hcircw : closedBall w (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) ⊆
      (ballO (0 : ℂ) 1 : Set ℂ))
    {fz : ((DistOn (ballO z ℓ) × DistOn (ballO z ℓ)) × (ℝ × ℝ)) × ℝ → ℝ}
    {fw : ((DistOn (ballO w ℓ) × DistOn (ballO w ℓ)) × (ℝ × ℝ)) × ℝ → ℝ}
    (hfz : Measurable fz) (hfw : Measurable fw)
    (hfacz : maskedUStarPrime D hγ ε q ζ z =ᵐ[P] fun ω => fz (GMS4.prop48LocalFieldObservation
      (p48oZeroField γ X₀ B₀ B₀') hIG₀ ℓ (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ)
        z ω, U ω))
    (hfacw : maskedUStarPrime D hγ ε q ζ w =ᵐ[P] fun ω => fw (GMS4.prop48LocalFieldObservation
      (p48oZeroField γ X₀ B₀ B₀') hIG₀ ℓ (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ)
        w ω, U ω)) :
    ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanTriple D hγ ε q ζ ω z) *
        (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanTriple D hγ ε q ζ ω w) ∂P =
      ∫ ω, (fz (GMS4.prop48LocalFieldObservation (p48oWPField X₀) hIG₀ ℓ
            (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z ω, phaseVersion D hγ ω) -
          p48oCondValueG P (p48oTripleObsVersion D hγ ε q ζ) (p48oMaskedVersion D hγ ε q ζ)
            (z, (GMS4.prop48CircleAverageObservation (p48oWPField X₀) hIG₀
              (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z ω, phaseVersion D hγ ω))) *
        (fw (GMS4.prop48LocalFieldObservation (p48oWPField X₀) hIG₀ ℓ
            (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) w ω, phaseVersion D hγ ω) -
          p48oCondValueG P (p48oTripleObsVersion D hγ ε q ζ) (p48oMaskedVersion D hγ ε q ζ)
            (w, (GMS4.prop48CircleAverageObservation (p48oWPField X₀) hIG₀
              (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) w ω, phaseVersion D hγ ω))) ∂P := by
  set r := MatedCRTHarmonic.Canon.conditioningRadius ε q ζ with hrdef
  set G := p48oCondValueG P (p48oTripleObsVersion D hγ ε q ζ) (p48oMaskedVersion D hγ ε q ζ)
    with hGdef
  have hGm : Measurable G := measurable_p48oCondValueG P _ _
  have hΛz := measurable_p48oΛ ℓ r z
  have hΛw := measurable_p48oΛ ℓ r w
  set Ψ : DistOn (ballO (0 : ℂ) 1) × (MatedCRT.Field × ℝ) → ℝ := fun x =>
    (fz (p48oΛ ℓ r z (x.1, x.2.1), x.2.2) - G (z, ((p48oΛ ℓ r z (x.1, x.2.1)).2, x.2.2))) *
    (fw (p48oΛ ℓ r w (x.1, x.2.1), x.2.2) - G (w, ((p48oΛ ℓ r w (x.1, x.2.1)).2, x.2.2)))
    with hΨdef
  have hx : Measurable fun x : DistOn (ballO (0 : ℂ) 1) × (MatedCRT.Field × ℝ) => (x.1, x.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hu : Measurable fun x : DistOn (ballO (0 : ℂ) 1) × (MatedCRT.Field × ℝ) => x.2.2 :=
    measurable_snd.comp measurable_snd
  have hΨm : Measurable Ψ := by
    have h1 := hfz.comp ((hΛz.comp hx).prodMk hu)
    have h2 := hGm.comp ((measurable_const (a := z)).prodMk
      ((measurable_snd.comp (hΛz.comp hx)).prodMk hu))
    have h3 := hfw.comp ((hΛw.comp hx).prodMk hu)
    have h4 := hGm.comp ((measurable_const (a := w)).prodMk
      ((measurable_snd.comp (hΛw.comp hx)).prodMk hu))
    have h := (h1.sub h2).mul (h3.sub h4)
    exact h
  have e0 : ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanTriple D hγ ε q ζ ω z) *
      (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanTriple D hγ ε q ζ ω w) ∂P =
      ∫ ω, Ψ (restrictTo (ballO 0 1) (p48oZeroField γ X₀ B₀ B₀' ω), (hIG₀ ω, U ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [p48o_ae_versions_eq D hγ, hfacz, hfacw] with ω hv hz hw
    simp only [hΨdef, ← p48o_localObs_eq_Λ hr hballz hcircz, ← p48o_localObs_eq_Λ hr hballw hcircw]
    rw [hz, hw]
    simp only [p48oCondMeanTriple, p48oTripleObsVersion, hv.1, hv.2]
    rfl
  have e1 : ∫ ω, Ψ (restrictTo (ballO 0 1) (p48oWPField X₀ ω), (hIG₀ ω, U ω)) ∂P =
      ∫ ω, (fz (GMS4.prop48LocalFieldObservation (p48oWPField X₀) hIG₀ ℓ r z ω,
            phaseVersion D hγ ω) -
          G (z, (GMS4.prop48CircleAverageObservation (p48oWPField X₀) hIG₀ r z ω,
            phaseVersion D hγ ω))) *
        (fw (GMS4.prop48LocalFieldObservation (p48oWPField X₀) hIG₀ ℓ r w ω,
            phaseVersion D hγ ω) -
          G (w, (GMS4.prop48CircleAverageObservation (p48oWPField X₀) hIG₀ r w ω,
            phaseVersion D hγ ω))) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [ae_phaseVersion_eq D hγ] with ω hω
    simp only [hΨdef, ← p48o_localObs_eq_Λ hr hballz hcircz, ← p48o_localObs_eq_Λ hr hballw hcircw,
      hω]
    rfl
  rw [e0, p48o_integral_disk_eq D hγ hΨm, e1]

/-! ### The rate -/

lemma p48o_exp_neg_le_factorial {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Real.exp (-y) ≤ (n.factorial : ℝ) * (1 / y) ^ n := by
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hyn : 0 < y ^ n := pow_pos hy n
  have hexp := Real.exp_pos y
  have h := Real.pow_div_factorial_le_exp y hy.le n
  rw [Real.exp_neg, one_div_pow, mul_one_div, inv_le_comm₀ hexp (div_pos hfac hyn), inv_div]
  exact h

/-- The real arithmetic turning the integrated A.3 bound into the source rate `ε^ζ` ([18] (4.36)). -/
lemma p48o_far_rate_arith {ε ζ p p₀ q' C3 Kp K₀ Kq b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hζ : 0 < ζ) (hp : 1 ≤ p) (hpp₀ : p < p₀) (hq' : 1 < q') (hC3 : 0 ≤ C3) (hKp : 0 ≤ Kp)
    (hK₀ : 0 ≤ K₀) (hKq : 0 ≤ Kq) (hb : 0 < b) :
    (C3 * ((8 * ε ^ (4 * ζ)) ^ ((1 / 2 : ℝ) * p) * Kp +
        Real.exp (-(b / (8 * ε ^ (4 * ζ)) ^ ((1 : ℝ) - 1 / 2))) * K₀ ^ (p / p₀))) ^ (1 / p) *
      (2 ^ q' * ε ^ (-(q' * ζ)) * Kq) ^ (1 / q') ≤
    (C3 * (8 ^ (p / 2) * Kp + ((Nat.ceil p).factorial : ℝ) * (8 ^ (1 / 2 : ℝ) / b) ^ Nat.ceil p *
        K₀ ^ (p / p₀))) ^ (1 / p) * (2 ^ q' * Kq) ^ (1 / q') * ε ^ ζ := by
  have hp0 : 0 < p := one_pos.trans_le hp
  have hq0 : 0 < q' := one_pos.trans hq'
  set n : ℕ := Nat.ceil p with hn
  have hnp : p ≤ n := Nat.le_ceil p
  have he4 : 0 < ε ^ (4 * ζ) := Real.rpow_pos_of_pos hε _
  have h8 : (0 : ℝ) < 8 := by norm_num
  -- δ^{p/2} = 8^{p/2} ε^{2ζp}
  have hδp : (8 * ε ^ (4 * ζ)) ^ ((1 / 2 : ℝ) * p) = 8 ^ (p / 2) * ε ^ (2 * ζ * p) := by
    rw [Real.mul_rpow h8.le he4.le, ← Real.rpow_mul hε.le]
    congr 1
    · congr 1; ring
    · congr 1; ring
  -- δ^{1/2} = 8^{1/2} ε^{2ζ}
  have hδh : (8 * ε ^ (4 * ζ)) ^ ((1 : ℝ) - 1 / 2) = 8 ^ (1 / 2 : ℝ) * ε ^ (2 * ζ) := by
    rw [Real.mul_rpow h8.le he4.le, ← Real.rpow_mul hε.le]
    congr 1
    · norm_num
    · congr 1; ring
  have h8h : (0 : ℝ) < 8 ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos h8 _
  have he2 : 0 < ε ^ (2 * ζ) := Real.rpow_pos_of_pos hε _
  have hy : 0 < b / (8 ^ (1 / 2 : ℝ) * ε ^ (2 * ζ)) := div_pos hb (mul_pos h8h he2)
  have hexp := p48o_exp_neg_le_factorial hy n
  have hexp' : Real.exp (-(b / (8 * ε ^ (4 * ζ)) ^ ((1 : ℝ) - 1 / 2))) ≤
      (n.factorial : ℝ) * (8 ^ (1 / 2 : ℝ) / b) ^ n * ε ^ (2 * ζ * p) := by
    rw [hδh]
    refine hexp.trans ?_
    have hpow : (ε ^ (2 * ζ)) ^ n ≤ ε ^ (2 * ζ * p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by nlinarith)
    have hfac : (0 : ℝ) ≤ n.factorial := by exact_mod_cast (Nat.factorial_pos n).le
    rw [one_div_div, show 8 ^ (1 / 2 : ℝ) * ε ^ (2 * ζ) / b = (8 ^ (1 / 2 : ℝ) / b) * ε ^ (2 * ζ)
      by ring, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hfac (pow_nonneg (div_pos h8h hb).le n))
  set M : ℝ := C3 * (8 ^ (p / 2) * Kp + (n.factorial : ℝ) * (8 ^ (1 / 2 : ℝ) / b) ^ n *
    K₀ ^ (p / p₀)) with hM
  have hM0 : 0 ≤ M := by
    have : (0 : ℝ) ≤ n.factorial := by exact_mod_cast (Nat.factorial_pos n).le
    positivity
  have hK₀θ : 0 ≤ K₀ ^ (p / p₀) := Real.rpow_nonneg hK₀ _
  have hinner : C3 * ((8 * ε ^ (4 * ζ)) ^ ((1 / 2 : ℝ) * p) * Kp +
      Real.exp (-(b / (8 * ε ^ (4 * ζ)) ^ ((1 : ℝ) - 1 / 2))) * K₀ ^ (p / p₀)) ≤
      M * ε ^ (2 * ζ * p) := by
    rw [hδp, hM]
    have hep : 0 ≤ ε ^ (2 * ζ * p) := Real.rpow_nonneg hε.le _
    have h1 : Real.exp (-(b / (8 * ε ^ (4 * ζ)) ^ ((1 : ℝ) - 1 / 2))) * K₀ ^ (p / p₀) ≤
        (n.factorial : ℝ) * (8 ^ (1 / 2 : ℝ) / b) ^ n * ε ^ (2 * ζ * p) * K₀ ^ (p / p₀) :=
      mul_le_mul_of_nonneg_right hexp' hK₀θ
    calc C3 * (8 ^ (p / 2) * ε ^ (2 * ζ * p) * Kp +
          Real.exp (-(b / (8 * ε ^ (4 * ζ)) ^ ((1 : ℝ) - 1 / 2))) * K₀ ^ (p / p₀))
        ≤ C3 * (8 ^ (p / 2) * ε ^ (2 * ζ * p) * Kp +
          (n.factorial : ℝ) * (8 ^ (1 / 2 : ℝ) / b) ^ n * ε ^ (2 * ζ * p) * K₀ ^ (p / p₀)) := by
          gcongr
      _ = C3 * (8 ^ (p / 2) * Kp + (n.factorial : ℝ) * (8 ^ (1 / 2 : ℝ) / b) ^ n *
          K₀ ^ (p / p₀)) * ε ^ (2 * ζ * p) := by ring
  have hinner0 : 0 ≤ C3 * ((8 * ε ^ (4 * ζ)) ^ ((1 / 2 : ℝ) * p) * Kp +
      Real.exp (-(b / (8 * ε ^ (4 * ζ)) ^ ((1 : ℝ) - 1 / 2))) * K₀ ^ (p / p₀)) := by
    have : 0 ≤ (8 * ε ^ (4 * ζ)) ^ ((1 / 2 : ℝ) * p) := Real.rpow_nonneg (by positivity) _
    positivity
  have hfirst : (C3 * ((8 * ε ^ (4 * ζ)) ^ ((1 / 2 : ℝ) * p) * Kp +
      Real.exp (-(b / (8 * ε ^ (4 * ζ)) ^ ((1 : ℝ) - 1 / 2))) * K₀ ^ (p / p₀))) ^ (1 / p) ≤
      M ^ (1 / p) * ε ^ (2 * ζ) := by
    refine (Real.rpow_le_rpow hinner0 hinner (by positivity)).trans (le_of_eq ?_)
    rw [Real.mul_rpow hM0 (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le]
    congr 2
    field_simp
  have hsecond : (2 ^ q' * ε ^ (-(q' * ζ)) * Kq) ^ (1 / q') =
      (2 ^ q' * Kq) ^ (1 / q') * ε ^ (-ζ) := by
    have h2 : (0 : ℝ) ≤ 2 ^ q' := Real.rpow_nonneg (by norm_num) _
    have he : 0 ≤ ε ^ (-(q' * ζ)) := Real.rpow_nonneg hε.le _
    rw [show 2 ^ q' * ε ^ (-(q' * ζ)) * Kq = (2 ^ q' * Kq) * ε ^ (-(q' * ζ)) by ring,
      Real.mul_rpow (mul_nonneg h2 hKq) he, ← Real.rpow_mul hε.le]
    congr 2
    field_simp
  rw [hsecond]
  have hsec0 : 0 ≤ (2 ^ q' * Kq) ^ (1 / q') :=
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKq) _
  calc (C3 * ((8 * ε ^ (4 * ζ)) ^ ((1 / 2 : ℝ) * p) * Kp +
        Real.exp (-(b / (8 * ε ^ (4 * ζ)) ^ ((1 : ℝ) - 1 / 2))) * K₀ ^ (p / p₀))) ^ (1 / p) *
        ((2 ^ q' * Kq) ^ (1 / q') * ε ^ (-ζ))
      ≤ (M ^ (1 / p) * ε ^ (2 * ζ)) * ((2 ^ q' * Kq) ^ (1 / q') * ε ^ (-ζ)) :=
        mul_le_mul_of_nonneg_right hfirst
          (mul_nonneg hsec0 (Real.rpow_nonneg hε.le _))
    _ = M ^ (1 / p) * (2 ^ q' * Kq) ^ (1 / q') * (ε ^ (2 * ζ) * ε ^ (-ζ)) := by ring
    _ = M ^ (1 / p) * (2 ^ q' * Kq) ^ (1 / q') * ε ^ ζ := by
        rw [← Real.rpow_add hε]
        congr 2
        ring

lemma p48o_lintegral_snd_of_map_eq {β : Type*} [MeasurableSpace β] {Ω' : Type*}
    [MeasurableSpace Ω'] {μ : Measure Ω'} {A B : Ω' → β × ℝ} (hA : Measurable A)
    (hB : Measurable B) (h : μ.map A = μ.map B) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (A ω).2 ∂μ = ∫⁻ ω, g (B ω).2 ∂μ := by
  have e1 : ∫⁻ ω, g (A ω).2 ∂μ = ∫⁻ x, g x.2 ∂(μ.map A) :=
    (lintegral_map (f := fun x : β × ℝ => g x.2) (hg.comp measurable_snd) hA).symm
  have e2 : ∫⁻ ω, g (B ω).2 ∂μ = ∫⁻ x, g x.2 ∂(μ.map B) :=
    (lintegral_map (f := fun x : β × ℝ => g x.2) (hg.comp measurable_snd) hB).symm
  rw [e1, e2, h]

/-- The degree cap turns the area moments of Lemma 4.9 into moments of the masked density of any
order. -/
lemma p48o_lintegral_maskedUStar_rpow_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) (q ζ : ℝ) (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal |maskedUStar D hγ ε q ζ z ω| ^ t ∂P ≤
      ENNReal.ofReal (ε ^ (-ζ)) ^ t *
        ∫⁻ ω, ENNReal.ofReal |maskedAreaRatio D hγ ε q ζ z ω| ^ t ∂P := by
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg ht ENNReal.ofReal_ne_top)]
  refine lintegral_mono fun ω => ?_
  rw [← ENNReal.mul_rpow_of_nonneg _ _ ht]
  refine ENNReal.rpow_le_rpow ?_ ht
  rw [abs_of_nonneg (maskedUStar_nonneg D hγ ε q ζ z ω),
    abs_of_nonneg (maskedAreaRatio_nonneg D hγ ε q ζ z ω),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hε _)]
  exact ENNReal.ofReal_le_ofReal (maskedUStar_le_areaRatio D hγ ε q ζ hε z ω)

/-! ### The canonical far-pair estimate -/

lemma p48o_a3aN_pos {p p₀ : ℝ} : 0 < GMSAppA.a3aN p p₀ 2 := by
  unfold GMSAppA.a3aN GMSAppA.a3AN
  refine lt_min (by norm_num) (div_pos (div_pos (GMSAppA.a3A_pos p p₀) ?_) ?_)
  · exact Real.sqrt_pos.2 (by norm_num)
  · exact lt_max_of_lt_left one_pos

lemma p48o_a3bN_pos {p p₀ : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) : 0 < GMSAppA.a3bN p p₀ 2 := by
  have hp0 : 0 < p := one_pos.trans_le hp
  have hp₀ : 0 < p₀ := hp0.trans hpp₀
  unfold GMSAppA.a3bN GMSAppA.cplExp GMSAppA.a3AN
  have h1 : 0 < p * (p₀ / (p₀ - p)) := mul_pos hp0 (div_pos hp₀ (by linarith))
  have h2 : 0 < 1 - 1 / p₀ := by
    rw [sub_pos, div_lt_one hp₀]; linarith
  have h3 : 0 < 1 - p / p₀ := by
    rw [sub_pos, div_lt_one hp₀]; exact hpp₀
  have h4 : 0 < GMSAppA.a3A p p₀ / Real.sqrt (2 : ℕ) :=
    div_pos (GMSAppA.a3A_pos p p₀) (Real.sqrt_pos.2 (by norm_num))
  positivity

set_option maxHeartbeats 1000000 in
/-- **[18] (4.35)–(4.37) on the canonical zero-cone coupling, with the conditional mean.**
For every radius there are `C, ε₀` such that, for `ε ≤ ε₀` and centres of `B_ρ(0)` farther apart
than `2 ε^(q−4ζ)`, the centred triple covariance is at most `C ε^ζ`. -/
theorem p48o_canonical_far_pair
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (H2 : ThickGMCReaders D) {q ζ : ℝ} (hζ : 0 < ζ)
    (hζq : 4 * ζ < q)
    (H1 : ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 → Lemma49ConditionalMoments D hγ q ζ ρ) :
    ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      ∀ z ∈ ball (0 : ℂ) ρ, ∀ w ∈ ball (0 : ℂ) ρ, 2 * ε ^ (q - 4 * ζ) < dist z w →
        ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanTriple D hγ ε q ζ ω z) *
          (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanTriple D hγ ε q ζ ω w) ∂P ≤
            C * ε ^ ζ := by
  intro ρ hρ
  haveI := D.isProbabilityMeasure
  set H := H1 ρ hρ with hH
  -- exponents
  have hγsq : 0 < γ ^ 2 := by have := hγ.1; positivity
  have hγ4 : (1 : ℝ) < 4 / γ ^ 2 := by
    rw [lt_div_iff₀ hγsq]; nlinarith [hγ.1, hγ.2]
  set p₀ : ℝ := (1 + 4 / γ ^ 2) / 2 with hp₀def
  have hp₀1 : 1 < p₀ := by rw [hp₀def]; linarith
  have hp₀γ : p₀ < 4 / γ ^ 2 := by rw [hp₀def]; linarith
  set p : ℝ := (1 + p₀) / 2 with hpdef
  have hp1 : 1 < p := by rw [hpdef]; linarith
  have hpp₀ : p < p₀ := by rw [hpdef]; linarith
  set q' : ℝ := Real.conjExponent p with hq'def
  have hpq : p.HolderConjugate q' := Real.HolderConjugate.conjExponent hp1
  have hq'1 : 1 < q' := hpq.symm.lt
  have hp0 : 0 < p := one_pos.trans hp1
  have hq'0 : 0 < q' := one_pos.trans hq'1
  -- moments from Lemma 4.9
  obtain ⟨K₀, hK₀, hmom₀⟩ := H.density_lintegral_le p₀ hp₀1 hp₀γ
  obtain ⟨Kp, hKp, hmomp⟩ := H.density_lintegral_le p hp1 (hpp₀.trans hp₀γ)
  obtain ⟨Kq, hKq, hmomq⟩ := H.area_lintegral_le q' hq'1.le
  -- A.3 constants
  set C3 : ℝ := GMSAppA.a3C p p₀ with hC3def
  have hC3 : 0 ≤ C3 := by rw [hC3def, GMSAppA.a3C]; positivity
  set b : ℝ := GMSAppA.a3bN p p₀ 2 with hbdef
  have hb : 0 < b := p48o_a3bN_pos hp1.le hpp₀
  have ha3 : 0 < GMSAppA.a3aN p p₀ 2 := p48o_a3aN_pos
  set n : ℕ := Nat.ceil p with hn
  set Cf : ℝ := (C3 * (8 ^ (p / 2) * Kp + (n.factorial : ℝ) * (8 ^ (1 / 2 : ℝ) / b) ^ n *
    K₀ ^ (p / p₀))) ^ (1 / p) * (2 ^ q' * Kq) ^ (1 / q') with hCfdef
  have hCf : 0 ≤ Cf := by
    have : (0 : ℝ) ≤ n.factorial := by exact_mod_cast (Nat.factorial_pos n).le
    have h8 : (0 : ℝ) ≤ 8 ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
    have hK₀θ : 0 ≤ K₀ ^ (p / p₀) := Real.rpow_nonneg hK₀ _
    have h2 : (0 : ℝ) ≤ 2 ^ q' := Real.rpow_nonneg (by norm_num) _
    have h8p : (0 : ℝ) ≤ 8 ^ (p / 2) := Real.rpow_nonneg (by norm_num) _
    rw [hCfdef]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  refine ⟨Cf, hCf, ?_⟩
  -- the mesh range
  set c : ℝ := min 1 (GMSAppA.a3aN p p₀ 2) with hcdef
  have hc : 0 < c := lt_min one_pos ha3
  have hqζ : 0 < q - 4 * ζ := by linarith
  have h4ζ : 0 < 4 * ζ := by linarith
  set ε₁ : ℝ := (c / 8) ^ (1 / (4 * ζ)) with hε₁def
  set ε₂ : ℝ := ((1 - ρ) / 2) ^ (1 / (q - 4 * ζ)) with hε₂def
  have hε₁0 : 0 < ε₁ := Real.rpow_pos_of_pos (by positivity) _
  have hρ2 : 0 < (1 - ρ) / 2 := by linarith [hρ.2]
  have hε₂0 : 0 < ε₂ := Real.rpow_pos_of_pos hρ2 _
  have hε₂1 : ε₂ < 1 :=
    Real.rpow_lt_one hρ2.le (by linarith [hρ.1]) (by positivity)
  refine ⟨min H.epsilonStar (min ε₁ ε₂), lt_min H.epsilonStar_pos (lt_min hε₁0 hε₂0), ?_⟩
  intro ε hε z hz w hw hfar
  have hε0 : 0 < ε := hε.1
  have hεstar : ε ≤ H.epsilonStar := hε.2.trans (min_le_left _ _)
  have hε₁ : ε ≤ ε₁ := hε.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₂ : ε ≤ ε₂ := hε.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := hεstar.trans H.epsilonStar_le_one
  have hεlt1 : ε < 1 := hε₂.trans_lt hε₂1
  set r : ℝ := MatedCRTHarmonic.Canon.conditioningRadius ε q ζ with hrdef
  have hreq : r = ε ^ (q - 4 * ζ) := rfl
  have hr : 0 < r := Real.rpow_pos_of_pos hε0 _
  have hr2 : r ≤ (1 - ρ) / 2 := by
    rw [hreq]
    calc ε ^ (q - 4 * ζ) ≤ ε₂ ^ (q - 4 * ζ) := Real.rpow_le_rpow hε0.le hε₂ hqζ.le
      _ = (1 - ρ) / 2 := by
        rw [hε₂def, ← Real.rpow_mul hρ2.le, one_div_mul_cancel hqζ.ne', Real.rpow_one]
  set δ : ℝ := 8 * ε ^ (4 * ζ) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hε0 _)
  have hδc : δ ≤ c := by
    have h1 : ε ^ (4 * ζ) ≤ ε₁ ^ (4 * ζ) := Real.rpow_le_rpow hε0.le hε₁ h4ζ.le
    have h2 : ε₁ ^ (4 * ζ) = c / 8 := by
      rw [hε₁def, ← Real.rpow_mul (by positivity), one_div_mul_cancel h4ζ.ne', Real.rpow_one]
    rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 := hδc.trans (min_le_left _ _)
  have hδa : δ ≤ GMSAppA.a3aN p p₀ 2 := hδc.trans (min_le_right _ _)
  have hrδ : r * δ = 8 * ε ^ q := by
    rw [hreq, hδdef, mul_left_comm, ← Real.rpow_add hε0]
    congr 2
    ring
  have hℓ : 5 * ε ^ q ≤ r * δ := by
    rw [hrδ]; have := Real.rpow_pos_of_pos hε0 q; linarith
  have hrδ_le : r * δ ≤ r := mul_le_of_le_one_right hr.le hδ1
  have hzn : ‖z‖ < ρ := by simpa using hz
  have hwn : ‖w‖ < ρ := by simpa using hw
  have hsmallz : r + ‖z‖ < 1 := by linarith
  have hsmallw : r + ‖w‖ < 1 := by linarith
  have hcircz : closedBall z r ⊆ (ballO (0 : ℂ) 1 : Set ℂ) :=
    prop48_closedBall_subset_unitDisk hsmallz
  have hcircw : closedBall w r ⊆ (ballO (0 : ℂ) 1 : Set ℂ) :=
    prop48_closedBall_subset_unitDisk hsmallw
  have hballz : ballO z (r * δ) ≤ ballO (0 : ℂ) 1 := fun x hx =>
    hcircz (Metric.ball_subset_closedBall (Metric.ball_subset_ball hrδ_le hx))
  have hballw : ballO w (r * δ) ≤ ballO (0 : ℂ) 1 := fun x hx =>
    hcircw (Metric.ball_subset_closedBall (Metric.ball_subset_ball hrδ_le hx))
  -- local factors
  obtain ⟨fz, hfz, hfz0, hfacz⟩ := p48o_localFactor_A3 D hγ H2 ⟨hε0, hεlt1⟩ q ζ z hℓ
  obtain ⟨fw, hfw, hfw0, hfacw⟩ := p48o_localFactor_A3 D hγ H2 ⟨hε0, hεlt1⟩ q ζ w hℓ
  -- transport to the whole-plane model
  rw [p48o_cov_transport D hγ q ζ hr hballz hcircz hballw hcircw hfz hfw hfacz hfacw]
  set G := p48oCondValueG P (p48oTripleObsVersion D hγ ε q ζ) (p48oMaskedVersion D hγ ε q ζ)
    with hGdef
  have hlawz := p48o_centre_transport D hγ hε0.le q ζ hr hballz hcircz hfz hfacz
  have hlaww := p48o_centre_transport D hγ hε0.le q ζ hr hballw hcircw hfw hfacw
  have hWm : Measurable (p48oWPField X₀) := (p48o_wp_isNormalized D).1.measurable
  have hIGm : Measurable hIG₀ := D.igField.1.1.measurable
  have hU'm : Measurable (phaseVersion D hγ) := measurable_phaseVersion D hγ
  have hobsz := p48o_measurable_localObs hWm hIGm (r * δ) r z
  have hobsw := p48o_measurable_localObs hWm hIGm (r * δ) r w
  have hcz : Measurable (GMS4.prop48CircleAverageObservation (p48oWPField X₀) hIG₀ r z) :=
    measurable_snd.comp hobsz
  have hcw : Measurable (GMS4.prop48CircleAverageObservation (p48oWPField X₀) hIG₀ r w) :=
    measurable_snd.comp hobsw
  have hTz : Measurable fun ω =>
      (GMS4.prop48CircleAverageObservation (p48oWPField X₀) hIG₀ r z ω, phaseVersion D hγ ω) :=
    hcz.prodMk hU'm
  have hTw : Measurable fun ω =>
      (GMS4.prop48CircleAverageObservation (p48oWPField X₀) hIG₀ r w ω, phaseVersion D hγ ω) :=
    hcw.prodMk hU'm
  have hXzm : Measurable fun ω =>
      fz (GMS4.prop48LocalFieldObservation (p48oWPField X₀) hIG₀ (r * δ) r z ω,
        phaseVersion D hγ ω) := hfz.comp (hobsz.prodMk hU'm)
  have hXwm : Measurable fun ω =>
      fw (GMS4.prop48LocalFieldObservation (p48oWPField X₀) hIG₀ (r * δ) r w ω,
        phaseVersion D hγ ω) := hfw.comp (hobsw.prodMk hU'm)
  have hTj := measurable_p48oTripleObsVersion D hγ ε q ζ
  have hXj := measurable_p48oMaskedVersion D hγ hε0.le q ζ
  -- moment identities
  have hmomz : ∀ t : ℝ, ∫⁻ ω, ENNReal.ofReal |fz (GMS4.prop48LocalFieldObservation
      (p48oWPField X₀) hIG₀ (r * δ) r z ω, phaseVersion D hγ ω)| ^ t ∂P =
      ∫⁻ ω, ENNReal.ofReal |maskedUStar D hγ ε q ζ z ω| ^ t ∂P := by
    intro t
    have hg : Measurable fun x : ℝ => ENNReal.ofReal |x| ^ t :=
      (ENNReal.measurable_ofReal.comp measurable_id.abs).pow_const t
    have hB : Measurable fun ω => (p48oTripleObsVersion D hγ ε q ζ ω z,
        p48oMaskedVersion D hγ ε q ζ ω z) := by
      have h := hTj.prodMk hXj
      have h2 := h.comp (measurable_id.prodMk (measurable_const (a := z)) :
        Measurable fun ω : Ω => (ω, z))
      exact h2
    have h := p48o_lintegral_snd_of_map_eq (hTz.prodMk hXzm) hB
      (hlawz.trans (p48oPairKernelG_apply P hTj hXj z)) hg
    refine h.trans (lintegral_congr_ae ?_)
    filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ] with ω hω
    exact congrArg (fun x : ℝ => ENNReal.ofReal |x| ^ t) (hω z)
  have hmomw : ∀ t : ℝ, ∫⁻ ω, ENNReal.ofReal |fw (GMS4.prop48LocalFieldObservation
      (p48oWPField X₀) hIG₀ (r * δ) r w ω, phaseVersion D hγ ω)| ^ t ∂P =
      ∫⁻ ω, ENNReal.ofReal |maskedUStar D hγ ε q ζ w ω| ^ t ∂P := by
    intro t
    have hg : Measurable fun x : ℝ => ENNReal.ofReal |x| ^ t :=
      (ENNReal.measurable_ofReal.comp measurable_id.abs).pow_const t
    have hB : Measurable fun ω => (p48oTripleObsVersion D hγ ε q ζ ω w,
        p48oMaskedVersion D hγ ε q ζ ω w) := by
      have h := hTj.prodMk hXj
      have h2 := h.comp (measurable_id.prodMk (measurable_const (a := w)) :
        Measurable fun ω : Ω => (ω, w))
      exact h2
    have h := p48o_lintegral_snd_of_map_eq (hTw.prodMk hXwm) hB
      (hlaww.trans (p48oPairKernelG_apply P hTj hXj w)) hg
    refine h.trans (lintegral_congr_ae ?_)
    filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ] with ω hω
    exact congrArg (fun x : ℝ => ENNReal.ofReal |x| ^ t) (hω w)
  have hεI : ε ∈ Ioc (0 : ℝ) H.epsilonStar := ⟨hε0, hεstar⟩
  have hXz₀ : ∫⁻ ω, ENNReal.ofReal |fz (GMS4.prop48LocalFieldObservation
      (p48oWPField X₀) hIG₀ (r * δ) r z ω, phaseVersion D hγ ω)| ^ p₀ ∂P ≤ ENNReal.ofReal K₀ := by
    rw [hmomz]; exact hmom₀ ε hεI z hz
  have hXzp : ∫⁻ ω, ENNReal.ofReal |fz (GMS4.prop48LocalFieldObservation
      (p48oWPField X₀) hIG₀ (r * δ) r z ω, phaseVersion D hγ ω)| ^ p ∂P ≤ ENNReal.ofReal Kp := by
    rw [hmomz]; exact hmomp ε hεI z hz
  have hXwq : ∫⁻ ω, ENNReal.ofReal |fw (GMS4.prop48LocalFieldObservation
      (p48oWPField X₀) hIG₀ (r * δ) r w ω, phaseVersion D hγ ω)| ^ q' ∂P ≤
      ENNReal.ofReal (ε ^ (-(q' * ζ)) * Kq) := by
    rw [hmomw]
    refine (p48o_lintegral_maskedUStar_rpow_le D hγ hε0.le q ζ w hq'0.le).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hε0.le _) hq'0.le,
      ← Real.rpow_mul hε0.le, ENNReal.ofReal_mul (Real.rpow_nonneg hε0.le _)]
    have he : -ζ * q' = -(q' * ζ) := by ring
    rw [he]
    exact mul_le_mul' le_rfl (hmomq ε hεI w hw)
  -- the conditional means in the whole-plane model
  have hXzint : Integrable (fun ω => fz (GMS4.prop48LocalFieldObservation
      (p48oWPField X₀) hIG₀ (r * δ) r z ω, phaseVersion D hγ ω)) P :=
    p48o_integrable_of_lintegral_rpow hXzm.aestronglyMeasurable hp₀1.le
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hXz₀)
  have hXwint : Integrable (fun ω => fw (GMS4.prop48LocalFieldObservation
      (p48oWPField X₀) hIG₀ (r * δ) r w ω, phaseVersion D hγ ω)) P :=
    p48o_integrable_of_lintegral_rpow hXwm.aestronglyMeasurable hq'1.le
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hXwq)
  have hmz := p48o_condValueG_ae_eq_condExp_of_law P hTz hXzm z hlawz (fun ω => hfz0 _) hTz
    (ae_eq_refl _) hXzint (ae_eq_refl _)
  have hmw := p48o_condValueG_ae_eq_condExp_of_law P hTw hXwm w hlaww (fun ω => hfw0 _) hTw
    (ae_eq_refl _) hXwint (ae_eq_refl _)
  -- the frozen-phase A.3 bound
  have hA3 := p48o_far_pair_frozen_A3 (p48o_wp_isNormalized D) D.igField.1 (p48o_wp_indep_hIG D)
    hU'm (p48o_wp_pair_indep_phase D hγ) hr hδ hδ1 hsmallz hfar hp1.le hpp₀
    (by norm_num : (0 : ℝ) < 1 / 2) hδa hpq hfz hfw hfz0 hfw0 hmz hmw
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hXz₀)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hXwq)
  -- bound the centred `w` moment
  set Xw : Ω → ℝ := fun ω => fw (GMS4.prop48LocalFieldObservation (p48oWPField X₀) hIG₀ (r * δ) r
    w ω, phaseVersion D hγ ω) with hXwdef
  set mw : Ω → ℝ := fun ω => G (w, (GMS4.prop48CircleAverageObservation (p48oWPField X₀) hIG₀ r
    w ω, phaseVersion D hγ ω)) with hmwdef
  have hmwq : ∫⁻ ω, ENNReal.ofReal |mw ω| ^ q' ∂P ≤ ∫⁻ ω, ENNReal.ofReal |Xw ω| ^ q' ∂P := by
    have e : ∫⁻ ω, ENNReal.ofReal |mw ω| ^ q' ∂P = ∫⁻ ω, ENNReal.ofReal
        |(P[Xw | MeasurableSpace.comap (fun ω => (GMS4.prop48CircleAverageObservation
          (p48oWPField X₀) hIG₀ r w ω, phaseVersion D hγ ω)) inferInstance]) ω| ^ q' ∂P :=
      lintegral_congr_ae (by filter_upwards [hmw] with ω hω; rw [hω])
    rw [e]
    exact p48o_lintegral_abs_rpow_condExp_le hq'1.le
  have hJq : ∫⁻ ω, ENNReal.ofReal |Xw ω - mw ω| ^ q' ∂P ≤
      ENNReal.ofReal (2 ^ q' * ε ^ (-(q' * ζ)) * Kq) := by
    have hsub := p48o_lintegral_abs_sub_rpow_le (μ := P) (f := Xw) (g := mw)
      hXwm.aemeasurable hq'1.le
    have hx : ∫⁻ ω, ENNReal.ofReal |Xw ω| ^ q' ∂P ≤ ENNReal.ofReal (ε ^ (-(q' * ζ)) * Kq) := hXwq
    refine hsub.trans ?_
    have hsum : ∫⁻ ω, ENNReal.ofReal |Xw ω| ^ q' ∂P + ∫⁻ ω, ENNReal.ofReal |mw ω| ^ q' ∂P ≤
        2 * ENNReal.ofReal (ε ^ (-(q' * ζ)) * Kq) := by
      rw [two_mul]; exact add_le_add hx (hmwq.trans hx)
    refine (mul_le_mul' le_rfl hsum).trans (le_of_eq ?_)
    have h2 : (2 : ℝ≥0∞) ^ (q' - 1) * 2 = ENNReal.ofReal (2 ^ q') := by
      rw [← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), ← Real.rpow_add_one (by norm_num)]
      congr 2
      ring
    rw [← mul_assoc, h2, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), mul_assoc]
  -- assemble the rate
  have hθ0 : 0 ≤ p / p₀ := (div_pos hp0 (hp0.trans hpp₀)).le
  have hδsp : 0 ≤ δ ^ ((1 / 2 : ℝ) * p) := Real.rpow_nonneg hδ.le _
  have hE0 : 0 ≤ Real.exp (-(b / δ ^ ((1 : ℝ) - 1 / 2))) := (Real.exp_pos _).le
  have hK₀θ : 0 ≤ K₀ ^ (p / p₀) := Real.rpow_nonneg hK₀ _
  have hinner0 : 0 ≤ C3 * (δ ^ ((1 / 2 : ℝ) * p) * Kp +
      Real.exp (-(b / δ ^ ((1 : ℝ) - 1 / 2))) * K₀ ^ (p / p₀)) := by positivity
  have hsecond0 : 0 ≤ 2 ^ q' * ε ^ (-(q' * ζ)) * Kq :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hε0.le _)) hKq
  have hRHS : (ENNReal.ofReal (GMSAppA.a3C p p₀) *
      (ENNReal.ofReal (δ ^ ((1 / 2 : ℝ) * p)) *
          ∫⁻ ω, ENNReal.ofReal |fz (GMS4.prop48LocalFieldObservation (p48oWPField X₀) hIG₀ (r * δ)
            r z ω, phaseVersion D hγ ω)| ^ p ∂P +
        ENNReal.ofReal (Real.exp (-(GMSAppA.a3bN p p₀ 2 / δ ^ ((1 : ℝ) - 1 / 2)))) *
          (∫⁻ ω, ENNReal.ofReal |fz (GMS4.prop48LocalFieldObservation (p48oWPField X₀) hIG₀
            (r * δ) r z ω, phaseVersion D hγ ω)| ^ p₀ ∂P) ^ (p / p₀))) ^ (1 / p) *
      (∫⁻ ω, ENNReal.ofReal |Xw ω - mw ω| ^ q' ∂P) ^ (1 / q') ≤
      ENNReal.ofReal (Cf * ε ^ ζ) := by
    calc _ ≤ (ENNReal.ofReal C3 * (ENNReal.ofReal (δ ^ ((1 / 2 : ℝ) * p)) * ENNReal.ofReal Kp +
          ENNReal.ofReal (Real.exp (-(b / δ ^ ((1 : ℝ) - 1 / 2)))) *
            (ENNReal.ofReal K₀) ^ (p / p₀))) ^ (1 / p) *
          (ENNReal.ofReal (2 ^ q' * ε ^ (-(q' * ζ)) * Kq)) ^ (1 / q') := by
          gcongr
      _ = ENNReal.ofReal ((C3 * (δ ^ ((1 / 2 : ℝ) * p) * Kp +
          Real.exp (-(b / δ ^ ((1 : ℝ) - 1 / 2))) * K₀ ^ (p / p₀))) ^ (1 / p) *
          (2 ^ q' * ε ^ (-(q' * ζ)) * Kq) ^ (1 / q')) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hK₀ hθ0, ← ENNReal.ofReal_mul hδsp,
            ← ENNReal.ofReal_mul hE0, ← ENNReal.ofReal_add (mul_nonneg hδsp hKp)
              (mul_nonneg hE0 hK₀θ), ← ENNReal.ofReal_mul hC3,
            ENNReal.ofReal_rpow_of_nonneg hinner0 (by positivity),
            ENNReal.ofReal_rpow_of_nonneg hsecond0 (by positivity),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hinner0 _)]
      _ ≤ ENNReal.ofReal (Cf * ε ^ ζ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hδdef, hCfdef]
          exact p48o_far_rate_arith hε0 hε1 hζ hp1.le hpp₀ hq'1 hC3 hKp hK₀ hKq hb
  have hfin := hA3.trans hRHS
  have hCε : 0 ≤ Cf * ε ^ ζ := mul_nonneg hCf (Real.rpow_nonneg hε0.le _)
  rw [ENNReal.ofReal_le_ofReal_iff hCε] at hfin
  exact (le_abs_self _).trans hfin

end MatedCRTHarmonic.GMS4O
