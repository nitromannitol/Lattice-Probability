/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalRegularity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalCompletion
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48UniformRegularity
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48ConeDisk
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Phase
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalCircleProcess

/-!
# Uniform regularity exponent on the canonical zero-cone carrier

The all-visit Lemma 4.3 reconstruction in H3 feeds Proposition 4.5, and the
rate exponent is selected before the spatial radius. The comparison is for
The specified circle-average versions; the spatial a.s. transfer to the
literal average process is a separate obligation.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT
open LQGMetric LQGMetric.Blueprint

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Circle averages on a disk contained in the unit disk depend only on the
unit-disk restriction of the distribution. -/
theorem prop48_circleAvg_eq_of_disk_restrict_eq
    (h h' : DistC) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hball : Metric.closedBall z r ⊆ (ballO (0 : ℂ) 1 : Set ℂ))
    (heq : restrictTo (ballO 0 1) h = restrictTo (ballO 0 1) h') :
    circleAvg h r z = circleAvg h' r z := by
  have he := congrArg
    (fun T => GMS4c.localCircleProcess (ballO (0 : ℂ) 1) T r z) heq
  rw [GMS4c.localCircleProcess_restrictTo,
    GMS4c.localCircleProcess_restrictTo] at he
  have hc : 0 < r ∧ Metric.closedBall z r ⊆ (ballO (0 : ℂ) 1 : Set ℂ) :=
    ⟨hr, hball⟩
  simpa only [MatedCRT.restrictCircles, if_pos hc] using he

/-- The source condition `r + |z| < 1` places the averaging disk inside the
unit disk where the 0-cone and reference whole-plane fields agree. -/
theorem prop48_closedBall_subset_unitDisk
    {r : ℝ} {z : ℂ} (hsmall : r + ‖z‖ < 1) :
    Metric.closedBall z r ⊆ (ballO (0 : ℂ) 1 : Set ℂ) := by
  intro w hw
  have hd : dist w 0 ≤ dist w z + ‖z‖ := by
    simpa only [dist_zero_right] using dist_triangle w z 0
  have hwz : dist w z ≤ r := hw
  change dist w 0 < 1
  linarith

/-- At each fixed centre with its averaging disk inside the unit disk, the
chosen whole-plane and IG versions equal the literal source observations
almost surely. This is deliberately a fixed-centre statement. -/
theorem prop48_circle_versions_eq_actual_fixed
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {Xt : Ω → DistC} {H HIG : ℝ → ℂ → Ω → ℝ}
    (hH : DFGPS.IsCircleAvgVersion Xt P H)
    (hHIG : DFGPS.IsCircleAvgVersion hIG₀ P HIG)
    (hdisc : ∀ᵐ ω ∂P, restrictTo (ballO 0 1)
      (coneField (X₀ ω) (coneRadial γ 0
        (fun t => B₀ t ω) (fun t => B₀' t ω))) =
        restrictTo (ballO 0 1) (Xt ω))
    {r : ℝ} (hr : 0 < r) (z : ℂ) (hsmall : r + ‖z‖ < 1) :
    (fun ω => (H r z ω, HIG r z ω + U ω)) =ᵐ[P]
      fun ω => (fieldCircleAverage D hγ r z ω,
        igCircleAverage hIG₀ U r z ω) := by
  filter_upwards [hdisc, hH.ae_eq r hr z, hHIG.ae_eq r hr z]
    with ω hω hwp hig
  have hcone := prop48_circleAvg_eq_of_disk_restrict_eq
    (coneField (X₀ ω) (coneRadial γ 0
      (fun t => B₀ t ω) (fun t => B₀' t ω)))
    (Xt ω) hr z (prop48_closedBall_subset_unitDisk hsmall) hω
  simp only [fieldCircleAverage, igCircleAverage,
    MatedCRTHarmonic.Canon.referenceSample,
    MatedCRTHarmonic.Canon.actualIGAverage]
  rw [hcone, hwp, hig]

/-- At a fixed centre, the versioned Proposition 4.5 event implies the
literal local event almost surely. The global all-centres implication is
handled later through spatial Fubini. -/
theorem prop48_ae_localEvent_of_versionGood_fixed
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {Xt : Ω → DistC} {H HIG : ℝ → ℂ → Ω → ℝ}
    (hH : DFGPS.IsCircleAvgVersion Xt P H)
    (hHIG : DFGPS.IsCircleAvgVersion hIG₀ P HIG)
    (hdisc : ∀ᵐ ω ∂P, restrictTo (ballO 0 1)
      (coneField (X₀ ω) (coneRadial γ 0
        (fun t => B₀ t ω) (fun t => B₀' t ω))) =
        restrictTo (ballO 0 1) (Xt ω))
    {ε ρ q ζ : ℝ} (hr : 0 < ε ^ (q - 4 * ζ))
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) ρ)
    (hsmall : ε ^ (q - 4 * ζ) + ‖z‖ < 1) :
    ∀ᵐ ω ∂P,
      ω ∈ GMS4b.prop45Event (GMS4b.l46tZeroConeCellModel D hγ)
        H (fun r w ω => HIG r w ω + U ω) ε ρ q ζ →
      ω ∈ localEvent D hγ ε q ζ z := by
  filter_upwards [prop48_circle_versions_eq_actual_fixed D hγ hH hHIG
    hdisc hr z hsmall] with ω hobs hgood
  obtain ⟨hgeom, havg⟩ := hgood
  have hg := hgeom z hz
  have ha := havg z hz
  change ω ∈ MatedCRTHarmonic.Canon.referenceLocalEvent D hγ ε q ζ z
  simp only [MatedCRTHarmonic.Canon.referenceLocalEvent,
    GMS4c.lemma49Event, MatedCRTHarmonic.Canon.referenceConditioningInput,
    MatedCRTHarmonic.Canon.actualIGAverage,
    GMS4b.l46tZeroConeCellModel] at hg ⊢
  refine ⟨hg.1, hg.2, ?_⟩
  change max |fieldCircleAverage D hγ (ε ^ (q - 4 * ζ)) z ω|
      |igCircleAverage hIG₀ U (ε ^ (q - 4 * ζ)) z ω| ≤
        2 * q * Real.log ε⁻¹
  have hF : H (ε ^ (q - 4 * ζ)) z ω =
      fieldCircleAverage D hγ (ε ^ (q - 4 * ζ)) z ω :=
    congrArg Prod.fst hobs
  have hI : HIG (ε ^ (q - 4 * ζ)) z ω + U ω =
      igCircleAverage hIG₀ U (ε ^ (q - 4 * ζ)) z ω :=
    congrArg Prod.snd hobs
  rw [← hF, ← hI]
  exact max_le_iff.mpr ha

/-- A whole-plane reference field realizes the zero-cone field on the unit
disk, with circle-average versions for both the reference and phase-shifted
IG fields. Both versions have Proposition 4.5 supremum bounds. -/
theorem exists_prop48_zeroCone_circle_versions
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ (Xt : Ω → DistC) (H HIG : ℝ → ℂ → Ω → ℝ),
      IsNormalizedWPGFF Xt P ∧
      DFGPS.IsCircleAvgVersion Xt P H ∧
      GMS4b.CircleAverageSupBound P H ∧
      DFGPS.IsCircleAvgVersion hIG₀ P HIG ∧
      GMS4b.CircleAverageSupBound P (fun r z ω => HIG r z ω + U ω) ∧
      (∀ᵐ ω ∂P, restrictTo (ballO 0 1)
        (coneField (X₀ ω) (coneRadial γ 0
          (fun t => B₀ t ω) (fun t => B₀' t ω))) =
          restrictTo (ballO 0 1) (Xt ω)) := by
  obtain ⟨Xt, hXt, hdisc⟩ := GMS4.prop48_exists_zeroCone_disk_wholePlaneGFF D hγ
  obtain ⟨H, hH, -⟩ := GMCUpper.exists_circleAvgVersion_normalized hXt
  obtain ⟨HIG, hHIG, -, hHIGsup⟩ := BundleSec4.exists_igCircleAvgVersion_withPhase D
  have hHsup : GMS4b.CircleAverageSupBound P H :=
    GMCUpper.circleAverageSupBound_of_model hXt hH
      (GMCUpper.circleAverageSupBoundModel_holds hXt hH)
  exact ⟨Xt, H, HIG, hXt, hH, hHsup, hHIG, hHIGsup, hdisc⟩

/-- H3's primed reconstruction gives a Proposition 4.5 exponent independent
of the radius. -/
theorem Prop48PrimedBorelLocalFactorInput.prop45_uniform_on_versions
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ : ℝ}
    {H2 : ThickGMCReaders D}
    (H3 : Prop48PrimedBorelLocalFactorInput D hγ q ζ H2)
    {H HIG : ℝ → ℂ → Ω → ℝ}
    (hH : GMS4b.CircleAverageSupBound P H)
    (hHIG : GMS4b.CircleAverageSupBound P HIG)
    (hq : q ∈ Ioo (0 : ℝ) (2 / (2 + γ) ^ 2))
    (hζ : ζ ∈ Ioo (0 : ℝ) (q / 4)) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1,
      ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
        P (GMS4b.prop45Event (GMS4b.l46tZeroConeCellModel D hγ)
          H HIG ε ρ q ζ)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) :=
  GMS4.prop48_zeroCone_prop45_uniform_of_primeReconstruction
    D hγ (BundleSec4.zeroCone_primeReconstruction D hγ) hH hHIG hq hζ

/-- The canonical field and IG data admit versions whose Proposition 4.5
failure probability has a single exponent for every radius. -/
theorem Prop48PrimedBorelLocalFactorInput.exists_uniform_regular_versions
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ : ℝ}
    {H2 : ThickGMCReaders D}
    (H3 : Prop48PrimedBorelLocalFactorInput D hγ q ζ H2)
    (hq : q ∈ Ioo (0 : ℝ) (min (2 / (2 + γ) ^ 2) γ))
    (hζ : ζ ∈ Ioo (0 : ℝ) (q / 100)) :
    ∃ (Xt : Ω → DistC) (H HIG : ℝ → ℂ → Ω → ℝ) (α : ℝ),
      0 < α ∧ IsNormalizedWPGFF Xt P ∧
      DFGPS.IsCircleAvgVersion Xt P H ∧
      DFGPS.IsCircleAvgVersion hIG₀ P HIG ∧
      (∀ᵐ ω ∂P, restrictTo (ballO 0 1)
        (coneField (X₀ ω) (coneRadial γ 0
          (fun t => B₀ t ω) (fun t => B₀' t ω))) =
          restrictTo (ballO 0 1) (Xt ω)) ∧
      ∀ ρ ∈ Ioo (0 : ℝ) 1,
        ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
          P (GMS4b.prop45Event (GMS4b.l46tZeroConeCellModel D hγ)
            H (fun r z ω => HIG r z ω + U ω) ε ρ q ζ)ᶜ ≤
            ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨Xt, H, HIG, hXt, hH, hHsup, hHIG, hHIGsup, hdisc⟩ :=
    exists_prop48_zeroCone_circle_versions D hγ
  obtain ⟨α, hα, hbound⟩ := H3.prop45_uniform_on_versions
    hHsup hHIGsup
    ⟨hq.1, lt_of_lt_of_le hq.2 (min_le_left _ _)⟩
    ⟨hζ.1, by linarith [hζ.2, hq.1]⟩
  exact ⟨Xt, H, HIG, α, hα, hXt, hH, hHIG, hdisc, hbound⟩

end MatedCRTHarmonic.GMS4.Canonical

