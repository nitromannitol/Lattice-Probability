/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalRegularitySpatial at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalSpatial

/-!
# Spatial form of the canonical regularity event

The versioned Proposition 4.5 event can be replaced by a measurable subset
with the same failure outer measure. On it, the literal (4.22) event holds at
Lebesgue-a.e. centre, which is the strength used by Proposition 4.8's test
integral. Source: [18] (4.22)–(4.29), lines 2183–2303.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT LQGMetric LQGMetric.Blueprint

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The jointly measurable local event evaluated on measurable field and
phase versions. -/
def prop48LocalEventVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (ω : Ω) (z : ℂ) : Prop :=
  ((η₀ ω, GMS4O.p48oObsVersion D hγ ε q ζ ω z) : GMS4c.Lemma49Input) ∈
    GMS4c.lemma49Event ε q ζ z

theorem measurableSet_prop48LocalEventVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) (q ζ : ℝ) :
    MeasurableSet {p : Ω × ℂ | prop48LocalEventVersion D hγ ε q ζ p.1 p.2} := by
  have hin : Measurable fun p : Ω × ℂ =>
      (((η₀ p.1, GMS4O.p48oObsVersion D hγ ε q ζ p.1 p.2) :
        GMS4c.Lemma49Input), p.2) :=
    (((D.measurable_curves.2.2.1.comp measurable_fst).prodMk
      (GMS4O.measurable_p48oObsVersion D hγ ε q ζ)).prodMk measurable_snd)
  exact hin (GMS4O.p48o_measurableSet_lemma49Event_joint hε q ζ)

/-- The versioned and literal local events agree at every centre on one
probability-one event. -/
theorem ae_prop48LocalEventVersion_iff_localEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      prop48LocalEventVersion D hγ ε q ζ ω z ↔
        ω ∈ localEvent D hγ ε q ζ z := by
  filter_upwards [GMS4O.p48o_ae_versions_eq D hγ] with ω hω z
  have hin : ((η₀ ω, GMS4O.p48oObsVersion D hγ ε q ζ ω z) :
      GMS4c.Lemma49Input) =
      MatedCRTHarmonic.Canon.referenceConditioningInput D hγ ε q ζ z ω := by
    simp only [GMS4O.p48oObsVersion,
      MatedCRTHarmonic.Canon.referenceConditioningInput,
      MatedCRTHarmonic.Canon.actualIGAverage, hω.1, hω.2]
  simp only [prop48LocalEventVersion, localEvent,
    MatedCRTHarmonic.Canon.referenceLocalEvent, hin, Set.mem_preimage]

/-- A measurable regularity event with the Proposition 4.5 failure measure
and the source local event at spatial-a.e. centre. -/
theorem exists_prop48_regular_good_spatial
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {Xt : Ω → DistC} {H HIG : ℝ → ℂ → Ω → ℝ}
    (hH : DFGPS.IsCircleAvgVersion Xt P H)
    (hHIG : DFGPS.IsCircleAvgVersion hIG₀ P HIG)
    (hdisc : ∀ᵐ ω ∂P, restrictTo (ballO 0 1)
      (coneField (X₀ ω) (coneRadial γ 0
        (fun t => B₀ t ω) (fun t => B₀' t ω))) =
        restrictTo (ballO 0 1) (Xt ω))
    {ε ρ q ζ : ℝ} (hε : 0 < ε)
    (hr : 0 < ε ^ (q - 4 * ζ))
    (hsmall : ε ^ (q - 4 * ζ) + ρ < 1) :
    ∃ E : Set Ω, MeasurableSet E ∧
      E ⊆ GMS4b.prop45Event (GMS4b.l46tZeroConeCellModel D hγ)
        H (fun r z ω => HIG r z ω + U ω) ε ρ q ζ ∧
      P Eᶜ = P (GMS4b.prop45Event (GMS4b.l46tZeroConeCellModel D hγ)
        H (fun r z ω => HIG r z ω + U ω) ε ρ q ζ)ᶜ ∧
      ∀ᵐ ω ∂P, ω ∈ E →
        ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : ℂ) ρ)),
          ω ∈ localEvent D hγ ε q ζ z := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  let G : Set Ω := GMS4b.prop45Event (GMS4b.l46tZeroConeCellModel D hγ)
    H (fun r z ω => HIG r z ω + U ω) ε ρ q ζ
  let L : Ω → ℂ → Prop := fun ω z =>
    z ∉ Metric.ball (0 : ℂ) ρ ∨ prop48LocalEventVersion D hγ ε q ζ ω z
  have hL : MeasurableSet {p : Ω × ℂ | L p.1 p.2} := by
    have heq : {p : Ω × ℂ | L p.1 p.2} =
        {p : Ω × ℂ | p.2 ∉ Metric.ball (0 : ℂ) ρ} ∪
          {p : Ω × ℂ | prop48LocalEventVersion D hγ ε q ζ p.1 p.2} := by
      ext p
      simp only [L, Set.mem_setOf_eq, Set.mem_union]
    rw [heq]
    exact (measurable_snd measurableSet_ball.compl).union
      (measurableSet_prop48LocalEventVersion D hγ hε.le q ζ)
  have hfixed : ∀ z : ℂ, ∀ᵐ ω ∂P, ω ∈ G → L ω z := by
    intro z
    by_cases hz : z ∈ Metric.ball (0 : ℂ) ρ
    · have hzsmall : ε ^ (q - 4 * ζ) + ‖z‖ < 1 := by
        have hzρ : ‖z‖ < ρ := by simpa only [mem_ball_zero_iff] using hz
        linarith
      filter_upwards [prop48_ae_localEvent_of_versionGood_fixed D hγ
        hH hHIG hdisc hr z hz hzsmall,
        ae_prop48LocalEventVersion_iff_localEvent D hγ ε q ζ]
        with ω hlocal heq hgood
      exact Or.inr ((heq z).2 (hlocal hgood))
    · exact Filter.Eventually.of_forall fun _ω _ => Or.inl hz
  obtain ⟨E, hEm, hEG, hP, hspatial⟩ :=
    prop48_exists_measurable_good_spatial P G L hL hfixed
  refine ⟨E, hEm, hEG, hP, ?_⟩
  filter_upwards [hspatial, ae_prop48LocalEventVersion_iff_localEvent D hγ ε q ζ]
    with ω hω heq hωE
  have hωL := hω hωE
  filter_upwards [ae_restrict_of_ae hωL,
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzball
  exact (heq z).1 (hz.resolve_left (not_not.mpr hzball))

/-- H3 yields the spatially correct Proposition 4.5 event with one exponent
chosen before the radius. The geometric guard is the source's condition that
all averaging disks used in the test lie inside the unit disk. -/
theorem Prop48PrimedBorelLocalFactorInput.exists_uniform_good_spatial
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ : ℝ}
    {H2 : ThickGMCReaders D}
    (H3 : Prop48PrimedBorelLocalFactorInput D hγ q ζ H2)
    (hq : q ∈ Ioo (0 : ℝ) (min (2 / (2 + γ) ^ 2) γ))
    (hζ : ζ ∈ Ioo (0 : ℝ) (q / 100)) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1,
      ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
        ε ^ (q - 4 * ζ) + ρ < 1 →
          ∃ E : Set Ω, MeasurableSet E ∧
            P Eᶜ ≤ ENNReal.ofReal (C * ε ^ α) ∧
            ∀ᵐ ω ∂P, ω ∈ E →
              ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : ℂ) ρ)),
                ω ∈ localEvent D hγ ε q ζ z := by
  obtain ⟨Xt, H, HIG, α, hα, -, hH, hHIG, hdisc, hbound⟩ :=
    H3.exists_uniform_regular_versions hq hζ
  refine ⟨α, hα, ?_⟩
  intro ρ hρ
  obtain ⟨C, hC⟩ := hbound ρ hρ
  refine ⟨C, ?_⟩
  intro ε hε hsmall
  obtain ⟨E, hEm, -, hP, hlocal⟩ :=
    exists_prop48_regular_good_spatial D hγ hH hHIG hdisc hε.1
      (Real.rpow_pos_of_pos hε.1 _) hsmall
  exact ⟨E, hEm, by rw [hP]; exact hC ε hε, hlocal⟩

end MatedCRTHarmonic.GMS4.Canonical

