/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.L46TAdapter at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.L46TInputs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.L46TAdapter
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TZeroVersion

/-!
# Equation (4.16) closes the local comparison `hcmp` on the zero-cone model

The transfer (`GMS4b/L46TZeroVersion.lean`) proves the repaired [18] Lemma 4.6 and Proposition 4.5
on the frozen zero-cone model from two named inputs stated for measurable versions `hS =ᵐ` γ-cone field,
`hT =ᵐ` 0-cone field and phases `uS, uT =ᵐ U`:
`hcmp` (the joint local density (4.16) on every observation disk `l46tObservation ρ w`, with phase) and
`hlocal` (the measurable Lemma 4.3 reconstruction). Here `hcmp` is constructed from the
`GMSCM.IsMatingOfTreesCoupling.exists_l46tLocalFieldLawComparison` (field pair, per-disk measurable versions, some
`p > 1`):

1. move the per-disk versions to the global ones (`coneFieldVersion D`, `GMS4b.l46tZeroConeFieldVersion D`) with
   `localFieldLawComparison_congr` (the target version agrees with the 0-cone field on the observation disk);
2. append the phase `U` with the transfer's `l46t_phaseComparison_of_independent`, using
   `indepFun_coneField_IG_phaseVersion`, `indepFun_zeroConeField_IG_phaseVersion` (`BundleSec4/L46TInputs.lean`).

Results: `l46tZeroConeComparison_of_CMRN` (exactly the transfer's `hcmp` with `hS = coneFieldVersion D`,
`hT = l46tZeroConeFieldVersion D`, `uS = uT = U`), and the transferred Lemma 4.6 / Proposition 4.5 on the zero-cone
model with **only the Lemma 4.3 reconstruction** (and, for Prop 4.5, the two circle-average bounds) left:
`l46t_zeroCone_innerDegreeBoundPolylog_of_reconstruction`, `l46t_zeroCone_prop45_of_reconstruction`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LQGMetric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The raw γ-cone field of the bundle is a.e.-measurable (the local comparison). -/
theorem aemeasurable_coneFieldRaw
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    AEMeasurable (fun ω => MatedCRT.coneField (X ω)
      (MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) P :=
  GMSCM.aemeasurable_coneFieldOf D.gff D.bm_B D.bm_B' D.indep_cone.2

/-- One global measurable version of the bundle's γ-cone field. -/
def coneFieldVersion
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Ω → DistC :=
  (aemeasurable_coneFieldRaw D).mk _

theorem measurable_coneFieldVersion
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    Measurable (coneFieldVersion D) :=
  (aemeasurable_coneFieldRaw D).measurable_mk

theorem coneFieldVersion_ae_eq
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    (MoTInput.cellModelOfCoupling D hγ).field =ᵐ[P] coneFieldVersion D :=
  (aemeasurable_coneFieldRaw D).ae_eq_mk

/-- The translated local observation map is measurable. -/
theorem bundle_measurable_translatedPair (V : TopologicalSpace.Opens ℂ) (z₀ : ℂ) :
    Measurable fun p : DistC × DistC =>
      ((restrictTo V (affineComp 1 (-z₀) p.1), restrictTo V (affineComp 1 (-z₀) p.2)) :
        GMS4c.LocalFieldPair V) :=
  ((measurable_restrictTo V).comp ((measurable_affineComp 1 (-z₀)).comp measurable_fst)).prodMk
    ((measurable_restrictTo V).comp ((measurable_affineComp 1 (-z₀)).comp measurable_snd))

/-- The untranslated local observation map is measurable. -/
theorem bundle_measurable_pair (V : TopologicalSpace.Opens ℂ) :
    Measurable fun p : DistC × DistC =>
      ((restrictTo V p.1, restrictTo V p.2) : GMS4c.LocalFieldPair V) :=
  ((measurable_restrictTo V).comp measurable_fst).prodMk ((measurable_restrictTo V).comp measurable_snd)

/-- **the transfer's `hcmp` on each observation disk, nonempty form** (the local comparison + version transport + phase). -/
theorem nonempty_l46tZeroConeComparison
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ) :
    Nonempty (Σ p q : ℝ, GMS4b.L46TPhaseLawComparison (GMS4b.l46tObservation ρ w) P P
      (GMS4b.l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (coneFieldVersion D))
      (GMS4b.l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) U
      (GMS4b.l46tZeroConeFieldVersion D) hIG₀ U p q) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hex := GMSCM.IsMatingOfTreesCoupling.exists_l46tLocalFieldLawComparison D hγ hρ w hw
  simp only at hex
  obtain ⟨hγm, h₀m, -, hγae, -, h₀ae, p, q, -, ⟨cmp⟩⟩ := hex
  set V := GMS4b.l46tObservation ρ w with hV
  set z₀ : ℂ := w + (((1 - ρ) / 2 : ℝ) : ℂ) with hz₀
  have hIGm : Measurable hIG₀ := D.igField.1.1.measurable
  -- 1. the comparison at the global versions
  have mγ : Measurable (GMS4c.localFieldPair V (GMS4b.l46tTranslatedField z₀ (coneFieldVersion D))
      (GMS4b.l46tTranslatedField z₀ hIG₀)) :=
    (bundle_measurable_translatedPair V z₀).comp ((measurable_coneFieldVersion D).prodMk hIGm)
  have m₀ : Measurable (GMS4c.localFieldPair V (GMS4b.l46tZeroConeFieldVersion D) hIG₀) :=
    GMS4c.measurable_localFieldPair V (GMS4b.l46tZeroConeFieldVersion_measurable D) hIGm
  have hversion : hγm =ᵐ[P] coneFieldVersion D := hγae.symm.trans (coneFieldVersion_ae_eq D hγ)
  have eγ : GMS4c.localFieldPair V (GMS4b.l46tTranslatedField z₀ hγm) (GMS4b.l46tTranslatedField z₀ hIG₀)
      =ᵐ[P] GMS4c.localFieldPair V (GMS4b.l46tTranslatedField z₀ (coneFieldVersion D))
        (GMS4b.l46tTranslatedField z₀ hIG₀) := by
    filter_upwards [hversion] with ω hω
    simp only [GMS4c.localFieldPair, GMS4b.l46tTranslatedField, hω]
  have hraw0 := GMS4b.l46tZeroConeFieldVersion_ae_eq_raw D hγ
  have e₀ : GMS4c.localFieldPair V h₀m hIG₀ =ᵐ[P]
      GMS4c.localFieldPair V (GMS4b.l46tZeroConeFieldVersion D) hIG₀ := by
    filter_upwards [h₀ae, hraw0] with ω h1 h2
    simp only [GMS4c.localFieldPair]
    have h2' : restrictTo V (MatedCRT.coneField (X₀ ω)
        (MatedCRT.coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω))) =
        restrictTo V (GMS4b.l46tZeroConeFieldVersion D ω) := by
      have : (GMS4b.l46tZeroConeCellModel D hγ).field ω = GMS4b.l46tZeroConeFieldVersion D ω := h2
      rw [← this]
      rfl
    rw [← h1, h2']
  let cmp' := localFieldLawComparison_congr cmp mγ m₀ eγ e₀
  -- 2. independence of the local pairs from the phase
  have hUm : AEMeasurable U P := aemeasurable_phase D
  have hindγ : IndepFun (GMS4c.localFieldPair V (GMS4b.l46tTranslatedField z₀ (coneFieldVersion D))
      (GMS4b.l46tTranslatedField z₀ hIG₀)) U P := by
    have h1 := (indepFun_coneField_IG_phaseVersion D hγ).comp (bundle_measurable_translatedPair V z₀)
      measurable_id
    refine h1.congr ?_ (phaseVersion_ae_eq D)
    filter_upwards [coneFieldVersion_ae_eq D hγ] with ω hω
    have hω' : MatedCRT.coneField (X ω)
        (MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) = coneFieldVersion D ω := hω
    simp only [Function.comp_apply, GMS4c.localFieldPair, GMS4b.l46tTranslatedField, hω']
  have hind₀ : IndepFun (GMS4c.localFieldPair V (GMS4b.l46tZeroConeFieldVersion D) hIG₀) U P := by
    have h1 := (indepFun_zeroConeField_IG_phaseVersion D hγ).comp (bundle_measurable_pair V)
      measurable_id
    refine h1.congr ?_ (phaseVersion_ae_eq D)
    filter_upwards [hraw0] with ω hω
    have hω' : MatedCRT.coneField (X₀ ω)
        (MatedCRT.coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)) =
        GMS4b.l46tZeroConeFieldVersion D ω := hω
    simp only [Function.comp_apply, GMS4c.localFieldPair, hω']
  exact ⟨⟨p, q, GMS4b.l46t_phaseComparison_of_independent cmp' hUm hUm rfl hindγ hind₀⟩⟩

/-- **the transfer's `hcmp` on the zero-cone model, from the local comparison** (data form, as the transfer consumes it), with
`hS = coneFieldVersion D`, `hT = l46tZeroConeFieldVersion D`, `uS = uT = U`. -/
def l46tZeroConeComparison_of_CMRN
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      Σ p q : ℝ, GMS4b.L46TPhaseLawComparison (GMS4b.l46tObservation ρ w) P P
        (GMS4b.l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (coneFieldVersion D))
        (GMS4b.l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) U
        (GMS4b.l46tZeroConeFieldVersion D) hIG₀ U p q :=
  fun _ hρ w hw => (nonempty_l46tZeroConeComparison D hγ hρ w hw).some

end Bundle

end MatedCRTHarmonic.BundleSec4
